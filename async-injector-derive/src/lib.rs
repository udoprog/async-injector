//! Macros for [async-injector](https://docs.rs/async-injector).
//!
//! This provides the [Provider] derive, which can be used to automatically
//! construct and inject dependencies. See its documentation for how to use.

#![recursion_limit = "256"]

extern crate proc_macro;

use darling::FromMeta;
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::spanned::Spanned as _;
use syn::*;

/// Helper derive to implement a provider.
///
/// The `Provider` derive can only be used on struct. Each field designates a
/// value that must either be injected, or provided during construction.
///
/// ```rust
/// use async_injector::Provider;
/// use serde::Serialize;
///
/// #[derive(Serialize)]
/// enum Tag {
///     Table,
///     Url,
/// }
///
/// #[derive(Provider)]
/// struct Deps {
///     fixed: String,
///     #[dependency(optional, tag = "Tag::Table")]
///     table: Option<String>,
///     #[dependency(tag = "Tag::Url")]
///     url: String,
///     #[dependency]
///     connection_limit: u32,
/// }
/// ```
///
/// This generates another struct named `DepsProvider`, with the following api:
///
/// ```rust,no_run
/// use async_injector::{Error, Injector};
///
/// # struct Deps {}
/// impl Deps {
///     /// Construct a new provider.
///     async fn provider(injector: &Injector, fixed: String) -> Result<DepsProvider, Error>
///     # { todo!() }
/// }
///
/// struct DepsProvider {
///     /* private fields */
/// }
///
/// impl DepsProvider {
///     /// Try to construct the current value. Returns [None] unless all
///     /// required dependencies are available.
///     fn build(&mut self) -> Option<Deps>
///     # { todo!() }
///
///     /// Wait until we can successfully build the complete provided
///     /// value.
///     async fn wait(&mut self) -> Deps
///     # { todo!() }
///
///     /// Wait until the provided value has changed. Either some
///     /// dependencies are no longer available at which it returns `None`,
///     /// or all dependencies are available after which we return the
///     /// build value.
///     async fn wait_for_update(&mut self) -> Option<Deps>
///     # { todo!() }
/// }
/// ```
///
/// The `provider` associated function takes the reference to an injector as its
/// first argument and any fields which are not marked as a `#[dependency]`.
/// These are called fixed fields.
///
/// <br>
///
/// # The `#[dependency]` field attribute
///
/// The `#[dependency]` attribute can be used to mark fields which need to be
/// injected. It takes an optional `#[dependency(tag = "..")]`, which allows you
/// to specify the tag to use when constructing the injected [Key].
///
/// ```rust
/// use async_injector::Provider;
/// use serde::Serialize;
///
/// #[derive(Serialize)]
/// enum Tag {
///     First,
/// }
///
/// #[derive(Provider)]
/// struct Params {
///     #[dependency(tag = "Tag::First")]
///     tagged: String,
///     #[dependency]
///     number: u32,
/// }
/// ```
///
/// Optional fields use the [Option] type and must be marked with the `optional`
/// meta attribute.
///
/// ```rust
/// use async_injector::Provider;
///
/// #[derive(Provider)]
/// struct Params {
///     #[dependency(optional)]
///     table: Option<String>,
/// }
/// ```
///
/// [Key]: https://docs.rs/async-injector/0/async_injector/struct.Key.html
#[proc_macro_derive(Provider, attributes(dependency))]
pub fn provider_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(input as DeriveInput);

    match implement(&ast) {
        Ok(stream) => stream,
        Err(e) => e.to_compile_error(),
    }
    .into()
}

/// Derive to implement the `Provider` trait.
fn implement(ast: &DeriveInput) -> syn::Result<TokenStream> {
    let st = match ast.data {
        Data::Struct(ref st) => st,
        _ => panic!("`Provider` attribute is only supported on structs"),
    };

    let config = provider_config(st)?;
    let (provider, provider_ident, fixed_args, fixed_idents) = impl_provider(ast, &config);

    let vis = &ast.vis;
    let ident = &ast.ident;
    let generics = &ast.generics;

    let output = quote! {
        impl #generics #ident #generics {
            /// Construct a new provider for this type.
            #vis async fn provider(injector: &::async_injector::Injector #(, #fixed_args)*) -> Result<#provider_ident #generics, ::async_injector::Error> {
                #provider_ident::new(injector #(, #fixed_idents)*).await
            }
        }

        #provider
    };

    Ok(output)
}

/// Build a provider configuration.
fn provider_config(st: &DataStruct) -> syn::Result<ProviderConfig<'_>> {
    let fields = provider_fields(st)?;
    Ok(ProviderConfig { fields })
}

/// Extracts provider fields.
fn provider_fields(st: &DataStruct) -> syn::Result<Vec<ProviderField<'_>>> {
    let mut fields = Vec::new();

    for field in &st.fields {
        let ident = field.ident.as_ref().expect("missing identifier for field");

        let mut dependency = None;

        for a in &field.attrs {
            let meta = match a.parse_meta() {
                Ok(meta) => meta,
                _ => continue,
            };

            if meta.path().is_ident("dependency") {
                if dependency.is_some() {
                    return Err(syn::Error::new(
                        meta.span(),
                        "multiple #[dependency] attributes are not supported",
                    ));
                }

                let d = if let Meta::Path(_) = meta {
                    DependencyAttr::default()
                } else {
                    match DependencyAttr::from_meta(&meta) {
                        Ok(d) => d,
                        Err(e) => panic!("bad #[dependency(..)] attribute: {}", e),
                    }
                };

                dependency = Some((meta.span(), d));
                continue;
            }
        }

        let dependency = match dependency {
            Some((span, dep)) => Some(Dependency {
                span,
                tag: dep.tag.map(|t| {
                    syn::parse_str::<TokenStream>(&t).expect("`tag` to be valid expression")
                }),
                optional: dep.optional,
                ty: if dep.optional {
                    optional_ty(&field.ty)
                } else {
                    &field.ty
                },
            }),
            None => None,
        };

        fields.push(ProviderField {
            ident,
            field,
            dependency,
        })
    }

    Ok(fields)
}

/// Build the provider type.
///
/// The factory is responsible for building providers that builds instances of
/// the provided type.
///
/// This step is necessary to support "fixed" fields, i.e. fields who's value
/// are provided at build time.
fn impl_provider<'a>(
    ast: &DeriveInput,
    config: &ProviderConfig<'a>,
) -> (TokenStream, Ident, Vec<TokenStream>, Vec<Ident>) {
    let provider_ident = Ident::new(&format!("{}Provider", ast.ident), Span::call_site());

    let mut provider_fields = Vec::new();
    let mut constructor_assign = Vec::new();
    let mut constructor_fields = Vec::new();
    let mut injected_update = Vec::new();
    let mut provider_extract = Vec::new();
    let mut initialized_fields = Vec::new();

    let mut fixed_args = Vec::new();
    let mut fixed_idents = Vec::new();

    for f in &config.fields {
        let field_ident = f.ident;
        let field_stream = Ident::new(&format!("{}_stream", field_ident), Span::call_site());
        let field_value = Ident::new(&format!("{}_value", field_ident), Span::call_site());

        if let Some(dep) = &f.dependency {
            let field_ty = dep.ty;

            provider_fields.push(quote!(#field_stream: ::async_injector::Stream<#field_ty>));
            provider_fields.push(quote!(#field_value: Option<#field_ty>));

            let key = match &dep.tag {
                Some(tag) => quote!(::async_injector::Key::<#field_ty>::tagged(#tag)?),
                None => quote!(::async_injector::Key::<#field_ty>::of()),
            };

            constructor_assign.push(quote! {
                let (#field_stream, #field_value) = __injector.stream_key(#key).await;
            });

            constructor_fields.push(field_stream.clone());
            constructor_fields.push(field_value.clone());

            injected_update.push(quote! {
                #field_value = self.#field_stream.recv() => {
                    self.#field_value = #field_value;
                }
            });

            if dep.optional {
                initialized_fields.push(quote_spanned! { f.field.span() =>
                    #field_ident: self.#field_value.as_ref().map(Clone::clone),
                });
            } else {
                provider_extract.push(quote_spanned! { f.field.span() =>
                    let #field_value = match self.#field_value.as_ref() {
                        Some(#field_value) => #field_value,
                        None => return None,
                    };
                });

                initialized_fields.push(quote_spanned! { dep.span =>
                    #field_ident: #field_value.clone(),
                });
            };
        } else {
            let field_ty = &f.field.ty;

            provider_fields.push(quote!(#field_ident: #field_ty));

            initialized_fields.push(quote_spanned! { f.field.span() =>
                #field_ident: self.#field_ident.clone(),
            });

            constructor_fields.push(field_ident.clone());

            fixed_args.push(quote!(#field_ident: #field_ty));
            fixed_idents.push(field_ident.clone());
        }
    }

    let ident = &ast.ident;

    let vis = &ast.vis;
    let generics = &ast.generics;
    let args = &fixed_args;

    let provider = quote_spanned! { ast.span() =>
        #vis struct #provider_ident #generics {
            /// Whether or not the injector has been initialized.
            __init: bool,
            #(#provider_fields,)*
        }

        impl #generics #provider_ident #generics {
            /// Construct a new provider.
            #vis async fn new(__injector: &::async_injector::Injector #(, #args)*) -> Result<#provider_ident #generics, ::async_injector::Error> {
                #(#constructor_assign)*

                Ok(#provider_ident {
                    __init: true,
                    #(#constructor_fields,)*
                })
            }

            /// Try to construct the current value. Returns [None] unless all
            /// required dependencies are available.
            #[allow(dead_code)]
            #vis fn build(&self) -> Option<#ident #generics> {
                #(#provider_extract)*

                Some(#ident {
                    #(#initialized_fields)*
                })
            }

            /// Wait until the provided value has changed. Either some
            /// dependencies are no longer available at which it returns `None`,
            /// or all dependencies are available after which we return the
            /// build value.
            #[allow(dead_code)]
            #vis async fn wait_for_update(&mut self) -> Option<#ident #generics> {
                if self.__init {
                    self.__init = false;
                } else {
                    self.wait_internal().await;
                }

                self.build()
            }

            /// Wait until we can successfully build the complete provided
            /// value.
            #[allow(dead_code)]
            #vis async fn wait(&mut self) -> #ident #generics {
                loop {
                    if let Some(value) = self.wait_for_update().await {
                        return value;
                    }
                }
            }

            async fn wait_internal(&mut self) {
                ::async_injector::derive::select! {
                    #(#injected_update)*
                }
            }
        }
    };

    (provider, provider_ident, fixed_args, fixed_idents)
}

/// Extract the optional type argument from the given type.
fn optional_ty(ty: &Type) -> &Type {
    match ty {
        Type::Path(ref path) => {
            let last = path.path.segments.last().expect("missing path segment");

            if last.ident != "Option" {
                panic!("optional field must be of type: Option<T>");
            }

            let arguments = match &last.arguments {
                PathArguments::AngleBracketed(ref arguments) => &arguments.args,
                other => panic!("bad path arguments: {:?}", other),
            };

            let first = arguments.iter().next().expect("at least one argument");

            match first {
                GenericArgument::Type(ref ty) => ty,
                _ => panic!("expected type generic argument"),
            }
        }
        _ => {
            panic!("expected optional type to be a path");
        }
    }
}

struct ProviderConfig<'a> {
    fields: Vec<ProviderField<'a>>,
}

struct ProviderField<'a> {
    ident: &'a Ident,
    field: &'a Field,
    dependency: Option<Dependency<'a>>,
}

#[derive(Debug)]
struct Dependency<'a> {
    span: Span,
    /// Use a string tag.
    tag: Option<TokenStream>,
    optional: bool,
    ty: &'a Type,
}

/// #[dependency(...)] attribute
#[derive(Debug, Default, FromMeta)]
#[darling(default)]
struct DependencyAttr {
    /// Use a string tag.
    tag: Option<String>,
    /// If the field is optional.
    optional: bool,
}
