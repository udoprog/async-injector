//! Macros for [`async-injector`](https://docs.rs/async-injector).
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
/// ```rust,no_run
/// use async_injector::Provider;
///
/// #[derive(Provider)]
/// struct DatabaseProvider {
///     #[dependency(tag = "\"url\"")]
///     url: String,
///     #[dependency]
///     connection_limit: u32,
/// }
///
/// #[derive(Debug, Clone)]
/// struct Database;
/// ```
///
/// # Field attributes
///
/// The `#[dependency]` attribute can be used to mark fields which need to be
/// injected. It takes an optional `#[dependency(tag = "..")]`, which allows you
/// to specify the tag to use when constructing the injected [Key].
///
/// ```rust,no_run
/// use async_injector::Provider;
///
/// #[derive(Provider)]
/// struct DatabaseParams {
///     #[dependency(tag = "\"url\"")]
///     url: String,
///     #[dependency]
///     connection_limit: u32,
/// }
/// ```
///
/// # Examples
///
/// ```rust,no_run
/// use async_injector::{Injector, Key, Provider};
/// use serde::Serialize;
/// use tokio_stream::StreamExt as _;
///
/// /// Fake database connection.
/// #[derive(Clone, Debug, PartialEq, Eq)]
/// struct Database {
///     url: String,
///     connection_limit: u32,
/// }
///
/// /// Provider that describes how to construct a database.
/// #[derive(Serialize)]
/// pub enum Tag {
///     DatabaseUrl,
///     ConnectionLimit,
/// }
///
/// #[derive(Provider)]
/// struct DatabaseParams {
///     #[dependency(tag = "Tag::DatabaseUrl")]
///     url: String,
///     #[dependency(tag = "Tag::ConnectionLimit")]
///     connection_limit: u32,
/// }
///
/// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let db_url_key = Key::<String>::tagged(Tag::DatabaseUrl)?;
/// let conn_limit_key = Key::<u32>::tagged(Tag::ConnectionLimit)?;
///
/// let injector = Injector::new();
///
/// let database_injector = injector.clone();
/// let mut database = DatabaseParams::provider(&injector).await?;
///
/// tokio::spawn(async move {
///     loop {
///         match database.update().await {
///             Some(update) => {
///                 database_injector.update(Database {
///                     url: update.url,
///                     connection_limit: update.connection_limit,
///                 }).await;
///             }
///             None => {
///                 database_injector.clear::<Database>().await;
///             }
///         }
///     }
/// });
///
/// let (mut database_stream, database) = injector.stream::<Database>().await;
///
/// // None of the dependencies are available, so it hasn't been constructed.
/// assert!(database.is_none());
///
/// assert!(injector
///     .update_key(&db_url_key, String::from("example.com"))
///     .await
///     .is_none());
///
/// assert!(injector.update_key(&conn_limit_key, 5).await.is_none());
///
/// let new_database = database_stream
///     .next()
///     .await
///     .expect("unexpected end of stream");
///
/// // Database instance is available!
/// assert_eq!(
///     new_database,
///     Some(Database {
///         url: String::from("example.com"),
///         connection_limit: 5
///     })
/// );
///
/// Ok(())
/// # }
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
fn provider_config<'a>(st: &'a DataStruct) -> syn::Result<ProviderConfig<'a>> {
    let fields = provider_fields(st)?;

    Ok(ProviderConfig { fields })
}

/// Extracts provider fields.
fn provider_fields<'a>(st: &'a DataStruct) -> syn::Result<Vec<ProviderField<'a>>> {
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
                tag: match dep.tag {
                    Some(tag) => Some(
                        syn::parse_str::<TokenStream>(&tag).expect("`tag` to be valid expression"),
                    ),
                    None => None,
                },
                optional: dep.optional,
                key_field: Ident::new(&format!("__key__{}", ident), Span::call_site()),
                ty: if dep.optional {
                    optional_ty(&field.ty)
                } else {
                    &field.ty
                },
            }),
            None => None,
        };

        fields.push(ProviderField {
            ident: &ident,
            field: &field,
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

        if let Some(dep) = &f.dependency {
            let field_ty = dep.ty;

            provider_fields.push(quote!(#field_stream: ::async_injector::Stream<#field_ty>));
            provider_fields.push(quote!(#field_ident: Option<#field_ty>));

            let key = match &dep.tag {
                Some(tag) => quote!(::async_injector::Key::<#field_ty>::tagged(#tag)?),
                None => quote!(::async_injector::Key::<#field_ty>::of()),
            };

            constructor_assign.push(quote! {
                let (#field_stream, #field_ident) = __injector.stream_key(#key).await;
            });

            constructor_fields.push(quote! { #field_stream });
            constructor_fields.push(quote! { #field_ident });

            injected_update.push(quote! {
                Some(#field_ident) = ::async_injector::derive::StreamExt::next(&mut self.#field_stream) => {
                    self.#field_ident = #field_ident;
                }
            });

            if dep.optional {
                initialized_fields.push(quote_spanned! { f.field.span() =>
                    #field_ident: self.#field_ident.as_ref().map(Clone::clone),
                });
            } else {
                provider_extract.push(quote_spanned! { f.field.span() =>
                    let #field_ident = match self.#field_ident.as_ref() {
                        Some(#field_ident) => #field_ident,
                        None => return None,
                    };
                });

                initialized_fields.push(quote_spanned! { dep.span =>
                    #field_ident: #field_ident.clone(),
                });
            };
        } else {
            let field_ty = &f.field.ty;

            provider_fields.push(quote!(#field_ident: #field_ty));

            initialized_fields.push(quote_spanned! { f.field.span() =>
                #field_ident: self.#field_ident.clone(),
            });

            constructor_fields.push(quote! { #field_ident });

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
            __injector_init: bool,
            #(#provider_fields,)*
        }

        impl #generics #provider_ident #generics {
            /// Construct a new provider.
            #vis async fn new(__injector: &::async_injector::Injector #(, #args)*) -> Result<#provider_ident #generics, ::async_injector::Error> {
                #(#constructor_assign)*

                Ok(#provider_ident {
                    __injector_init: false,
                    #(#constructor_fields,)*
                })
            }

            /// Update the provided value.
            #vis async fn update(&mut self) -> Option<#ident #generics> {
                loop {
                    if !::std::mem::take(&mut self.__injector_init) {
                        ::async_injector::derive::select! {
                            #(#injected_update)*
                        }
                    }

                    #(#provider_extract)*

                    return Some(#ident {
                        #(#initialized_fields)*
                    });
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
                GenericArgument::Type(ref ty) => return ty,
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
    key_field: Ident,
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
