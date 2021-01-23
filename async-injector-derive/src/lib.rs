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
/// # Container attributes
///
/// The `#[provider]` attribute is an attribute that must be used.
///
/// The available attributes are:
/// * `#[provider(output = "...")]` - which is used to specify the type of the
///   provided value.
/// * `#[provider(build = "...")]` (optional) - which can be used to specify a
///   custom *build* function. If no build function is specified, the value will
///   always be cleared.
/// * `#[provider(clear = "...")]` (optional) - which can be used to specify a
///   custom *clear* function.
///
/// We must specify the output type of the `Provider` using `#[provider(output =
/// "...")]` like this:
///
/// ```rust,no_run
/// use async_injector::Provider;
///
/// #[derive(Provider)]
/// #[provider(output = "Database")]
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
/// #[provider(output = "Database", build = "Database::build", clear = "Database::clear")]
/// struct DatabaseProvider {
///     #[dependency(tag = "\"url\"")]
///     url: String,
///     #[dependency]
///     connection_limit: u32,
/// }
///
/// #[derive(Debug, Clone)]
/// struct Database {
///     url: String,
/// }
///
/// impl Database {
///     /// Logic for how to build the injected value with all dependencies available.
///     async fn build(provider: DatabaseProvider) -> Option<Self> {
///         Some(Self {
///             url: provider.url,
///         })
///     }
///
///     /// Logic for how to clear the injected value.
///     async fn clear() -> Option<Self> {
///         None
///     }
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
/// impl Database {
///     async fn build(provider: DatabaseProvider2) -> Option<Self> {
///         Some(Self {
///             url: provider.url,
///             connection_limit: provider.connection_limit,
///         })
///     }
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
/// #[provider(output = "Database", build = "Database::build")]
/// struct DatabaseProvider2 {
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
/// tokio::spawn(DatabaseProvider2::run(injector.clone()));
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
#[proc_macro_derive(Provider, attributes(provider, dependency))]
pub fn provider_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(input as DeriveInput);
    let gen = implement(&ast);
    gen.into()
}

/// Derive to implement the `Provider` trait.
fn implement(ast: &DeriveInput) -> TokenStream {
    let st = match ast.data {
        Data::Struct(ref st) => st,
        _ => panic!("`Provider` attribute is only supported on structs"),
    };

    let config = provider_config(ast, st);
    let (factory, factory_ident) = impl_factory(ast, &config);
    let (builder, builder_ident) = impl_builder(ast, &factory_ident, &config);
    let maybe_run = impl_immediate_run(&config);

    let ident = &ast.ident;
    let generics = &ast.generics;

    let output = quote! {
        #builder

        #factory

        impl#generics #ident#generics {
            #maybe_run

            pub fn builder() -> #builder_ident#generics {
                #builder_ident::new()
            }
        }
    };

    output
}

/// Build a provider configuration.
fn provider_config<'a>(ast: &'a DeriveInput, st: &'a DataStruct) -> ProviderConfig<'a> {
    let fields = provider_fields(st);
    let mut provider = None;

    for a in &ast.attrs {
        let meta = match a.parse_meta() {
            Ok(meta) => meta,
            _ => continue,
        };

        if meta.path().is_ident("provider") {
            if provider.is_some() {
                panic!("multiple #[provider] attributes are not supported");
            }

            provider = if let Meta::Path(_) = meta {
                None
            } else {
                Some(match ProviderAttr::from_meta(&meta) {
                    Ok(d) => d,
                    Err(e) => panic!("bad #[provider(..)] attribute: {}", e),
                })
            };

            continue;
        }
    }

    let provider = provider.expect("missing #[provider(..)] attribute");

    ProviderConfig {
        fields,
        provider,
        generics: &ast.generics,
    }
}

/// Extracts provider fields.
fn provider_fields<'a>(st: &'a DataStruct) -> Vec<ProviderField<'a>> {
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
                    panic!("multiple #[dependency] attributes are not supported");
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

    fields
}

/// Constructs a builder for the given provider.
fn impl_builder<'a>(
    ast: &DeriveInput,
    factory_ident: &Ident,
    config: &ProviderConfig<'a>,
) -> (TokenStream, Ident) {
    let ident = Ident::new(&format!("{}Builder", ast.ident), Span::call_site());

    let mut field_idents = Vec::new();
    let mut builder_fields = Vec::new();
    let mut builder_inits = Vec::new();
    let mut builder_setters = Vec::new();
    let mut builder_assign = Vec::new();

    for f in &config.fields {
        let field_ident = &f.ident;

        field_idents.push(f.ident.clone());

        if let Some(dep) = &f.dependency {
            let field_ty = &dep.ty;

            builder_fields.push(quote!(#field_ident: Option<#field_ty>,));
            builder_inits.push(quote!(#field_ident: None,));
            builder_assign.push(quote! {
                let #field_ident = None;
            });

            let key = match &dep.tag {
                Some(tag) => quote!(::async_injector::Key::<#field_ty>::tagged(#tag)?),
                None => quote!(::async_injector::Key::<#field_ty>::of()),
            };

            let key_ident = &dep.key_field;
            builder_assign.push(quote!(let #key_ident = #key;));
            field_idents.push(key_ident.clone());
        } else {
            let field_ty = &f.field.ty;

            builder_fields.push(quote!(#field_ident: Option<#field_ty>,));
            builder_inits.push(quote!(#field_ident: None,));
            builder_setters.push(quote! {
                fn #field_ident(self, #field_ident: #field_ty) -> Self {
                    Self {
                        #field_ident: Some(#field_ident),
                        ..self
                    }
                }
            });

            let message = format!("{}: expected value assigned in builder", field_ident);

            builder_assign.push(quote! {
                let #field_ident = self.#field_ident.expect(#message);
            });
        }
    }

    let vis = &ast.vis;
    let generics = &config.generics;

    let builder = quote! {
        #vis struct #ident#generics {
            #(#builder_fields)*
        }

        impl#generics #ident#generics {
            pub fn new() -> Self {
                Self {
                    #(#builder_inits)*
                }
            }

            pub fn build(self) -> Result<#factory_ident#generics, ::async_injector::Error> {
                #(#builder_assign)*

                Ok(#factory_ident {
                    #(#field_idents,)*
                })
            }

            #(#builder_setters)*
        }
    };

    (builder, ident)
}

/// Build the factory instance.
///
/// The factory is responsible for building providers that builds instances of
/// the provided type.
///
/// This step is necessary to support "fixed" fields, i.e. fields who's value
/// are provided at build time.
fn impl_factory<'a>(ast: &DeriveInput, config: &ProviderConfig<'a>) -> (TokenStream, Ident) {
    let factory_ident = Ident::new(&format!("{}Factory", ast.ident), Span::call_site());

    let mut provider_fields = Vec::new();
    let mut injected_fields_init = Vec::new();
    let mut injected_update = Vec::new();
    let mut provider_extract = Vec::new();
    let mut provider_clone = Vec::new();
    let mut initialized_fields = Vec::new();

    let output = syn::parse_str::<TokenStream>(&config.provider.output)
        .expect("`output` to be valid expression");

    for f in &config.fields {
        let field_ident = &f.ident;

        let field_stream = Ident::new(&format!("{}_stream", field_ident), Span::call_site());

        if let Some(dep) = &f.dependency {
            let field_ty = dep.ty;
            let key_ident = &dep.key_field;

            provider_fields.push(quote!(#field_ident: Option<#field_ty>,));
            provider_fields.push(quote!(#key_ident: ::async_injector::Key<#field_ty>,));

            injected_fields_init.push(quote! {
                let (mut #field_stream, #field_ident) = __injector.stream_key(&self.#key_ident).await;
                self.#field_ident = #field_ident;
            });

            injected_update.push(quote! {
                #field_ident = ::async_injector::derive::StreamExt::next(&mut #field_stream) => {
                    self.#field_ident = #field_ident.unwrap();
                }
            });

            if dep.optional {
                provider_extract.push(quote! {
                    let #field_ident = match self.#field_ident.as_ref() {
                        Some(#field_ident) => Some(#field_ident),
                        None => None,
                    };
                });

                provider_clone.push(quote_spanned! { f.field.span() =>
                    let #field_ident: Option<String> = #field_ident.map(Clone::clone);
                });
            } else {
                let clear = match &config.provider.clear {
                    Some(clear) => {
                        let clear = syn::parse_str::<TokenStream>(&clear)
                            .expect("`clear` to be valid expression");

                        quote_spanned! { f.field.span() =>
                            match #clear().await {
                                Some(output) => { __injector.update::<#output>(output).await; }
                                None => { let _ = __injector.clear::<#output>().await; }
                            }
                        }
                    }
                    None => quote! {
                        let _ = __injector.clear::<#output>().await;
                    },
                };

                provider_extract.push(quote_spanned! { f.field.span() =>
                    let #field_ident = match self.#field_ident.as_ref() {
                        Some(#field_ident) => #field_ident,
                        None => {
                            #clear
                            continue;
                        },
                    };
                });

                provider_clone.push(quote_spanned! { dep.span =>
                    let #field_ident = #field_ident.clone();
                });
            };
        } else {
            let field_ty = &f.field.ty;

            provider_fields.push(quote!(#field_ident: #field_ty,));

            provider_clone.push(quote_spanned! { f.field.span() =>
                let #field_ident = self.#field_ident.clone();
            });
        }

        initialized_fields.push(quote!(#field_ident,));
    }

    let build = match &config.provider.build {
        Some(build) => {
            let build =
                syn::parse_str::<TokenStream>(&build).expect("`build` to be valid expression");

            quote! {
                match #build(builder).await {
                    Some(output) => { __injector.update::<#output>(output).await; }
                    None => { let _ = __injector.clear::<#output>().await; }
                }
            }
        }
        None => quote! {
            let _ = __injector.clear::<#output>().await;
        },
    };

    let ident = &ast.ident;

    let provider_construct = quote! {
        let builder = #ident {
            #(#initialized_fields)*
        };

        #build
    };

    let vis = &ast.vis;
    let generics = &config.generics;

    let factory = quote_spanned! { ast.span() =>
        #vis struct #factory_ident#generics {
            #(#provider_fields)*
        }

        impl#generics #factory_ident#generics {
            pub async fn run(mut self, __injector: ::async_injector::Injector) -> Result<(), ::async_injector::Error> {
                #(#injected_fields_init)*

                let mut __injector_init = true;

                loop {
                    if !::std::mem::take(&mut __injector_init) {
                        ::async_injector::derive::select! {
                            #(#injected_update)*
                        }
                    }

                    #(#provider_extract)*
                    #(#provider_clone)*

                    #provider_construct
                }
            }
        }
    };

    (factory, factory_ident)
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

/// Constructs an immediate run implementation if there are no fixed dependencies.
fn impl_immediate_run<'a>(config: &ProviderConfig<'a>) -> Option<TokenStream> {
    for f in &config.fields {
        if f.dependency.is_none() {
            return None;
        }
    }

    let run = quote! {
        pub async fn run(__injector: ::async_injector::Injector) -> Result<(), ::async_injector::Error> {
            let mut provider = Self::builder().build()?;
            provider.run(__injector).await
        }
    };

    Some(run)
}

struct ProviderConfig<'a> {
    fields: Vec<ProviderField<'a>>,
    provider: ProviderAttr,
    generics: &'a Generics,
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
    optional: bool,
}

/// #[provider(...)] attribute
#[derive(Debug, Default, FromMeta)]
struct ProviderAttr {
    /// Output type of the provider.
    output: String,
    /// Builder function for a provider.
    #[darling(default)]
    build: Option<String>,
    /// Clear function for a provider.
    #[darling(default)]
    clear: Option<String>,
}
