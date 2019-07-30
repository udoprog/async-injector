#![recursion_limit = "256"]

extern crate proc_macro;

use darling::FromMeta;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::*;

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
    let (factory, factory_ident) = impl_factory(&ast.vis, &ast.ident, &config);
    let (builder, builder_ident) = impl_builder(&ast.vis, &ast.ident, &factory_ident, &config);
    let maybe_run = impl_immediate_run(&config, &factory_ident);

    let ident = &ast.ident;

    quote! {
        #builder

        #factory

        impl #ident {
            #maybe_run

            pub fn builder() -> #builder_ident {
                #builder_ident::new()
            }
        }
    }
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

        if meta.name() == "provider" {
            provider = Some(match ProviderAttr::from_meta(&meta) {
                Ok(d) => d,
                Err(e) => panic!("bad #[provider(..)] attribute: {}", e),
            });

            continue;
        }
    }

    let provider = match provider {
        Some(provider) => provider,
        None => panic!("missing #[provider(..)] attribute"),
    };

    ProviderConfig { provider, fields }
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

            if meta.name() == "dependency" {
                if dependency.is_some() {
                    panic!("multiple #[dependency] attributes are not supported");
                }

                dependency = Some(if let Meta::Word(_) = meta {
                    DependencyAttr::default()
                } else {
                    match DependencyAttr::from_meta(&meta) {
                        Ok(d) => d,
                        Err(e) => panic!("bad #[dependency(..)] attribute: {}", e),
                    }
                });

                continue;
            }
        }

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
    vis: &Visibility,
    ident: &Ident,
    factory_ident: &Ident,
    config: &ProviderConfig<'a>,
) -> (TokenStream, Ident) {
    let ident = Ident::new(&format!("{}Builder", ident), Span::call_site());

    let mut field_idents = Vec::new();
    let mut builder_fields = Vec::new();
    let mut builder_inits = Vec::new();
    let mut builder_setters = Vec::new();
    let mut builder_assign = Vec::new();

    for f in &config.fields {
        let field_ident = &f.ident;
        let field_ty = &f.field.ty;

        field_idents.push(f.ident.clone());

        if let Some(_dependency) = &f.dependency {
            builder_fields.push(quote!(#field_ident: Option<#field_ty>,));
            builder_inits.push(quote!(#field_ident: None,));
            builder_assign.push(quote! {
                let #field_ident = None;
            });
        } else {
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

    let builder = quote! {
        #vis struct #ident {
            #(#builder_fields)*
        }

        impl #ident {
            pub fn new() -> Self {
                Self {
                    #(#builder_inits)*
                }
            }

            pub fn build(self) -> #factory_ident {
                #(#builder_assign)*

                #factory_ident {
                    #(#field_idents,)*
                }
            }

            #(#builder_setters)*
        }
    };

    (builder, ident)
}

fn impl_factory<'a>(
    vis: &Visibility,
    ident: &Ident,
    config: &ProviderConfig<'a>,
) -> (TokenStream, Ident) {
    let factory_ident = Ident::new(&format!("{}Factory", ident), Span::call_site());

    let output = syn::parse_str::<TokenStream>(&config.provider.output)
        .expect("output: to be valid expression");
    let error = syn::parse_str::<TokenStream>(&config.provider.error)
        .expect("error: to be valid expression");

    let mut provider_fields = Vec::new();
    let mut injected_fields_init = Vec::new();
    let mut injected_update = Vec::new();
    let mut provider_extract = Vec::new();
    let mut provider_clone = Vec::new();
    let mut initialized_fields = Vec::new();

    for f in &config.fields {
        let field_ident = &f.ident;
        let field_ty = &f.field.ty;

        let field_stream = Ident::new(&format!("{}_stream", field_ident), Span::call_site());

        if let Some(dependency) = &f.dependency {
            provider_fields.push(quote!(#field_ident: Option<#field_ty>,));

            injected_update.push(quote! {
                #field_ident = #field_stream.select_next_some() => {
                    self.#field_ident = #field_ident;
                }
            });

            provider_extract.push(quote! {
                let #field_ident = match self.#field_ident.as_ref() {
                    Some(#field_ident) => #field_ident,
                    None => {
                        injector.clear::<#output>();
                        continue;
                    },
                };
            });

            provider_clone.push(quote! {
                let #field_ident = #field_ident.clone();
            });

            let key = if let Some(tag) = &dependency.tag {
                quote!(::async_injector::Key::<#field_ty>::tagged(#tag))
            } else {
                quote!(::async_injector::Key::<#field_ty>::of())
            };

            injected_fields_init.push(quote! {
                let (mut #field_stream, #field_ident) = injector.stream_key::<#field_ty>(&#key);
                self.#field_ident = #field_ident;
            });
        } else {
            provider_fields.push(quote!(#field_ident: #field_ty,));

            provider_clone.push(quote! {
                let #field_ident = self.#field_ident.clone();
            });
        }

        initialized_fields.push(quote!(#field_ident,));
    }

    let constructor = Ident::new(&config.provider.constructor, Span::call_site());

    let provider_construct = quote! {
        let builder = #ident {
            #(#initialized_fields)*
        };
        injector.update(builder.#constructor().await?);
    };

    let factory = quote! {
        #vis struct #factory_ident {
            #(#provider_fields)*
        }

        impl #factory_ident {
            pub async fn run(mut self, injector: &::async_injector::Injector) -> Result<(), #error> {
                use ::futures::stream::StreamExt as _;

                #(#injected_fields_init)*

                loop {
                    ::futures::select! {
                        #(#injected_update)*
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

/// Constructs an immediate run implementation if there are no fixed dependencies.
fn impl_immediate_run<'a>(
    config: &ProviderConfig<'a>,
    factory_ident: &Ident,
) -> Option<TokenStream> {
    let mut field_idents = Vec::new();

    for f in &config.fields {
        let field_ident = &f.ident;

        if f.dependency.is_some() {
            field_idents.push(quote!(#field_ident: None));
        } else {
            return None;
        }
    }

    let error = syn::parse_str::<TokenStream>(&config.provider.error)
        .expect("error: to be valid expression");

    let run = quote! {
        pub async fn run(injector: &::async_injector::Injector) -> Result<(), #error> {
            let mut provider = #factory_ident {
                #(#field_idents,)*
            };

            provider.run(injector).await
        }
    };

    Some(run)
}

struct ProviderConfig<'a> {
    provider: ProviderAttr,
    fields: Vec<ProviderField<'a>>,
}

struct ProviderField<'a> {
    ident: &'a Ident,
    field: &'a Field,
    dependency: Option<DependencyAttr>,
}

/// #[provider(...)] attribute
#[derive(Debug, FromMeta)]
struct ProviderAttr {
    constructor: String,
    output: String,
    error: String,
}

/// #[dependency(...)] attribute
#[derive(Debug, Default, FromMeta)]
#[darling(default)]
struct DependencyAttr {
    tag: Option<String>,
}
