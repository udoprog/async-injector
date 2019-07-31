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

        if meta.name() == "provider" {
            provider = Some(match ProviderAttr::from_meta(&meta) {
                Ok(d) => d,
                Err(e) => panic!("bad #[provider(..)] attribute: {}", e),
            });

            continue;
        }
    }

    let (error, clear, constructor) = match provider {
        Some(ProviderAttr {
            ref error,
            ref clear,
            ref constructor,
        }) => (error.as_ref(), clear.as_ref(), constructor.as_ref()),
        None => (None, None, None),
    };

    let error = match error {
        Some(error) => {
            Some(syn::parse_str::<TokenStream>(error).expect("error: to be valid expression"))
        }
        None => None,
    };

    let clear = match clear {
        Some(clear) => Ident::new(clear, Span::call_site()),
        None => Ident::new("clear", Span::call_site()),
    };

    let constructor = match constructor {
        Some(constructor) => Ident::new(constructor, Span::call_site()),
        None => Ident::new("build", Span::call_site()),
    };

    ProviderConfig {
        error,
        fields,
        clear,
        constructor,
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

            pub fn build(self) -> #factory_ident#generics {
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

    let mut provider_fields = Vec::new();
    let mut injected_fields_init = Vec::new();
    let mut injected_update = Vec::new();
    let mut provider_extract = Vec::new();
    let mut provider_clone = Vec::new();
    let mut initialized_fields = Vec::new();

    let wait = match &config.error {
        Some(_) => quote!(await?),
        None => quote!(await),
    };

    for f in &config.fields {
        let field_ident = &f.ident;

        let field_stream = Ident::new(&format!("{}_stream", field_ident), Span::call_site());

        if let Some(dependency) = &f.dependency {
            let field_ty = if dependency.optional {
                optional_ty(&f.field.ty)
            } else {
                &f.field.ty
            };

            provider_fields.push(quote!(#field_ident: Option<#field_ty>,));

            let key = if let Some(tag) = &dependency.tag {
                quote!(::async_injector::Key::<#field_ty>::tagged(#tag))
            } else {
                quote!(::async_injector::Key::<#field_ty>::of())
            };

            injected_fields_init.push(quote! {
                let (mut #field_stream, #field_ident) = injector__.stream_key::<#field_ty>(&#key);
                self.#field_ident = #field_ident;
            });

            injected_update.push(quote! {
                #field_ident = #field_stream.select_next_some() => {
                    self.#field_ident = #field_ident;
                }
            });

            let clear = &config.clear;

            if dependency.optional {
                provider_extract.push(quote! {
                    let #field_ident = match self.#field_ident.as_ref() {
                        Some(#field_ident) => Some(#field_ident),
                        None => None,
                    };
                });

                provider_clone.push(quote! {
                    let #field_ident: Option<String> = #field_ident.map(Clone::clone);
                });
            } else {
                provider_extract.push(quote! {
                    let #field_ident = match self.#field_ident.as_ref() {
                        Some(#field_ident) => #field_ident,
                        None => {
                            #ident::#clear(&injector__).#wait;
                            continue;
                        },
                    };
                });

                provider_clone.push(quote! {
                    let #field_ident = #field_ident.clone();
                });
            };
        } else {
            let field_ty = &f.field.ty;

            provider_fields.push(quote!(#field_ident: #field_ty,));

            provider_clone.push(quote! {
                let #field_ident = self.#field_ident.clone();
            });
        }

        initialized_fields.push(quote!(#field_ident,));
    }

    let constructor = &config.constructor;

    let provider_construct = quote! {
        let builder = #ident {
            #(#initialized_fields)*
        };

        builder.#constructor(injector__).#wait;
    };

    let run_ret = match &config.error {
        Some(error) => quote!(Result<(), #error>),
        None => quote!(()),
    };

    let generics = &config.generics;

    let factory = quote! {
        #vis struct #factory_ident#generics {
            #(#provider_fields)*
        }

        impl#generics #factory_ident#generics {
            pub async fn run(mut self, injector__: &::async_injector::Injector) -> #run_ret {
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

/// Extract the optional type argument from the given type.
fn optional_ty(ty: &Type) -> &Type {
    match ty {
        Type::Path(ref path) => {
            let last = path.path.segments.last().expect("missing path segment").into_value();

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

    let run_ret = match &config.error {
        Some(error) => quote!(Result<(), #error>),
        None => quote!(()),
    };

    let run = quote! {
        pub async fn run(injector__: &::async_injector::Injector) -> #run_ret {
            let mut provider = #factory_ident {
                #(#field_idents,)*
            };

            provider.run(injector__).await
        }
    };

    Some(run)
}

struct ProviderConfig<'a> {
    error: Option<TokenStream>,
    fields: Vec<ProviderField<'a>>,
    clear: Ident,
    constructor: Ident,
    generics: &'a Generics,
}

struct ProviderField<'a> {
    ident: &'a Ident,
    field: &'a Field,
    dependency: Option<DependencyAttr>,
}

/// #[provider(...)] attribute
#[derive(Debug, FromMeta)]
struct ProviderAttr {
    #[darling(default)]
    clear: Option<String>,
    #[darling(default)]
    constructor: Option<String>,
    #[darling(default)]
    error: Option<String>,
}

/// #[dependency(...)] attribute
#[derive(Debug, Default, FromMeta)]
#[darling(default)]
struct DependencyAttr {
    tag: Option<String>,
    optional: bool,
}
