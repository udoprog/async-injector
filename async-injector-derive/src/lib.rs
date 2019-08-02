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

    ProviderConfig {
        fields,
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

        let dependency = match dependency {
            Some(dep) => Some(Dependency {
                tag: match dep.tag {
                    Some(tag) => Some(syn::parse_str::<TokenStream>(&tag).expect("`tag` to be valid expression")),
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

    for f in &config.fields {
        let field_ident = &f.ident;

        let field_stream = Ident::new(&format!("{}_stream", field_ident), Span::call_site());

        if let Some(dep) = &f.dependency {
            let field_ty = dep.ty;
            let key_ident = &dep.key_field;

            provider_fields.push(quote!(#field_ident: Option<#field_ty>,));
            provider_fields.push(quote!(#key_ident: ::async_injector::Key<#field_ty>,));

            injected_fields_init.push(quote! {
                let (mut #field_stream, #field_ident) = __injector.stream_key(&self.#key_ident);
                self.#field_ident = #field_ident;
            });

            injected_update.push(quote! {
                #field_ident = #field_stream.select_next_some() => {
                    self.#field_ident = #field_ident;
                }
            });

            if dep.optional {
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
                            match #ident::clear().await {
                                Some(value) => __injector.update(value),
                                None => __injector.clear::<<#ident as ::async_injector::Provider>::Output>(),
                            }

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

    let provider_construct = quote! {
        let builder = #ident {
            #(#initialized_fields)*
        };

        match builder.build().await {
            Some(value) => __injector.update(value),
            None => __injector.clear::<<#ident as ::async_injector::Provider>::Output>(),
        }
    };

    let generics = &config.generics;

    let factory = quote! {
        #vis struct #factory_ident#generics {
            #(#provider_fields)*
        }

        impl#generics #factory_ident#generics {
            pub async fn run(mut self, __injector: &::async_injector::Injector) -> Result<(), ::async_injector::Error> {
                use ::futures::stream::StreamExt as _;
                use ::async_injector::Provider as _;

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
) -> Option<TokenStream> {
    for f in &config.fields {
        if f.dependency.is_none() {
            return None;
        }
    }

    let run = quote! {
        pub async fn run(__injector: &::async_injector::Injector) -> Result<(), ::async_injector::Error> {
            let mut provider = Self::builder().build()?;
            provider.run(__injector).await
        }
    };

    Some(run)
}

struct ProviderConfig<'a> {
    fields: Vec<ProviderField<'a>>,
    generics: &'a Generics,
}

struct ProviderField<'a> {
    ident: &'a Ident,
    field: &'a Field,
    dependency: Option<Dependency<'a>>,
}

#[derive(Debug)]
struct Dependency<'a> {
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
