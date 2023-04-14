use std::{cell::RefCell, fmt};

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{parse::ParseBuffer, spanned::Spanned as _};

#[derive(Default)]
pub(crate) struct Ctxt {
    errors: RefCell<Vec<syn::Error>>,
}

impl Ctxt {
    /// Test if context has an error.
    fn has_errors(&self) -> bool {
        !self.errors.borrow().is_empty()
    }

    /// Report an error.
    fn error(&self, span: Span, error: impl fmt::Display) {
        self.errors.borrow_mut().push(syn::Error::new(span, error));
    }

    pub(crate) fn into_errors(self) -> TokenStream {
        let mut stream = TokenStream::new();

        for error in self.errors.into_inner() {
            stream.extend(error.into_compile_error());
        }

        stream
    }
}

/// Derive to implement the `Provider` trait.
pub(crate) fn implement(cx: &Ctxt, ast: &syn::DeriveInput) -> Result<TokenStream, ()> {
    let syn::Data::Struct(st) = &ast.data else {
        cx.error(ast.span(), "`Provider` attribute is only supported on structs");
        return Err(());
    };

    let config = provider_config(cx, st)?;
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
fn provider_config<'a>(cx: &Ctxt, st: &'a syn::DataStruct) -> Result<ProviderConfig<'a>, ()> {
    let fields = provider_fields(cx, st)?;
    Ok(ProviderConfig { fields })
}

/// Extracts provider fields.
fn provider_fields<'a>(cx: &Ctxt, st: &'a syn::DataStruct) -> Result<Vec<ProviderField<'a>>, ()> {
    let mut fields = Vec::new();

    for field in &st.fields {
        let Some(ident) = &field.ident else {
            cx.error(field.span(), "missing identifier for field");
            continue;
        };

        let mut optional = false;
        let mut tag = None;
        let mut is_fixed = true;

        for a in &field.attrs {
            if !a.path().is_ident("dependency") {
                continue;
            }

            is_fixed = false;

            match &a.meta {
                syn::Meta::Path(..) => {}
                syn::Meta::List(list) => {
                    let result = list.parse_args_with(|input: &ParseBuffer| {
                        let mut end = false;

                        while !input.is_empty() {
                            if end {
                                cx.error(input.span(), "expected no more input");
                                break;
                            }

                            let ident = input.parse::<syn::Ident>()?;

                            if ident == "tag" {
                                let _ = input.parse::<syn::Token![=]>()?;
                                let expr = input.parse::<syn::Expr>()?;

                                if tag.is_some() {
                                    cx.error(
                                        expr.span(),
                                        "#[dependency(tag = ...)] can only be specified once",
                                    );
                                } else {
                                    tag = Some(expr);
                                }
                            } else if ident == "optional" {
                                if input.parse::<Option<syn::Token![=]>>()?.is_some() {
                                    optional = input.parse::<syn::LitBool>()?.value;
                                } else {
                                    optional = true;
                                }
                            } else {
                                cx.error(ident.span(), "unsupported key");
                            }

                            if input.parse::<Option<syn::Token![,]>>()?.is_none() {
                                end = true;
                            }
                        }

                        Ok(())
                    });

                    if let Err(error) = result {
                        cx.errors.borrow_mut().push(error);
                    }
                }
                syn::Meta::NameValue(..) => {
                    cx.error(a.span(), "unsupported value");
                    continue;
                }
            }
        }

        let dependency = if is_fixed {
            None
        } else {
            let ty = if optional {
                optional_ty(cx, &field.ty)
            } else {
                Some(&field.ty)
            };

            ty.map(|ty| Dependency {
                span: field.span(),
                tag,
                optional,
                ty,
            })
        };

        fields.push(ProviderField {
            ident,
            field,
            dependency,
        })
    }

    if cx.has_errors() {
        return Err(());
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
fn impl_provider(
    ast: &syn::DeriveInput,
    config: &ProviderConfig<'_>,
) -> (TokenStream, syn::Ident, Vec<TokenStream>, Vec<syn::Ident>) {
    let provider_ident = syn::Ident::new(&format!("{}Provider", ast.ident), Span::call_site());

    let mut provider_fields = Vec::new();
    let mut constructor_assign = Vec::new();
    let mut constructor_fields = Vec::new();
    let mut injected_update = Vec::new();
    let mut provider_extract = Vec::new();
    let mut initialized_fields = Vec::new();

    let mut fixed_args = Vec::new();
    let mut fixed_idents = Vec::new();

    let clone = quote!(::std::clone::Clone);

    for f in &config.fields {
        let field_ident = f.ident;
        let field_stream = syn::Ident::new(&format!("{}_stream", field_ident), Span::call_site());
        let field_value = syn::Ident::new(&format!("{}_value", field_ident), Span::call_site());

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
                    #field_ident: self.#field_value.as_ref().map(#clone::clone),
                });
            } else {
                provider_extract.push(quote_spanned! { f.field.span() =>
                    let #field_value = match self.#field_value.as_ref() {
                        Some(#field_value) => #field_value,
                        None => return None,
                    };
                });

                initialized_fields.push(quote_spanned! { dep.span =>
                    #field_ident: #clone::clone(#field_value),
                });
            };
        } else {
            let field_ty = &f.field.ty;

            provider_fields.push(quote!(#field_ident: #field_ty));

            initialized_fields.push(quote_spanned! { f.field.span() =>
                #field_ident: #clone::clone(&self.#field_ident),
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

        #[automatically_derived]
        #[allow(clippy::clone_double_ref)]
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
fn optional_ty<'a>(cx: &Ctxt, ty: &'a syn::Type) -> Option<&'a syn::Type> {
    let syn::Type::Path(path) = ty else {
        cx.error(ty.span(), format_args!("expected type generic argument"));
        return None;
    };

    let last = path.path.segments.last().expect("missing path segment");

    if last.ident != "Option" {
        cx.error(
            last.ident.span(),
            "optional field must be of type: Option<T>",
        );
        return None;
    }

    let syn::PathArguments::AngleBracketed(arguments) = &last.arguments else {
        cx.error(last.span(), format_args!("bad path arguments"));
        return None;
    };

    let Some(first) = arguments.args.first() else {
        cx.error(arguments.span(), "expected one generic argument");
        return None;
    };

    let syn::GenericArgument::Type(ty) = first else {
        cx.error(first.span(), "expected type generic argument");
        return None;
    };

    Some(ty)
}

struct ProviderConfig<'a> {
    fields: Vec<ProviderField<'a>>,
}

struct ProviderField<'a> {
    ident: &'a syn::Ident,
    field: &'a syn::Field,
    dependency: Option<Dependency<'a>>,
}

struct Dependency<'a> {
    /// The span of the dependency.
    span: Span,
    /// Expression that is used as a tag.
    tag: Option<syn::Expr>,
    /// If the field is optional.
    optional: bool,
    /// The type of the dependency.
    ty: &'a syn::Type,
}
