//! [<img alt="github" src="https://img.shields.io/badge/github-udoprog/async--injector-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/async-injector)
//! [<img alt="crates.io" src="https://img.shields.io/crates/v/async-injector-derive.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/async-injector-derive)
//! [<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-async--injector--derive-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/async-injector-derive)
//!
//! Macros for [async-injector](https://docs.rs/async-injector).
//!
//! This provides the [Provider] derive, which can be used to automatically
//! construct and inject dependencies. See its documentation for how to use.
//!
//! [Provider]: https://docs.rs/async-injector/latest/async_injector/derive.Provider.html

mod implement;

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
///     #[dependency(optional, tag = Tag::Table)]
///     table: Option<String>,
///     #[dependency(tag = Tag::Url)]
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
/// injected. It takes an optional `#[dependency(tag = ...)]`, which allows you
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
///     #[dependency(tag = Tag::First)]
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
    let ast = syn::parse_macro_input!(input as syn::DeriveInput);

    let cx = implement::Ctxt::default();

    if let Ok(tokens) = implement::implement(&cx, &ast) {
        return tokens.into();
    }

    cx.into_errors().into()
}
