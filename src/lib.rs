//! [<img alt="github" src="https://img.shields.io/badge/github-udoprog/async--injector-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/async-injector)
//! [<img alt="crates.io" src="https://img.shields.io/crates/v/async-injector.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/async-injector)
//! [<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-async--injector-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/async-injector)
//!
//! Asynchronous dependency injection for Rust.
//!
//! This library provides the glue which allows for building robust decoupled
//! applications that can be reconfigured dynamically while they are running.
//!
//! For a real world example of how this is used, see [`OxidizeBot`] for which
//! it was written.
//!
//! <br>
//!
//! ## Usage
//!
//! Add `async-injector` to your `Cargo.toml`.
//!
//! ```toml
//! [dependencies]
//! async-injector = "0.19.2"
//! ```
//!
//! <br>
//!
//! ## Example
//!
//! In the following we'll showcase the injection of a *fake* `Database`. The
//! idea here would be that if something about the database connection changes,
//! a new instance of `Database` would be created and cause the application to
//! reconfigure itself.
//!
//! ```rust
//! use async_injector::{Key, Injector, Provider};
//!
//! #[derive(Debug, Clone)]
//! struct Database;
//!
//! #[derive(Debug, Provider)]
//! struct Service {
//!     #[dependency]
//!     database: Database,
//! }
//!
//! async fn service(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
//!     let mut provider = Service::provider(&injector).await?;
//!
//!     let Service { database } = provider.wait().await;
//!     println!("Service got initial database {database:?}!");
//!
//!     let Service { database } = provider.wait().await;
//!     println!("Service got new database {database:?}!");
//!
//!     Ok(())
//! }
//! ```
//!
//! > **Note:** This is available as the `database` example:
//! > ```sh
//! > cargo run --example database
//! > ```
//!
//! The [`Injector`] above provides a structured broadcasting system that allows
//! for configuration updates to be cleanly integrated into asynchronous
//! contexts. The update itself is triggered by some other component that is
//! responsible for constructing the `Database` instance.
//!
//! Building up the components of your application like this means that it can
//! be reconfigured without restarting it. Providing a much richer user
//! experience.
//!
//! <br>
//!
//! ## Injecting multiple things of the same type
//!
//! In the previous section you might've noticed that the injected value was
//! solely discriminated by its type: `Database`. In this example we'll show how
//! [`Key`] can be used to *tag* values of the same type with different names to
//! discriminate them. This can be useful when dealing with overly generic types
//! like [`String`].
//!
//! The tag used must be serializable with [`serde`]. It must also not use any
//! components which [cannot be hashed], like `f32` and `f64`.
//!
//! <br>
//!
//! ### A simple greeter
//!
//! The following example showcases the use of `Key` to injector two different
//! values into an asynchronous `greeter`.
//!
//! ```rust,no_run
//! use async_injector::{Key, Injector};
//!
//! async fn greeter(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
//!     let name = Key::<String>::tagged("name")?;
//!     let fun = Key::<String>::tagged("fun")?;
//!
//!     let (mut name_stream, mut name) = injector.stream_key(name).await;
//!     let (mut fun_stream, mut fun) = injector.stream_key(fun).await;
//!
//!     loop {
//!         tokio::select! {
//!             update = name_stream.recv() => {
//!                 name = update;
//!             }
//!             update = fun_stream.recv() => {
//!                 fun = update;
//!             }
//!         }
//!
//!         let (Some(name), Some(fun)) = (&name, &fun) else {
//!             continue;
//!         };
//!
//!         println!("Hi {name}! I see you do \"{fun}\" for fun!");
//!         return Ok(());
//!     }
//! }
//! ```
//!
//! > **Note:** you can run this using:
//! > ```sh
//! > cargo run --example greeter
//! > ```
//!
//! The loop above can be implemented more easily using the [`Provider`] derive,
//! so let's do that.
//!
//! ```rust,no_run
//! use async_injector::{Injector, Provider};
//!
//! #[derive(Provider)]
//! struct Dependencies {
//!     #[dependency(tag = "name")]
//!     name: String,
//!     #[dependency(tag = "fun")]
//!     fun: String,
//! }
//!
//! async fn greeter(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
//!     let mut provider = Dependencies::provider(&injector).await?;
//!     let Dependencies { name, fun } = provider.wait().await;
//!     println!("Hi {name}! I see you do \"{fun}\" for fun!");
//!     Ok(())
//! }
//! ```
//!
//! > **Note:** you can run this using:
//! > ```sh
//! > cargo run --example greeter_provider
//! > ```
//!
//! <br>
//!
//! ## The `Provider` derive
//!
//! The [`Provider`] derive can be used to conveniently implement the mechanism
//! necessary to wait for a specific set of dependencies to become available.
//!
//! It builds a companion structure next to the type being provided called
//! `<name>Provider` which in turn implements the following set of methods:
//!
//! ```rust,no_run
//! use async_injector::{Error, Injector};
//!
//! # struct Dependencies {}
//! impl Dependencies {
//!     /// Construct a new provider.
//!     async fn provider(injector: &Injector) -> Result<DependenciesProvider, Error>
//!     # { todo!() }
//! }
//!
//! struct DependenciesProvider {
//!     /* private fields */
//! }
//!
//! impl DependenciesProvider {
//!     /// Try to construct the current value. Returns [None] unless all
//!     /// required dependencies are available.
//!     fn build(&mut self) -> Option<Dependencies>
//!     # { todo!() }
//!
//!     /// Wait until we can successfully build the complete provided
//!     /// value.
//!     async fn wait(&mut self) -> Dependencies
//!     # { todo!() }
//!
//!     /// Wait until the provided value has changed. Either some
//!     /// dependencies are no longer available at which it returns `None`,
//!     /// or all dependencies are available after which we return the
//!     /// build value.
//!     async fn wait_for_update(&mut self) -> Option<Dependencies>
//!     # { todo!() }
//! }
//! ```
//!
//! <br>
//!
//! ### Fixed arguments to `Provider`
//!
//! Any arguments which do not have the `#[dependency]` attribute are known as
//! "fixed" arguments. These must be passed in when calling the `provider`
//! constructor. They can also be used during tag construction.
//!
//! ```rust,no_run
//! use async_injector::{Injector, Key, Provider};
//!
//! #[derive(Provider)]
//! struct Dependencies {
//!     name_tag: &'static str,
//!     #[dependency(tag = name_tag)]
//!     name: String,
//! }
//!
//! async fn greeter(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
//!     let mut provider = Dependencies::provider(&injector, "name").await?;
//!     let Dependencies { name, .. } = provider.wait().await;
//!     println!("Hi {name}!");
//!     Ok(())
//! }
//! ```
//!
//! [`OxidizeBot`]: https://github.com/udoprog/OxidizeBot
//! [cannot be hashed]: https://internals.rust-lang.org/t/f32-f64-should-implement-hash/5436
//! [`Injector`]: https://docs.rs/async-injector/0/async_injector/struct.Injector.html
//! [`Key`]: https://docs.rs/async-injector/0/async_injector/struct.Key.html
//! [`Provider`]: https://docs.rs/async-injector/0/async_injector/derive.Provider.html
//! [`serde`]: https://serde.rs
//! [`Stream`]: https://docs.rs/futures-core/0/futures_core/stream/trait.Stream.html
//! [`String`]: https://doc.rust-lang.org/std/string/struct.String.html

#![deny(missing_docs)]

use hashbrown::HashMap;
use serde_hashkey as hashkey;
use std::any::{Any, TypeId};
use std::cmp;
use std::error;
use std::fmt;
use std::hash;
use std::marker;
use std::mem;
use std::ptr;
use std::sync::Arc;
use tokio::sync::{broadcast, RwLock};

/// The read guard produced by [Ref::read].
pub type RefReadGuard<'a, T> = tokio::sync::RwLockReadGuard<'a, T>;

/// re-exports for the Provider derive.
#[doc(hidden)]
pub mod derive {
    pub use tokio::select;
}

/// Helper derive to implement a "provider".
///
/// The `Provider` derive can only be used on structs. Each field designates a
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
#[doc(inline)]
pub use async_injector_derive::Provider;

/// Errors that can be raised by various functions in the [`Injector`].
#[derive(Debug)]
pub enum Error {
    /// Error when serializing key.
    SerializationError(hashkey::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::SerializationError(..) => "serialization error".fmt(fmt),
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::SerializationError(e) => Some(e),
        }
    }
}

impl From<hashkey::Error> for Error {
    fn from(value: hashkey::Error) -> Self {
        Error::SerializationError(value)
    }
}

/// A stream of updates to a value in the [`Injector`].
///
/// This is created using [Injector::stream] or [Injector::stream_key] and can
/// be used to make sure that an asynchronous process has access to the most
/// up-to-date value from the injector.
pub struct Stream<T> {
    rx: broadcast::Receiver<Option<Value>>,
    marker: marker::PhantomData<T>,
}

impl<T> Stream<T> {
    /// Receive the next injected element from the stream.
    pub async fn recv(&mut self) -> Option<T> {
        let value = loop {
            let value = self.rx.recv().await;

            match value {
                Ok(value) => break value,
                Err(broadcast::error::RecvError::Lagged { .. }) => continue,
                _ => return None,
            };
        };

        let value = match value {
            Some(value) => value,
            _ => return None,
        };

        // Safety: The expected type parameter is encoded and maintained in the
        // Stream<T> type.
        Some(unsafe { value.downcast::<T>() })
    }
}

/// An opaque value holder, similar to Any, but can be cloned and relies
/// entirely on external type information.
struct Value {
    data: *const (),
    // clone function, to use when cloning the value.
    value_clone_fn: unsafe fn(*const ()) -> *const (),
    // drop function, to use when dropping the value.
    value_drop_fn: unsafe fn(*const ()),
}

impl Value {
    /// Construct a new opaque value.
    pub(crate) fn new<T>(data: T) -> Self
    where
        T: 'static + Clone + Send + Sync,
    {
        return Self {
            data: Box::into_raw(Box::new(data)) as *const (),
            value_clone_fn: value_clone_fn::<T>,
            value_drop_fn: value_drop_fn::<T>,
        };

        /// Clone implementation for a given value.
        unsafe fn value_clone_fn<T>(data: *const ()) -> *const ()
        where
            T: Clone,
        {
            let data = T::clone(&*(data as *const _));
            Box::into_raw(Box::new(data)) as *const ()
        }

        /// Drop implementation for a given value.
        unsafe fn value_drop_fn<T>(value: *const ()) {
            ptr::drop_in_place(value as *mut () as *mut T)
        }
    }

    /// Downcast the given value reference.
    ///
    /// # Safety
    ///
    /// Assumes that we know the type of the underlying value.
    pub(crate) unsafe fn downcast_ref<T>(&self) -> &T {
        &*(self.data as *const T)
    }

    /// Downcast the given value to a mutable reference.
    ///
    /// # Safety
    ///
    /// Assumes that we know the type of the underlying value.
    pub(crate) unsafe fn downcast_mut<T>(&mut self) -> &mut T {
        &mut *(self.data as *const T as *mut T)
    }

    /// Downcast the given value.
    ///
    /// # Safety
    ///
    /// Assumes that we know the correct, underlying type of the value.
    pub(crate) unsafe fn downcast<T>(self) -> T {
        let value = Box::from_raw(self.data as *const T as *mut T);
        mem::forget(self);
        *value
    }
}

/// Safety: Send + Sync bound is enforced in all constructors of `Value`.
unsafe impl Send for Value {}
unsafe impl Sync for Value {}

impl Clone for Value {
    fn clone(&self) -> Self {
        let data = unsafe { (self.value_clone_fn)(self.data as *const _) };

        Self {
            data,
            value_clone_fn: self.value_clone_fn,
            value_drop_fn: self.value_drop_fn,
        }
    }
}

impl Drop for Value {
    fn drop(&mut self) {
        unsafe {
            (self.value_drop_fn)(self.data);
        }
    }
}

struct Storage {
    value: Arc<RwLock<Option<Value>>>,
    tx: broadcast::Sender<Option<Value>>,
}

impl Default for Storage {
    fn default() -> Self {
        let (tx, _) = broadcast::channel(1);
        Self {
            value: Arc::new(RwLock::new(None)),
            tx,
        }
    }
}

struct Inner {
    storage: RwLock<HashMap<RawKey, Storage>>,
}

/// An injector of dependencies.
///
/// Injectors are defined in hierarchies where an injector is either the root
/// injector as created using [Injector::new].
#[derive(Clone)]
pub struct Injector {
    inner: Arc<Inner>,
}

impl Injector {
    /// Construct and use an [`Injector`].
    ///
    /// # Example
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// # #[tokio::main] async fn main() {
    /// let injector = Injector::new();
    ///
    /// assert_eq!(None, injector.get::<u32>().await);
    /// injector.update(1u32).await;
    /// assert_eq!(Some(1u32), injector.get::<u32>().await);
    /// assert!(injector.clear::<u32>().await.is_some());
    /// assert_eq!(None, injector.get::<u32>().await);
    /// # }
    /// ```
    ///
    /// Example using a [`Stream`].
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    ///
    /// let database = injector.var::<Database>().await;
    ///
    /// assert!(database.read().await.is_none());
    /// injector.update(Database).await;
    /// assert!(database.read().await.is_some());
    /// # Ok(()) }
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Get a value from the injector.
    ///
    /// This will cause the clear to be propagated to all streams set up using
    /// [`stream`]. And for future calls to [`get`] to return the updated value.
    ///
    /// [`stream`]: Injector::stream
    /// [`get`]: Injector::get
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// # #[tokio::main] async fn main() {
    /// let injector = Injector::new();
    ///
    /// assert_eq!(None, injector.get::<u32>().await);
    /// injector.update(1u32).await;
    /// assert_eq!(Some(1u32), injector.get::<u32>().await);
    /// assert!(injector.clear::<u32>().await.is_some());
    /// assert_eq!(None, injector.get::<u32>().await);
    /// # }
    /// ```
    pub async fn clear<T>(&self) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        self.clear_key(Key::<T>::of()).await
    }

    /// Clear the given value with the given key.
    ///
    /// This will cause the clear to be propagated to all streams set up using
    /// [`stream`]. And for future calls to [`get`] to return the updated value.
    ///
    /// [`stream`]: Injector::stream
    /// [`get`]: Injector::get
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    /// let k = Key::<u32>::tagged("first")?;
    ///
    /// assert_eq!(None, injector.get_key(&k).await);
    /// injector.update_key(&k, 1u32).await;
    /// assert_eq!(Some(1u32), injector.get_key(&k).await);
    /// assert!(injector.clear_key(&k).await.is_some());
    /// assert_eq!(None, injector.get_key(&k).await);
    /// # Ok(()) }
    /// ```
    pub async fn clear_key<T>(&self, key: impl AsRef<Key<T>>) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();

        let storage = self.inner.storage.read().await;
        let storage = storage.get(key)?;
        let value = storage.value.write().await.take()?;
        let _ = storage.tx.send(None);
        Some(unsafe { value.downcast() })
    }

    /// Set the given value and notify any subscribers.
    ///
    /// This will cause the update to be propagated to all streams set up using
    /// [`stream`]. And for future calls to [`get`] to return the updated value.
    ///
    /// [`stream`]: Injector::stream
    /// [`get`]: Injector::get
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// # #[tokio::main]
    /// # async fn main() {
    /// let injector = Injector::new();
    ///
    /// assert_eq!(None, injector.get::<u32>().await);
    /// injector.update(1u32).await;
    /// assert_eq!(Some(1u32), injector.get::<u32>().await);
    /// # }
    /// ```
    pub async fn update<T>(&self, value: T) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        self.update_key(Key::<T>::of(), value).await
    }

    /// Update the value associated with the given key.
    ///
    /// This will cause the update to be propagated to all streams set up using
    /// [`stream`]. And for future calls to [`get`] to return the updated value.
    ///
    /// [`stream`]: Injector::stream
    /// [`get`]: Injector::get
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    /// let k = Key::<u32>::tagged("first")?;
    ///
    /// assert_eq!(None, injector.get_key(&k).await);
    /// injector.update_key(&k, 1u32).await;
    /// assert_eq!(Some(1u32), injector.get_key(&k).await);
    /// # Ok(()) }
    /// ```
    pub async fn update_key<T>(&self, key: impl AsRef<Key<T>>, value: T) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();
        let value = Value::new(value);

        let mut storage = self.inner.storage.write().await;
        let storage = storage.entry(key.clone()).or_default();
        let _ = storage.tx.send(Some(value.clone()));
        let old = storage.value.write().await.replace(value)?;
        Some(unsafe { old.downcast() })
    }

    /// Test if a given value exists by type.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    ///
    /// # #[tokio::main] async fn main() {
    /// let injector = Injector::new();
    ///
    /// assert_eq!(false, injector.exists::<u32>().await);
    /// injector.update(1u32).await;
    /// assert_eq!(true, injector.exists::<u32>().await);
    /// # }
    /// ```
    pub async fn exists<T>(&self) -> bool
    where
        T: Clone + Any + Send + Sync,
    {
        self.exists_key(Key::<T>::of()).await
    }

    /// Test if a given value exists by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    /// let k = Key::<u32>::tagged("first")?;
    ///
    /// assert_eq!(false, injector.exists_key(&k).await);
    /// injector.update_key(&k, 1u32).await;
    /// assert_eq!(true, injector.exists_key(&k).await);
    /// # Ok(()) }
    /// ```
    pub async fn exists_key<T>(&self, key: impl AsRef<Key<T>>) -> bool
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();
        let storage = self.inner.storage.read().await;

        if let Some(s) = storage.get(key) {
            s.value.read().await.is_some()
        } else {
            false
        }
    }

    /// Mutate the given value by type.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// # #[tokio::main] async fn main() {
    /// let injector = Injector::new();
    ///
    /// injector.update(1u32).await;
    ///
    /// let old = injector.mutate(|value: &mut u32| {
    ///     let old = *value;
    ///     *value += 1;
    ///     old
    /// }).await;
    ///
    /// assert_eq!(Some(1u32), old);
    /// # }
    /// ```
    pub async fn mutate<T, M, R>(&self, mutator: M) -> Option<R>
    where
        T: Clone + Any + Send + Sync,
        M: FnMut(&mut T) -> R,
    {
        self.mutate_key(Key::<T>::of(), mutator).await
    }

    /// Mutate the given value by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    /// let k = Key::<u32>::tagged("first")?;
    ///
    /// injector.update_key(&k, 1u32).await;
    ///
    /// let old = injector.mutate_key(&k, |value| {
    ///     let old = *value;
    ///     *value += 1;
    ///     old
    /// }).await;
    ///
    /// assert_eq!(Some(1u32), old);
    /// # Ok(()) }
    /// ```
    pub async fn mutate_key<T, M, R>(&self, key: impl AsRef<Key<T>>, mut mutator: M) -> Option<R>
    where
        T: Clone + Any + Send + Sync,
        M: FnMut(&mut T) -> R,
    {
        let key = key.as_ref().as_raw_key();
        let storage = self.inner.storage.read().await;

        let storage = match storage.get(key) {
            Some(s) => s,
            None => return None,
        };

        let mut value = storage.value.write().await;

        if let Some(value) = &mut *value {
            let output = mutator(unsafe { value.downcast_mut() });
            let value = value.clone();
            let _ = storage.tx.send(Some(value));
            return Some(output);
        }

        None
    }

    /// Get a value from the injector.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// # #[tokio::main] async fn main() {
    /// let injector = Injector::new();
    ///
    /// assert_eq!(None, injector.get::<u32>().await);
    /// injector.update(1u32).await;
    /// assert_eq!(Some(1u32), injector.get::<u32>().await);
    /// # }
    /// ```
    pub async fn get<T>(&self) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        self.get_key(Key::<T>::of()).await
    }

    /// Get a value from the injector with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let k1 = Key::<u32>::tagged("first")?;
    /// let k2 = Key::<u32>::tagged("second")?;
    ///
    /// let injector = Injector::new();
    ///
    /// assert_eq!(None, injector.get_key(&k1).await);
    /// assert_eq!(None, injector.get_key(&k2).await);
    ///
    /// injector.update_key(&k1, 1u32).await;
    ///
    /// assert_eq!(Some(1u32), injector.get_key(&k1).await);
    /// assert_eq!(None, injector.get_key(&k2).await);
    /// # Ok(()) }
    /// ```
    pub async fn get_key<T>(&self, key: impl AsRef<Key<T>>) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();
        let storage = self.inner.storage.read().await;

        let storage = match storage.get(key) {
            Some(storage) => storage,
            None => return None,
        };

        let value = storage.value.read().await;

        value.as_ref().map(|value| {
            // Safety: Ref<T> instances can only be produced by checked fns.
            unsafe { value.downcast_ref::<T>().clone() }
        })
    }

    /// Wait for a value to become available.
    ///
    /// Note that this could potentially wait forever if the value is never
    /// injected.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// # #[tokio::main]
    /// # async fn main() {
    /// let injector = Injector::new();
    ///
    /// injector.update(1u32).await;
    /// assert_eq!(1u32, injector.wait::<u32>().await);
    /// # }
    /// ```
    #[inline]
    pub async fn wait<T>(&self) -> T
    where
        T: Clone + Any + Send + Sync,
    {
        self.wait_key(Key::<T>::of()).await
    }

    /// Wait for a value associated with the given key to become available.
    ///
    /// Note that this could potentially wait forever if the value is never
    /// injected.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    /// let tag = Key::<u32>::tagged("first")?;
    ///
    /// injector.update_key(&tag, 1u32).await;
    /// assert_eq!(1u32, injector.wait_key(tag).await);
    /// # Ok(()) }
    /// ```
    pub async fn wait_key<T>(&self, key: impl AsRef<Key<T>>) -> T
    where
        T: Clone + Any + Send + Sync,
    {
        let (mut stream, value) = self.stream_key(key).await;

        if let Some(value) = value {
            return value;
        }

        loop {
            if let Some(value) = stream.recv().await {
                return value;
            }
        }
    }

    /// Get an existing value and setup a stream for updates at the same time.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// #[derive(Debug, Clone, PartialEq, Eq)]
    /// struct Database;
    ///
    /// # #[tokio::main] async fn main() {
    /// let injector = Injector::new();
    /// let (mut database_stream, mut database) = injector.stream::<Database>().await;
    ///
    /// // Update the key somewhere else.
    /// tokio::spawn({
    ///     let injector = injector.clone();
    ///
    ///     async move {
    ///         injector.update(Database).await;
    ///     }
    /// });
    ///
    /// let database = loop {
    ///     if let Some(update) = database_stream.recv().await {
    ///         break update;
    ///     }
    /// };
    ///
    /// assert_eq!(database, Database);
    /// # }
    /// ```
    pub async fn stream<T>(&self) -> (Stream<T>, Option<T>)
    where
        T: Clone + Any + Send + Sync,
    {
        self.stream_key(Key::<T>::of()).await
    }

    /// Get an existing value and setup a stream for updates at the same time.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    ///
    /// #[derive(Debug, Clone, PartialEq, Eq)]
    /// struct Database;
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    /// let db = Key::<Database>::tagged("first")?;
    /// let (mut database_stream, mut database) = injector.stream_key(&db).await;
    ///
    /// // Update the key somewhere else.
    /// tokio::spawn({
    ///     let db = db.clone();
    ///     let injector = injector.clone();
    ///
    ///     async move {
    ///         injector.update_key(&db, Database).await;
    ///     }
    /// });
    ///
    /// let database = loop {
    ///     if let Some(update) = database_stream.recv().await {
    ///         break update;
    ///     }
    /// };
    ///
    /// assert_eq!(database, Database);
    /// # Ok(()) }
    /// ```
    pub async fn stream_key<T>(&self, key: impl AsRef<Key<T>>) -> (Stream<T>, Option<T>)
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();

        let mut storage = self.inner.storage.write().await;
        let storage = storage.entry(key.clone()).or_default();

        let rx = storage.tx.subscribe();

        let value = storage.value.read().await;

        let value = value.as_ref().map(|value| {
            // Safety: The expected type parameter is encoded and maintained
            // in the Stream type.
            unsafe { value.downcast_ref::<T>().clone() }
        });

        let stream = Stream {
            rx,
            marker: marker::PhantomData,
        };

        (stream, value)
    }

    /// Get a synchronized reference for the given configuration key.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    ///
    /// let database = injector.var::<Database>().await;
    ///
    /// assert!(database.read().await.is_none());
    /// injector.update(Database).await;
    /// assert!(database.read().await.is_some());
    /// # Ok(()) }
    /// ```
    pub async fn var<T>(&self) -> Ref<T>
    where
        T: Clone + Any + Send + Sync + Unpin,
    {
        self.var_key(Key::<T>::of()).await
    }

    /// Get a synchronized reference for the given configuration key.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::{Key, Injector};
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn Error>> {
    /// let injector = Injector::new();
    /// let db = Key::<Database>::tagged("first")?;
    ///
    /// let database = injector.var_key(&db).await;
    ///
    /// assert!(database.read().await.is_none());
    /// injector.update_key(&db, Database).await;
    /// assert!(database.read().await.is_some());
    /// # Ok(()) }
    /// ```
    pub async fn var_key<T>(&self, key: impl AsRef<Key<T>>) -> Ref<T>
    where
        T: Clone + Any + Send + Sync + Unpin,
    {
        let key = key.as_ref().as_raw_key();

        let mut storage = self.inner.storage.write().await;
        let storage = storage.entry(key.clone()).or_default();

        Ref {
            value: storage.value.clone(),
            _m: marker::PhantomData,
        }
    }
}

impl Default for Injector {
    fn default() -> Self {
        Self {
            inner: Arc::new(Inner {
                storage: Default::default(),
            }),
        }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
struct RawKey {
    type_id: TypeId,
    tag_type_id: TypeId,
    tag: hashkey::Key,
}

impl RawKey {
    /// Construct a new raw key.
    fn new<T, K>(tag: hashkey::Key) -> Self
    where
        T: Any,
        K: Any,
    {
        Self {
            type_id: TypeId::of::<T>(),
            tag_type_id: TypeId::of::<K>(),
            tag,
        }
    }
}

/// A key used to discriminate a value in the [`Injector`].
#[derive(Clone)]
pub struct Key<T>
where
    T: Any,
{
    raw_key: RawKey,
    _marker: marker::PhantomData<T>,
}

impl<T> fmt::Debug for Key<T>
where
    T: Any,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.raw_key, fmt)
    }
}

impl<T> cmp::PartialEq for Key<T>
where
    T: Any,
{
    fn eq(&self, other: &Self) -> bool {
        self.as_raw_key().eq(other.as_raw_key())
    }
}

impl<T> cmp::Eq for Key<T> where T: Any {}

impl<T> cmp::PartialOrd for Key<T>
where
    T: Any,
{
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.as_raw_key().partial_cmp(other.as_raw_key())
    }
}

impl<T> cmp::Ord for Key<T>
where
    T: Any,
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_raw_key().cmp(other.as_raw_key())
    }
}

impl<T> hash::Hash for Key<T>
where
    T: Any,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        self.as_raw_key().hash(state);
    }
}

impl<T> Key<T>
where
    T: Any,
{
    /// Construct a new key without a tag.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Key;
    ///
    /// struct Foo;
    ///
    /// assert_eq!(Key::<Foo>::of(), Key::<Foo>::of());
    /// ```
    pub fn of() -> Self {
        Self {
            raw_key: RawKey::new::<T, ()>(hashkey::Key::Unit),
            _marker: marker::PhantomData,
        }
    }

    /// Construct a new key.
    ///
    /// # Examples
    ///
    /// ```
    /// use serde::Serialize;
    /// use async_injector::Key;
    ///
    /// struct Foo;
    ///
    /// #[derive(Serialize)]
    /// enum Tag {
    ///     One,
    ///     Two,
    /// }
    ///
    /// #[derive(Serialize)]
    /// enum Tag2 {
    ///     One,
    ///     Two,
    /// }
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// assert_eq!(Key::<Foo>::tagged(Tag::One)?, Key::<Foo>::tagged(Tag::One)?);
    /// assert_ne!(Key::<Foo>::tagged(Tag::One)?, Key::<Foo>::tagged(Tag::Two)?);
    /// assert_ne!(Key::<Foo>::tagged(Tag::One)?, Key::<Foo>::tagged(Tag2::One)?);
    /// # Ok(()) }
    /// ```
    pub fn tagged<K>(tag: K) -> Result<Self, Error>
    where
        K: Any + serde::Serialize,
    {
        let tag = hashkey::to_key(&tag)?;

        Ok(Self {
            raw_key: RawKey::new::<T, K>(tag),
            _marker: marker::PhantomData,
        })
    }

    /// Convert into a raw key.
    fn as_raw_key(&self) -> &RawKey {
        &self.raw_key
    }
}

impl<T> AsRef<Key<T>> for Key<T>
where
    T: 'static,
{
    fn as_ref(&self) -> &Self {
        self
    }
}

/// A variable allowing for the synchronized reading of avalue in the
/// [`Injector`].
///
/// This can be created through [Injector::var] or [Injector::var_key].
#[derive(Clone)]
pub struct Ref<T>
where
    T: Clone + Any + Send + Sync,
{
    value: Arc<RwLock<Option<Value>>>,
    _m: marker::PhantomData<T>,
}

impl<T> Ref<T>
where
    T: Clone + Any + Send + Sync,
{
    /// Read the synchronized variable.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    ///
    /// let database = injector.var::<Database>().await;
    ///
    /// assert!(database.read().await.is_none());
    /// injector.update(Database).await;
    /// assert!(database.read().await.is_some());
    /// # Ok(()) }
    /// ```
    pub async fn read(&self) -> Option<RefReadGuard<'_, T>> {
        let value = self.value.read().await;

        let result = RefReadGuard::try_map(value, |value| {
            value.as_ref().map(|value| {
                // Safety: The expected type parameter is encoded and
                // maintained in the Stream type.
                unsafe { value.downcast_ref::<T>() }
            })
        });

        result.ok()
    }

    /// Load the synchronized variable. This clones the underlying value if it
    /// has been set.
    ///
    /// # Examples
    ///
    /// ```
    /// use async_injector::Injector;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// # #[tokio::main] async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let injector = Injector::new();
    ///
    /// let database = injector.var::<Database>().await;
    ///
    /// assert!(database.load().await.is_none());
    /// injector.update(Database).await;
    /// assert!(database.load().await.is_some());
    /// # Ok(()) }
    /// ```
    pub async fn load(&self) -> Option<T> {
        let value = self.value.read().await;

        value.as_ref().map(|value| {
            // Safety: The expected type parameter is encoded and maintained
            // in the Stream type.
            unsafe { value.downcast_ref::<T>().clone() }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Value;

    #[test]
    fn test_clone() {
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        };

        let count = Arc::new(AtomicUsize::new(0));

        let value = Value::new(Foo(count.clone()));
        assert_eq!(0, count.load(Ordering::SeqCst));
        drop(value.clone());
        assert_eq!(1, count.load(Ordering::SeqCst));
        drop(value);
        assert_eq!(2, count.load(Ordering::SeqCst));

        #[derive(Clone)]
        struct Foo(Arc<AtomicUsize>);

        impl Drop for Foo {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }
    }
}
