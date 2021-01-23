//! [![Documentation](https://docs.rs/async-injector/badge.svg)](https://docs.rs/async-injector)
//! [![Crates](https://img.shields.io/crates/v/async-injector.svg)](https://crates.io/crates/async-injector)
//! [![Actions Status](https://github.com/udoprog/async-injector/workflows/Rust/badge.svg)](https://github.com/udoprog/async-injector/actions)
//!
//! Asynchronous dependency injection for Rust.
//!
//! This crate provides a dependency injection system that can be used to
//! reactively reconfigure you're application while it's running. Reactive in
//! this case refers to the application being reconfigured as-the-value changes,
//! and not for other typical scenarios such as when it's being restarted.
//!
//! Values are provided as [Stream]s of updates that can be subscribed to as
//! necessary throughout your application.
//!
//! # Examples
//!
//! In the following we'll showcase the injection of a *fake* `Database`. The
//! idea here would be that if something about the database connection changes,
//! a new instance of `Database` would be created and cause the application to
//! update.
//!
//! > This is available as the `fake_database` example and you can run it
//! > yourself using:
//! > ```sh
//! > cargo run --example fake_database
//! > ```
//!
//! ```rust,no_run
//! use tokio::time;
//! use tokio_stream::StreamExt as _;
//!
//! #[derive(Clone)]
//! struct Database;
//!
//! #[tokio::main]
//! async fn main() {
//!     let injector = async_injector::setup();
//!     let (mut database_stream, mut database) = injector.stream::<Database>().await;
//!
//!     // Insert the database dependency in a different task in the background.
//!     tokio::spawn({
//!         let injector = injector.clone();
//!
//!         async move {
//!             time::sleep(time::Duration::from_secs(2)).await;
//!             injector.update(Database).await;
//!         }
//!     });
//!
//!     assert!(database.is_none());
//!
//!     // Every update to the stored type will be streamed, allowing you to
//!     // react to it.
//!     if let Some(update) = database_stream.next().await {
//!         println!("Updating database!");
//!         database = update;
//!     } else {
//!         panic!("No database update received :(");
//!     }
//!
//!     assert!(database.is_some());
//! }
//! ```
//!
//! The [Injector] provides a structured broadcast system of updates, that can
//! integrate cleanly into asynchronous contexts.
//!
//! With a bit of glue, this means that your application can be reconfigured
//! without restarting it. Providing a richer user experience.
//!
//! ## Injecting multiple things of the same type
//!
//! In the previous section you might've noticed that the injected value was
//! solely discriminated by its type: `Database`. In this example we'll show how
//! [Key] can be used to *tag* values of the same type under different names.
//! This can be useful when dealing with overly generic types like [String].
//!
//! The tag used must be serializable with [serde]. It must also not use any
//! components which [cannot be hashed], like `f32` and `f64`. This will
//! otherwise cause an error to be raised as it's being injected.
//!
//! ```rust,no_run
//! use async_injector::Key;
//! use serde::Serialize;
//! use std::{error::Error, time::Duration};
//! use tokio::time;
//! use tokio_stream::StreamExt as _;
//!
//! #[derive(Serialize)]
//! enum Tag {
//!     One,
//!     Two,
//! }
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn Error>> {
//!     let injector = async_injector::setup();
//!     let one = Key::<u32>::tagged(Tag::One)?;
//!     let two = Key::<u32>::tagged(Tag::Two)?;
//!
//!     tokio::spawn({
//!         let injector = injector.clone();
//!         let one = one.clone();
//!
//!         async move {
//!             let mut interval = time::interval(Duration::from_secs(1));
//!
//!             for i in 0u32.. {
//!                 interval.tick().await;
//!                 injector.update_key(&one, i).await;
//!             }
//!         }
//!     });
//!
//!     tokio::spawn({
//!         let injector = injector.clone();
//!         let two = two.clone();
//!
//!         async move {
//!             let mut interval = time::interval(Duration::from_secs(1));
//!
//!             for i in 0u32.. {
//!                 interval.tick().await;
//!                 injector.update_key(&two, i * 2).await;
//!             }
//!         }
//!     });
//!
//!     let (mut one_stream, mut one) = injector.stream_key(one).await;
//!     let (mut two_stream, mut two) = injector.stream_key(two).await;
//!
//!     println!("one: {:?}", one);
//!     println!("two: {:?}", two);
//!
//!     loop {
//!         tokio::select! {
//!             Some(update) = one_stream.next() => {
//!                 one = update;
//!                 println!("one: {:?}", one);
//!             }
//!             Some(update) = two_stream.next() => {
//!                 two = update;
//!                 println!("two: {:?}", two);
//!             }
//!         }
//!     }
//! }
//! ```
//!
//! # The `Provider` derive
//!
//! The following showcases how the [Provider] derive can be used to
//! automatically construct and inject dependencies.
//!
//! ```rust,no_run
//! use async_injector::{Key, Provider};
//! use serde::Serialize;
//! use tokio_stream::StreamExt as _;
//! use std::error::Error;
//!
//! /// Fake database connection.
//! #[derive(Clone, Debug, PartialEq, Eq)]
//! struct Database {
//!     url: String,
//!     connection_limit: u32,
//! }
//!
//! impl Database {
//!     async fn build(provider: DatabaseProvider) -> Option<Self> {
//!         Some(Self {
//!             url: provider.url,
//!             connection_limit: provider.connection_limit,
//!         })
//!     }
//! }
//!
//! /// Provider that describes how to construct a database.
//! #[derive(Serialize)]
//! pub enum Tag {
//!     DatabaseUrl,
//!     ConnectionLimit,
//! }
//!
//! #[derive(Provider)]
//! #[provider(output = "Database", build = "Database::build")]
//! struct DatabaseProvider {
//!     #[dependency(tag = "Tag::DatabaseUrl")]
//!     url: String,
//!     #[dependency(tag = "Tag::ConnectionLimit")]
//!     connection_limit: u32,
//! }
//!
//! #[tokio::test]
//! async fn test_provider() -> Result<(), Box<dyn Error>> {
//!     let db_url_key = Key::<String>::tagged(Tag::DatabaseUrl)?;
//!     let conn_limit_key = Key::<u32>::tagged(Tag::ConnectionLimit)?;
//!
//!     let injector = async_injector::setup();
//!     tokio::spawn(DatabaseProvider::run(injector.clone()));
//!
//!     let (mut database_stream, database) = injector.stream::<Database>().await;
//!
//!     // None of the dependencies are available, so it hasn't been constructed.
//!     assert!(database.is_none());
//!
//!     assert!(injector
//!         .update_key(&db_url_key, String::from("example.com"))
//!         .await
//!         .is_none());
//!
//!     assert!(injector.update_key(&conn_limit_key, 5).await.is_none());
//!
//!     let new_database = database_stream
//!         .next()
//!         .await
//!         .expect("unexpected end of stream");
//!
//!     // Database instance is available!
//!     assert_eq!(
//!         new_database,
//!         Some(Database {
//!             url: String::from("example.com"),
//!             connection_limit: 5
//!         })
//!     );
//!
//!     Ok(())
//! }
//! ```
//!
//! [cannot be hashed]: https://internals.rust-lang.org/t/f32-f64-should-implement-hash/5436
//! [Injector]: https://docs.rs/async-injector/0/async_injector/struct.Injector.html
//! [Key]: https://docs.rs/async-injector/0/async_injector/struct.Key.html
//! [Provider]: https://docs.rs/async-injector-derive/0/async_injector_derive/derive.Provider.html
//! [serde]: https://serde.rs
//! [Stream]: https://docs.rs/futures-core/0/futures_core/stream/trait.Stream.html

#![deny(missing_docs)]

use hashbrown::HashMap;
use serde_hashkey as hashkey;
use std::any::{Any, TypeId};
use std::cmp;
use std::error;
use std::fmt;
use std::future::Future;
use std::hash;
use std::marker;
use std::mem;
use std::pin::Pin;
use std::ptr;
use std::sync::Arc;
use std::task::{Context, Poll};
use tokio::sync::{broadcast, mpsc, RwLock, RwLockReadGuard, RwLockWriteGuard};

/// Internal type alias for the stream used to receive value updates.
type ValueStream = dyn ::tokio_stream::Stream<Item = Result<Option<Value>, broadcast::error::RecvError>>
    + Send
    + Sync;

/// re-exports for the Provider derive.
#[doc(hidden)]
pub mod derive {
    pub use tokio::select;
    pub use tokio_stream::StreamExt;
}

#[macro_use]
#[allow(unused_imports)]
extern crate async_injector_derive;
#[doc(hidden)]
pub use self::async_injector_derive::*;

/// Errors that can be raised by various functions in the [Injector].
#[derive(Debug)]
pub enum Error {
    /// Failed to perform work due to injector shutting down.
    Shutdown,
    /// Error raised when trying to setup a synchronized variable without any
    /// driver configured.
    NoDriver,
    /// Error when serializing key.
    SerializationError(hashkey::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Shutdown => "injector is shutting down".fmt(fmt),
            Self::NoDriver => "no driver configured".fmt(fmt),
            Self::SerializationError(..) => "serialization error".fmt(fmt),
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::SerializationError(e) => Some(e),
            _ => None,
        }
    }
}

impl From<hashkey::Error> for Error {
    fn from(value: hashkey::Error) -> Self {
        Error::SerializationError(value)
    }
}

/// Error raised when the driver channel ends in [Driver::drive]. This means
/// that there are no injectors available.
///
/// The typical way this is handled is through a panic when setting up the
/// driver:
///
/// ```rust
/// use std::error::Error;
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn Error>> {
///     let (injector, driver) = async_injector::setup_with_driver();
///
///     tokio::spawn(async move {
///         driver.drive().await.expect("injector driver failed");
///     });
///
///     // use `injector`.
///     Ok(())
/// }
/// ```
#[derive(Debug)]
pub struct EndOfDriverStream(());

impl fmt::Display for EndOfDriverStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "end of driver")
    }
}

impl error::Error for EndOfDriverStream {}

/// Construct an [Injector] without a [Driver].
///
/// This returns the root injector and *discards* the corresponding driver. The
/// driver is necessary in case any synchronized variables are used, like the
/// ones created with [Injector::var] *will not* update.
///
/// # Examples
///
/// ```rust
/// #[tokio::main]
/// async fn main() {
///     let injector = async_injector::setup();
///
///     assert_eq!(None, injector.get::<u32>().await);
///     injector.update(1u32).await;
///     assert_eq!(Some(1u32), injector.get::<u32>().await);
///     assert!(injector.clear::<u32>().await.is_some());
///     assert_eq!(None, injector.get::<u32>().await);
/// }
/// ```
///
/// Trying to use a synchronized [Var] with an injector that does not have a
/// driver will fail with an error:
///
/// ```rust
/// use tokio_stream::StreamExt as _;
/// use std::error::Error;
///
/// #[derive(Clone)]
/// struct Database;
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn Error>> {
///     let injector = async_injector::setup();
///     assert!(injector.var::<Database>().await.is_err());
///     Ok(())
/// }
/// ```
pub fn setup() -> Injector {
    Injector {
        inner: Arc::new(Inner {
            storage: Default::default(),
            tx: None,
        }),
    }
}

/// Construct an [Injector] with a [Driver].
///
/// This returns the root injector and the corresponding driver. The driver is
/// necessary in case any synchronized variables are used, like the ones created
/// with [Injector::var].
///
/// # Examples
///
/// ```rust
/// use tokio_stream::StreamExt as _;
/// use std::error::Error;
///
/// #[derive(Clone)]
/// struct Database;
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn Error>> {
///     let (injector, driver) = async_injector::setup_with_driver();
///
///     // Drive variable updates.
///     tokio::spawn(async move {
///         driver.drive().await.expect("injector driver failed");
///     });
///
///     let database = injector.var::<Database>().await?;
///
///     assert!(database.read().await.is_none());
///     injector.update(Database).await;
///
///     /// Variable updated in the background by the driver.
///     while database.read().await.is_none() {
///     }
///
///     assert!(database.read().await.is_some());
///     Ok(())
/// }
/// ```
pub fn setup_with_driver() -> (Injector, Driver) {
    let (tx, rx) = mpsc::unbounded_channel();

    let injector = Injector {
        inner: Arc::new(Inner {
            storage: Default::default(),
            tx: Some(tx),
        }),
    };

    let driver = Driver { rx };
    (injector, driver)
}

/// A stream of updates to a value in the [Injector].
///
/// This is created using [Injector::stream] or [Injector::stream_key] and can
/// be used to make sure that an asynchronous process has access to the most
/// up-to-date value from the injector.
pub struct Stream<T> {
    rx: Pin<Box<ValueStream>>,
    marker: marker::PhantomData<T>,
}

impl<T> Unpin for Stream<T> {}

impl<T> tokio_stream::Stream for Stream<T> {
    type Item = Option<T>;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
        let value = loop {
            let value = match self.rx.as_mut().poll_next(cx) {
                Poll::Ready(value) => value,
                Poll::Pending => return Poll::Pending,
            };

            let value = match value {
                Some(value) => value,
                _ => return Poll::Ready(None),
            };

            match value {
                Ok(value) => break value,
                // NB: need to poll again.
                Err(broadcast::error::RecvError::Lagged { .. }) => continue,
                _ => return Poll::Ready(None),
            };
        };

        let value = match value {
            Some(value) => value,
            _ => return Poll::Ready(Some(None)),
        };

        // Safety: The expected type parameter is encoded and maintained in the
        // Stream<T> type.
        Poll::Ready(Some(Some(unsafe { value.downcast::<T>() })))
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
    value: Option<Value>,
    tx: broadcast::Sender<Option<Value>>,
}

impl Default for Storage {
    fn default() -> Self {
        let (tx, _) = broadcast::channel(1);
        Self { value: None, tx }
    }
}

struct Inner {
    storage: RwLock<HashMap<RawKey, Storage>>,
    /// Channel where new drivers are sent.
    tx: Option<mpsc::UnboundedSender<TaskDriver>>,
}

/// An injector of dependencies.
///
/// Injectors are defined in hierarchies where an injector is either the root
/// injector as created using [setup] or [setup_with_driver], or the child of
/// another injector through [Injector::child].
///
/// Child injectors receive all the updates of their ancestors.
#[derive(Clone)]
pub struct Injector {
    inner: Arc<Inner>,
}

impl Injector {
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
    /// ```rust
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = async_injector::setup();
    ///
    ///     assert_eq!(None, injector.get::<u32>().await);
    ///     injector.update(1u32).await;
    ///     assert_eq!(Some(1u32), injector.get::<u32>().await);
    ///     assert!(injector.clear::<u32>().await.is_some());
    ///     assert_eq!(None, injector.get::<u32>().await);
    /// }
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
    /// ```rust
    /// use async_injector::{Key, Injector};
    /// use std::error::Error;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = async_injector::setup();
    ///     let k = Key::<u32>::tagged("foo")?;
    ///
    ///     assert_eq!(None, injector.get_key(&k).await);
    ///     injector.update_key(&k, 1u32).await;
    ///     assert_eq!(Some(1u32), injector.get_key(&k).await);
    ///     assert!(injector.clear_key(&k).await.is_some());
    ///     assert_eq!(None, injector.get_key(&k).await);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub async fn clear_key<T>(&self, key: impl AsRef<Key<T>>) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();

        let mut storage = self.inner.storage.write().await;
        let storage = storage.get_mut(key)?;
        let value = storage.value.take()?;
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
    /// ```rust
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = async_injector::setup();
    ///
    ///     assert_eq!(None, injector.get::<u32>().await);
    ///     injector.update(1u32).await;
    ///     assert_eq!(Some(1u32), injector.get::<u32>().await);
    /// }
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
    /// ```rust
    /// use async_injector::{Key, Injector};
    /// use std::error::Error;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = async_injector::setup();
    ///     let k = Key::<u32>::tagged("foo")?;
    ///
    ///     assert_eq!(None, injector.get_key(&k).await);
    ///     injector.update_key(&k, 1u32).await;
    ///     assert_eq!(Some(1u32), injector.get_key(&k).await);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub async fn update_key<T>(&self, key: impl AsRef<Key<T>>, value: T) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();
        let value = Value::new(T::from(value));

        let mut storage = self.inner.storage.write().await;
        let storage = storage.entry(key.clone()).or_default();
        let _ = storage.tx.send(Some(value.clone()));
        let old = storage.value.replace(value)?;
        Some(unsafe { old.downcast() })
    }

    /// Test if a given value exists by type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = async_injector::setup();
    ///
    ///     assert_eq!(false, injector.exists::<u32>().await);
    ///     injector.update(1u32).await;
    ///     assert_eq!(true, injector.exists::<u32>().await);
    /// }
    /// ```
    pub async fn exists<T>(&self) -> bool
    where
        T: Clone + Any + Send + Sync,
    {
        self.exists_key(&Key::<T>::of()).await
    }

    /// Test if a given value exists by key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::{Key, Injector};
    /// use std::error::Error;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = async_injector::setup();
    ///     let k = Key::<u32>::tagged("foo")?;
    ///
    ///     assert_eq!(false, injector.exists_key(&k).await);
    ///     injector.update_key(&k, 1u32).await;
    ///     assert_eq!(true, injector.exists_key(&k).await);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub async fn exists_key<T>(&self, key: impl AsRef<Key<T>>) -> bool
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();
        let storage = self.inner.storage.read().await;
        storage
            .get(key)
            .map(|s| s.value.is_some())
            .unwrap_or_default()
    }

    /// Mutate the given value by type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = async_injector::setup();
    ///
    ///     injector.update(1u32).await;
    ///
    ///     let old = injector.mutate(|value: &mut u32| {
    ///         let old = *value;
    ///         *value += 1;
    ///         old
    ///     }).await;
    ///
    ///     assert_eq!(Some(1u32), old);
    /// }
    /// ```
    pub async fn mutate<T, M, R>(&self, mutator: M) -> Option<R>
    where
        T: Clone + Any + Send + Sync,
        M: FnMut(&mut T) -> R,
    {
        self.mutate_key(&Key::<T>::of(), mutator).await
    }

    /// Mutate the given value by key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::{Key, Injector};
    /// use std::error::Error;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = async_injector::setup();
    ///     let k = Key::<u32>::tagged("foo")?;
    ///
    ///     injector.update_key(&k, 1u32).await;
    ///
    ///     let old = injector.mutate_key(&k, |value| {
    ///         let old = *value;
    ///         *value += 1;
    ///         old
    ///     }).await;
    ///
    ///     assert_eq!(Some(1u32), old);
    ///     Ok(())
    /// }
    /// ```
    pub async fn mutate_key<T, M, R>(&self, key: impl AsRef<Key<T>>, mut mutator: M) -> Option<R>
    where
        T: Clone + Any + Send + Sync,
        M: FnMut(&mut T) -> R,
    {
        let key = key.as_ref().as_raw_key();
        let mut storage = self.inner.storage.write().await;

        if let Some(storage) = storage.get_mut(key) {
            if let Some(value) = &mut storage.value {
                let output = mutator(unsafe { value.downcast_mut() });
                let value = value.clone();
                let _ = storage.tx.send(Some(value));
                return Some(output);
            }
        }

        None
    }

    /// Get a value from the injector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = async_injector::setup();
    ///
    ///     assert_eq!(None, injector.get::<u32>().await);
    ///     injector.update(1u32).await;
    ///     assert_eq!(Some(1u32), injector.get::<u32>().await);
    /// }
    /// ```
    pub async fn get<T>(&self) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        self.get_key(&Key::<T>::of()).await
    }

    /// Get a value from the injector with the given key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::{Injector, Key};
    /// use std::error::Error;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let k1 = Key::<u32>::tagged("foo")?;
    ///     let k2 = Key::<u32>::tagged("bar")?;
    ///
    ///     let injector = async_injector::setup();
    ///
    ///     assert_eq!(None, injector.get_key(&k1).await);
    ///     assert_eq!(None, injector.get_key(&k2).await);
    ///
    ///     injector.update_key(&k1, 1u32).await;
    ///
    ///     assert_eq!(Some(1u32), injector.get_key(&k1).await);
    ///     assert_eq!(None, injector.get_key(&k2).await);
    ///
    ///     Ok(())
    /// }
    /// ```
    pub async fn get_key<T>(&self, key: impl AsRef<Key<T>>) -> Option<T>
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();
        let storage = self.inner.storage.read().await;

        if let Some(value) = storage.get(key).and_then(|s| s.value.as_ref()) {
            // Safety: The expected type parameter is encoded and
            // maintained in the Stream type.
            return Some(unsafe { value.downcast_ref::<T>().clone() });
        }

        None
    }

    /// Get an existing value and setup a stream for updates at the same time.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokio_stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = async_injector::setup();
    ///     let (mut database_stream, mut database) = injector.stream::<Database>().await;
    ///
    ///     // Update the key somewhere else.
    ///     tokio::spawn({
    ///         let injector = injector.clone();
    ///
    ///         async move {
    ///             injector.update(Database).await;
    ///         }
    ///     });
    ///
    ///     loop {
    ///         tokio::select! {
    ///             Some(update) = database_stream.next() => {
    ///                 database = update;
    ///                 break;
    ///             }
    ///         }
    ///     }
    /// }
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
    /// ```rust
    /// use async_injector::{Injector, Key};
    /// use tokio_stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = async_injector::setup();
    ///     let db = Key::<Database>::tagged("foo")?;
    ///     let (mut database_stream, mut database) = injector.stream_key(&db).await;
    ///
    ///     // Update the key somewhere else.
    ///     tokio::spawn({
    ///         let db = db.clone();
    ///         let injector = injector.clone();
    ///
    ///         async move {
    ///             injector.update_key(&db, Database).await;
    ///         }
    ///     });
    ///
    ///     loop {
    ///         tokio::select! {
    ///             Some(update) = database_stream.next() => {
    ///                 database = update;
    ///                 break;
    ///             }
    ///         }
    ///     }
    ///
    ///     Ok(())
    /// }
    /// ```
    pub async fn stream_key<T>(&self, key: impl AsRef<Key<T>>) -> (Stream<T>, Option<T>)
    where
        T: Clone + Any + Send + Sync,
    {
        let key = key.as_ref().as_raw_key();

        let mut value = None;

        let mut storage = self.inner.storage.write().await;
        let storage = storage.entry(key.clone()).or_default();

        let rx = storage.tx.subscribe();
        let rx = Box::pin(into_stream(rx));

        value = value.or_else(|| match &storage.value {
            Some(value) => {
                // Safety: The expected type parameter is encoded and
                // maintained in the Stream type.
                Some(unsafe { value.downcast_ref::<T>().clone() })
            }
            None => None,
        });

        let stream = Stream {
            rx,
            marker: marker::PhantomData,
        };

        return (stream, value);

        fn into_stream(
            mut rx: broadcast::Receiver<Option<Value>>,
        ) -> impl ::tokio_stream::Stream<Item = Result<Option<Value>, broadcast::error::RecvError>>
        {
            async_stream::stream! {
                loop {
                    yield rx.recv().await;
                }
            }
        }
    }

    /// Get a synchronized variable for the given configuration key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokio_stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let (injector, driver) = async_injector::setup_with_driver();
    ///
    ///     // Drive variable updates.
    ///     tokio::spawn(async move {
    ///         driver.drive().await.expect("injector driver failed");
    ///     });
    ///
    ///     let database = injector.var::<Database>().await?;
    ///
    ///     assert!(database.read().await.is_none());
    ///     injector.update(Database).await;
    ///
    ///     /// Variable updated in the background by the driver.
    ///     while database.read().await.is_none() {
    ///     }
    ///
    ///     assert!(database.read().await.is_some());
    ///     Ok(())
    /// }
    /// ```
    pub async fn var<T>(&self) -> Result<Var<Option<T>>, Error>
    where
        T: Clone + Any + Send + Sync + Unpin,
    {
        self.var_key(&Key::<T>::of()).await
    }

    /// Get a synchronized variable for the given configuration key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::{Injector, Key};
    /// use tokio_stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let (injector, driver) = async_injector::setup_with_driver();
    ///     let db = Key::<Database>::tagged("foo")?;
    ///
    ///     // Drive variable updates.
    ///     tokio::spawn(async move {
    ///         driver.drive().await.expect("injector driver failed");
    ///     });
    ///
    ///     let database = injector.var_key(&db).await?;
    ///
    ///     assert!(database.read().await.is_none());
    ///     injector.update_key(&db, Database).await;
    ///
    ///     /// Variable updated in the background by the driver.
    ///     while database.read().await.is_none() {
    ///     }
    ///
    ///     assert!(database.read().await.is_some());
    ///     Ok(())
    /// }
    /// ```
    pub async fn var_key<T>(&self, key: impl AsRef<Key<T>>) -> Result<Var<Option<T>>, Error>
    where
        T: Clone + Any + Send + Sync + Unpin,
    {
        use tokio_stream::StreamExt as _;

        let tx = match &self.inner.tx {
            None => return Err(Error::NoDriver),
            Some(tx) => tx,
        };

        let (mut stream, value) = self.stream_key(key).await;

        let value = Var::new(value);
        let future_value = value.clone();

        let result = tx.send(TaskDriver(Box::pin(async move {
            while let Some(update) = stream.next().await {
                *future_value.write().await = update;
            }
        })));

        if result.is_err() {
            // NB: normally happens when the injector is shutting down.
            return Err(Error::Shutdown);
        }

        Ok(value)
    }
}

/// The driver of the injector system.
///
/// The driver is necessary in case any synchronized variables are used, like
/// the ones created with [Injector::var]. If a driver is not present and
/// *running*, synchronized variables will not be updated.
///
/// This should be driven using the [drive][Driver::drive] function.
///
/// # Examples
///
/// ```rust
/// use tokio_stream::StreamExt as _;
/// use std::error::Error;
///
/// #[derive(Clone)]
/// struct Database;
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn Error>> {
///     let (injector, driver) = async_injector::setup_with_driver();
///
///     // Drive variable updates.
///     tokio::spawn(async move {
///         driver.drive().await.expect("injector driver failed");
///     });
///
///     let database = injector.var::<Database>().await?;
///
///     assert!(database.read().await.is_none());
///     injector.update(Database).await;
///
///     /// Variable updated in the background by the driver.
///     while database.read().await.is_none() {
///     }
///
///     assert!(database.read().await.is_some());
///     Ok(())
/// }
/// ```
pub struct Driver {
    /// Receiver for drivers. Used by the run function.
    rx: mpsc::UnboundedReceiver<TaskDriver>,
}

impl Driver {
    /// Run the injector as a future, making sure all asynchronous processes
    /// associated with it are driven to completion.
    ///
    /// This has to be called for the injector to perform important tasks.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokio_stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let (injector, driver) = async_injector::setup_with_driver();
    ///
    ///     // Drive variable updates.
    ///     tokio::spawn(async move {
    ///         driver.drive().await.expect("injector driver failed");
    ///     });
    ///
    ///     let database = injector.var::<Database>().await?;
    ///
    ///     assert!(database.read().await.is_none());
    ///     injector.update(Database).await;
    ///
    ///     /// Variable updated in the background by the driver.
    ///     while database.read().await.is_none() {
    ///     }
    ///
    ///     assert!(database.read().await.is_some());
    ///     Ok(())
    /// }
    /// ```
    pub async fn drive(self) -> Result<(), EndOfDriverStream> {
        use tokio_stream::StreamExt as _;

        let mut rx = self.rx;
        let mut drivers = ::futures_util::stream::FuturesUnordered::new();

        loop {
            while drivers.is_empty() {
                drivers.push(rx.recv().await.ok_or(EndOfDriverStream(()))?);
            }

            while !drivers.is_empty() {
                tokio::select! {
                    driver = rx.recv() => drivers.push(driver.ok_or(EndOfDriverStream(()))?),
                    _ = drivers.next() => (),
                }
            }
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

/// A key used to discriminate a value in the [Injector].
#[derive(Clone)]
pub struct Key<T>
where
    T: Any,
{
    raw_key: RawKey,
    _marker: std::marker::PhantomData<T>,
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
    /// ```rust
    /// use async_injector::Key;
    ///
    /// struct Foo;
    ///
    /// assert_eq!(Key::<Foo>::of(), Key::<Foo>::of());
    /// ```
    pub fn of() -> Self {
        Self {
            raw_key: RawKey::new::<T, ()>(hashkey::Key::Unit),
            _marker: std::marker::PhantomData,
        }
    }

    /// Construct a new key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use serde::Serialize;
    /// use async_injector::Key;
    /// use std::error::Error;
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
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// assert_eq!(Key::<Foo>::tagged(Tag::One)?, Key::<Foo>::tagged(Tag::One)?);
    /// assert_ne!(Key::<Foo>::tagged(Tag::One)?, Key::<Foo>::tagged(Tag::Two)?);
    /// assert_ne!(Key::<Foo>::tagged(Tag::One)?, Key::<Foo>::tagged(Tag2::One)?);
    /// # Ok(())
    /// # }
    /// ```
    pub fn tagged<K>(tag: K) -> Result<Self, Error>
    where
        K: Any + serde::Serialize,
    {
        let tag = hashkey::to_key(&tag)?;

        Ok(Self {
            raw_key: RawKey::new::<T, K>(tag),
            _marker: std::marker::PhantomData,
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

/// The future that drives a synchronized variable.
struct TaskDriver(Pin<Box<dyn Future<Output = ()> + Send + Sync + 'static>>);

impl Future for TaskDriver {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.0.as_mut().poll(cx)
    }
}

/// A variable synchronized to a value in the [Injector].
///
/// This can be created through [Injector::var] or [Injector::var_key], and will
/// be kept in sync with the value inside of the injector by the [Driver].
///
/// Writing to this variable has *no effect* on the value inside of the
/// injector. But if you're lazy, you can use this as a shorthand for an async
/// `Arc<RwLock<T>>` type.
#[derive(Debug)]
pub struct Var<T> {
    storage: Arc<RwLock<T>>,
}

impl<T> Clone for Var<T> {
    fn clone(&self) -> Self {
        Self {
            storage: self.storage.clone(),
        }
    }
}

impl<T> Var<T> {
    /// Construct a new variable holder.
    pub fn new(value: T) -> Self {
        Self {
            storage: Arc::new(RwLock::new(value)),
        }
    }
}

impl<T> Var<T>
where
    T: Clone,
{
    /// Load the given variable, cloning the underlying value while doing so.
    pub async fn load(&self) -> T {
        self.storage.read().await.clone()
    }
}

impl<T> Var<T> {
    /// Read referentially from the underlying variable.
    pub async fn read(&self) -> RwLockReadGuard<'_, T> {
        self.storage.read().await
    }

    /// Write to the underlying variable.
    pub async fn write(&self) -> RwLockWriteGuard<'_, T> {
        self.storage.write().await
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
