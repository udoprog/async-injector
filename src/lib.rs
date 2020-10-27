//! [![Documentation](https://docs.rs/async-injector/badge.svg)](https://docs.rs/async-injector)
//! [![Crates](https://img.shields.io/crates/v/async-injector.svg)](https://crates.io/crates/async-injector)
//! [![Actions Status](https://github.com/udoprog/async-injector/workflows/Rust/badge.svg)](https://github.com/udoprog/async-injector/actions)
//!
//! Asynchronous reactive dependency injection for Rust.
//!
//! This crate provides a reactive dependency injection system that can
//! reconfigure your application dynamically from changes in dependencies.
//!
//! It allows for subscribing to changes in application configuration keys using
//! asynchronous streams, like this:
//!
//! ```rust
//! use async_injector::Injector;
//! use tokio::{stream::StreamExt as _, time};
//! use std::error::Error;
//!
//! #[derive(Clone)]
//! struct Database;
//!
//! #[tokio::main]
//! async fn main() {
//!     let injector = Injector::new();
//!     let (mut database_stream, mut database) = injector.stream::<Database>().await;
//!
//!     // Insert the database dependency in a different task in the background.
//!     tokio::spawn({
//!         let injector = injector.clone();
//!
//!         async move {
//!             time::sleep(time::Duration::from_secs(2));
//!             injector.update(Database).await;
//!         }
//!     });
//!
//!     assert!(database.is_none());
//!
//!     // Every update to the stored type will be streamed, allowing you to
//!     // react to it.
//!     if let Some(update) = database_stream.next().await {
//!         database = update;
//!     }
//!
//!     assert!(database.is_some());
//! }
//! ```
//!
//! With a bit of glue, this means that your application can be reconfigured
//! without restarting it. Providing a richer user experience.
//!
//! ## Example using `Key`
//!
//! The following showcases how the injector can be shared across threads, and
//! how you can distinguish between different keys of the same type (`u32`)
//! using a tag (`Tag`).
//!
//! The tag used must be serializable with [`serde`]. It must also not use any
//! components which [cannot be hashed], like `f32` and `f64` (this will cause
//! an error to be raised).
//!
//! [`serde`]: https://serde.rs
//! [cannot be hashed]: https://internals.rust-lang.org/t/f32-f64-should-implement-hash/5436
//!
//! ```rust,no_run
//! use async_injector::{Key, Injector};
//! use serde::Serialize;
//! use std::{error::Error, time::Duration};
//! use tokio::{stream::StreamExt as _, time};
//!
//! #[derive(Serialize)]
//! enum Tag {
//!     One,
//!     Two,
//! }
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn Error>> {
//!     let injector = Injector::new();
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
//! The following showcases how the [`Provider` derive] can be used to
//! automatically construct and inject dependencies.
//!
//! ```rust,no_run
//! use async_injector::{Injector, Key, Provider};
//! use serde::Serialize;
//! use tokio::stream::StreamExt as _;
//!
//! /// Fake database connection.
//! #[derive(Clone, Debug, PartialEq, Eq)]
//! struct Database {
//!     url: String,
//!     connection_limit: u32,
//! }
//!
//! impl Database {
//!     async fn build(provider: DatabaseProvider2) -> Option<Self> {
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
//! struct DatabaseProvider2 {
//!     #[dependency(tag = "Tag::DatabaseUrl")]
//!     url: String,
//!     #[dependency(tag = "Tag::ConnectionLimit")]
//!     connection_limit: u32,
//! }
//!
//! #[tokio::test]
//! async fn test_provider() -> Result<(), Box<dyn std::error::Error>> {
//!     let db_url_key = Key::<String>::tagged(Tag::DatabaseUrl)?;
//!     let conn_limit_key = Key::<u32>::tagged(Tag::ConnectionLimit)?;
//!
//!     let injector = Injector::new();
//!     tokio::spawn(DatabaseProvider2::run(injector.clone()));
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
//! [`Provider` derive]: https://docs.rs/async-injector-derive/0/async_injector_derive/derive.Provider.html

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
use tokio::sync::{broadcast, mpsc, Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard};

/// Internal type alias for the stream used to receive value updates.
type ValueStream = dyn ::futures_util::stream::Stream<Item = Result<Option<Value>, broadcast::error::RecvError>>
    + Send
    + Sync;

/// re-exports for the Provider derive.
#[doc(hidden)]
pub mod derive {
    pub use tokio::{select, stream::StreamExt};
}

#[macro_use]
#[allow(unused_imports)]
extern crate async_injector_derive;
#[doc(hidden)]
pub use self::async_injector_derive::*;

/// Errors that can be raised by various functions in the [`Injector`].
///
/// [`Injector`]: Injector
#[derive(Debug)]
pub enum Error {
    /// Failed to perform work due to injector shutting down.
    Shutdown,
    /// Unexpected end of driver stream.
    EndOfDriverStream,
    /// Driver already configured.
    DriverAlreadyConfigured,
    /// Error when serializing key.
    SerializationError(hashkey::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Shutdown => "injector is shutting down".fmt(fmt),
            Self::EndOfDriverStream => "end of driver stream".fmt(fmt),
            Self::DriverAlreadyConfigured => "driver already configured".fmt(fmt),
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

/// A stream of updates for values injected into this injector.
pub struct Stream<T> {
    rxs: ::futures_util::stream::SelectAll<Pin<Box<ValueStream>>>,
    marker: marker::PhantomData<T>,
}

impl<T> tokio::stream::Stream for Stream<T> {
    type Item = Option<T>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
        let mut rxs = unsafe { Pin::map_unchecked_mut(self, |s| &mut s.rxs) };

        let value = loop {
            let value = match rxs.as_mut().poll_next(cx) {
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

impl<T> ::futures_util::stream::FusedStream for Stream<T> {
    fn is_terminated(&self) -> bool {
        self.rxs.is_terminated()
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

struct Storage {
    value: Option<Value>,
    tx: broadcast::Sender<Option<Value>>,
    count: usize,
}

impl Default for Storage {
    fn default() -> Self {
        let (tx, _) = broadcast::channel(1);
        Self {
            value: None,
            tx,
            count: 0,
        }
    }
}

struct Inner {
    storage: RwLock<HashMap<RawKey, Storage>>,
    /// Channel where new drivers are sent.
    drivers: mpsc::UnboundedSender<Driver>,
    /// Receiver for drivers. Used by the run function.
    drivers_rx: Mutex<Option<mpsc::UnboundedReceiver<Driver>>>,
    /// Parent injector for the current injector.
    parent: Option<Injector>,
}

/// Use for handling injection.
#[derive(Clone)]
pub struct Injector {
    inner: Arc<Inner>,
}

impl Default for Injector {
    fn default() -> Self {
        Injector::new()
    }
}

impl Injector {
    /// Create a new injector instance.
    pub fn new() -> Self {
        let (drivers, drivers_rx) = mpsc::unbounded_channel();

        Self {
            inner: Arc::new(Inner {
                storage: Default::default(),
                drivers,
                drivers_rx: Mutex::new(Some(drivers_rx)),
                parent: None,
            }),
        }
    }

    /// Construct a new child injector.
    ///
    /// When a child injector is dropped, all associated listeners are cleaned
    /// up as well.
    pub fn child(&self) -> Injector {
        Self {
            inner: Arc::new(Inner {
                storage: Default::default(),
                drivers: self.inner.drivers.clone(),
                drivers_rx: Mutex::new(None),
                parent: Some(self.clone()),
            }),
        }
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
    /// ```rust
    /// use async_injector::Injector;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = Injector::new();
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
    ///     let injector = Injector::new();
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
    /// use async_injector::Injector;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = Injector::new();
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
    ///     let injector = Injector::new();
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
    /// use async_injector::Injector;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = Injector::new();
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
    ///     let injector = Injector::new();
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

        for c in self.chain() {
            let storage = c.inner.storage.read().await;

            if let Some(true) = storage.get(key).map(|s| s.value.is_some()) {
                return true;
            }
        }

        false
    }

    /// Mutate the given value by type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::Injector;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = Injector::new();
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
    ///     let injector = Injector::new();
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

        for c in self.chain() {
            let mut storage = c.inner.storage.write().await;

            if let Some(storage) = storage.get_mut(key) {
                if let Some(value) = &mut storage.value {
                    let output = mutator(unsafe { value.downcast_mut() });
                    let value = value.clone();
                    let _ = storage.tx.send(Some(value));
                    return Some(output);
                }
            }
        }

        None
    }

    /// Get a value from the injector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::Injector;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = Injector::new();
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
    ///     let injector = Injector::new();
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

        for c in self.chain() {
            let storage = c.inner.storage.read().await;

            if let Some(value) = storage.get(key).and_then(|s| s.value.as_ref()) {
                // Safety: The expected type parameter is encoded and
                // maintained in the Stream type.
                return Some(unsafe { value.downcast_ref::<T>().clone() });
            }
        }

        None
    }

    /// Get an existing value and setup a stream for updates at the same time.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::Injector;
    /// use tokio::stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let injector = Injector::new();
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
    /// use tokio::stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = Injector::new();
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

        let mut rxs = ::futures_util::stream::SelectAll::new();
        let mut value = None;

        for c in self.chain() {
            let mut storage = c.inner.storage.write().await;
            let storage = storage.entry(key.clone()).or_default();

            let rx = storage.tx.subscribe();
            storage.count += 1;
            rxs.push(Box::pin(rx.into_stream()) as Pin<Box<ValueStream>>);

            value = value.or_else(|| match &storage.value {
                Some(value) => {
                    // Safety: The expected type parameter is encoded and
                    // maintained in the Stream type.
                    Some(unsafe { value.downcast_ref::<T>().clone() })
                }
                None => None,
            });
        }

        let stream = Stream {
            rxs,
            marker: marker::PhantomData,
        };

        (stream, value)
    }

    /// Get a synchronized variable for the given configuration key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::Injector;
    /// use tokio::stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = Injector::new();
    ///
    ///     // Drive variable updates.
    ///     tokio::spawn({
    ///         let injector = injector.clone();
    ///
    ///         async move {
    ///             injector.drive().await.expect("injector driver failed");
    ///         }
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
    /// use tokio::stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = Injector::new();
    ///     let db = Key::<Database>::tagged("foo")?;
    ///
    ///     // Drive variable updates.
    ///     tokio::spawn({
    ///         let injector = injector.clone();
    ///
    ///         async move {
    ///             injector.drive().await.expect("injector driver failed");
    ///         }
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
        use tokio::stream::StreamExt as _;

        let (mut stream, value) = self.stream_key(key).await;
        let value = Var::new(value);
        let future_value = value.clone();

        let future = async move {
            while let Some(update) = stream.next().await {
                *future_value.write().await = update;
            }
        };

        let result = self.inner.drivers.clone().send(Driver {
            future: Box::pin(future),
        });

        if result.is_err() {
            // NB: normally happens when the injector is shutting down.
            return Err(Error::Shutdown);
        }

        Ok(value)
    }

    /// Run the injector as a future, making sure all asynchronous processes
    /// associated with it are driven to completion.
    ///
    /// This has to be called for the injector to perform important tasks.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::Injector;
    /// use tokio::stream::StreamExt as _;
    /// use std::error::Error;
    ///
    /// #[derive(Clone)]
    /// struct Database;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn Error>> {
    ///     let injector = Injector::new();
    ///
    ///     // Drive variable updates.
    ///     tokio::spawn({
    ///         let injector = injector.clone();
    ///
    ///         async move {
    ///             injector.drive().await.expect("injector driver failed");
    ///         }
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
    pub async fn drive(self) -> Result<(), Error> {
        use tokio::stream::StreamExt as _;

        let mut rx = self
            .inner
            .drivers_rx
            .lock()
            .await
            .take()
            .ok_or(Error::DriverAlreadyConfigured)?;

        let mut drivers = ::futures_util::stream::FuturesUnordered::new();

        loop {
            while drivers.is_empty() {
                drivers.push(rx.next().await.ok_or(Error::EndOfDriverStream)?);
            }

            while !drivers.is_empty() {
                tokio::select! {
                    driver = rx.next() => {
                        drivers.push(driver.ok_or(Error::EndOfDriverStream)?);
                    }
                    _ = drivers.next() => {
                    }
                }
            }
        }
    }

    /// Iterate through the chain of injectors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use async_injector::Injector;
    ///
    /// let injector = Injector::new();
    /// let child = injector.child();
    ///
    /// assert_eq!(1, injector.chain().count());
    /// assert_eq!(2, child.chain().count());
    /// ```
    pub fn chain(&self) -> Chain<'_> {
        Chain {
            injector: Some(self),
        }
    }
}

/// A chain of [`Injector`]s.
///
/// A chain is composed of a child injector and all of its parents. This is
/// created through [Injector::chain].
///
/// [`Injector`]: Injector
pub struct Chain<'a> {
    injector: Option<&'a Injector>,
}

impl<'a> Iterator for Chain<'a> {
    type Item = &'a Injector;

    fn next(&mut self) -> Option<Self::Item> {
        let injector = self.injector.take()?;
        self.injector = injector.inner.parent.as_ref();
        Some(injector)
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
///
/// [`Injector`]: Injector
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
struct Driver {
    future: Pin<Box<dyn Future<Output = ()> + Send + Sync + 'static>>,
}

impl Future for Driver {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.future.as_mut().poll(cx)
    }
}

/// Proxy accessor for an injected variable.
///
/// This stores a reference to the given variable and provides methods for
/// accessing it, similarly to an `RwLock`, but biased towards efficient
/// cloning.
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
