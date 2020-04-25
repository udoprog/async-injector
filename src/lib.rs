//! Asynchronous dependency injection for Rust.
//!
//! ## Example
//!
//! The following is an example application that receives configuration changes
//! over HTTP.
//!
//! ```rust,compile_fail
//! use anyhow::Error;
//! use async_injector::{Provider, Injector, Key, async_trait};
//!
//! /// Provider that describes how to construct a database.
//! #[derive(Provider)]
//! struct DatabaseProvider {
//!     #[dependency(tag = "\"database/url\"")]
//!     url: String,
//!     #[dependency(tag = "\"database/connection-limit\"")]
//!     connection_limit: u32,
//! }
//!
//! #[async_trait]
//! impl Provider for DatabaseProvider {
//!     type Output = Database;
//!
//!     /// Constructor a new database and supply it to the injector.
//!     async fn build(self) -> Option<Self::Output> {
//!         match Database::connect(&self.url, self.connection_limit).await {
//!             Ok(database) => Some(database),
//!             Err(e) => {
//!                 log::warn!("failed to connect to database: {}: {}", self.url, e);
//!                 None
//!             }
//!         }
//!     }
//! }
//!
//! /// A fake webserver handler.
//! ///
//! /// Note: there's no real HTTP framework that looks like this. This is just an
//! /// example.
//! async fn serve(injector: &Injector) -> Result<(), Error> {
//!     let server = Server::new()?;
//!
//!     // Fake endpoint to set the database URL.
//!     server.on("POST", "/config/database/url", |url: String| {
//!         injector.update_key(Key::tagged("database/url")?, url);
//!     });
//!
//!     // Fake endpoint to set the database connection limit.
//!     server.on("POST", "/config/database/connection-limit", |limit: u32| {
//!         injector.update_key(Key::tagged("database/connection-limit")?, limit);
//!     });
//!
//!     // Listen for requests.
//!     server.await?;
//!     Ok(())
//! }
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Error> {
//!     let injector0 = Injector::new();
//!
//!     /// Setup database provider.
//!     let injector = injector0.clone();
//!
//!     tokio::spawn(async move {
//!         DatabaseProvider::run(&injector0).await;
//!     });
//!
//!     let injector = injector0.clone();
//!
//!     tokio::spawn(async move {
//!         serve(&injector).await.expect("web server errored");
//!     });
//!
//!     let (database_stream, database) = injector0.stream::<Database>();
//!
//!     let application = Application::new(database);
//!
//!     loop {
//!         tokio::select! {
//!             // receive new databases when available.
//!             database = database_stream.next() => {
//!                 application.database = database;
//!             },
//!             // run the application to completion.
//!             _ = &mut application => {
//!                 log::info!("application finished");
//!             },
//!         }
//!     }
//! }
//! ```

use futures_util::{
    future::{select, Either},
    ready,
    stream::{self, StreamExt as _},
};
use hashbrown::HashMap;
use serde_hashkey as hashkey;
use std::{
    any::{Any, TypeId},
    error, fmt,
    future::Future,
    marker,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
};
use tokio::sync::{mpsc, Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard};

#[macro_use]
#[allow(unused_imports)]
extern crate async_injector_derive;
#[doc(hidden)]
pub use self::async_injector_derive::*;
pub use async_trait::async_trait;

#[async_trait]
pub trait Provider
where
    Self: Sized,
{
    type Output;

    /// What to do when you want to clear the value.
    async fn clear() -> Option<Self::Output> {
        None
    }

    /// What to do when we construct a value.
    async fn build(self) -> Option<Self::Output> {
        None
    }
}

#[derive(Debug)]
pub enum Error {
    /// Failed to perform work due to injector shutting down.
    Shutdown,
    /// Unexpected end of driver stream.
    EndOfDriverStream,
    /// Driver already configured.
    DriverAlreadyConfigured,
    /// Error when serializing key.
    SerializationError(serde_hashkey::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Error::Shutdown => "injector is shutting down".fmt(fmt),
            Error::EndOfDriverStream => "end of driver stream".fmt(fmt),
            Error::DriverAlreadyConfigured => "driver already configured".fmt(fmt),
            Error::SerializationError(..) => "serialization error".fmt(fmt),
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Error::SerializationError(e) => Some(e),
            _ => None,
        }
    }
}

impl From<serde_hashkey::Error> for Error {
    fn from(value: serde_hashkey::Error) -> Self {
        Error::SerializationError(value)
    }
}

/// Use for sending information on updates.
struct Sender {
    tx: mpsc::UnboundedSender<Option<Box<dyn Any + Send + Sync + 'static>>>,
}

/// A stream of updates for values injected into this injector.
pub struct Stream<T> {
    rx: stream::SelectAll<mpsc::UnboundedReceiver<Option<Box<dyn Any + Send + Sync + 'static>>>>,
    marker: marker::PhantomData<T>,
}

impl<T> stream::Stream for Stream<T>
where
    T: Unpin + Any + Send + Sync + 'static,
{
    type Item = Option<T>;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
        let value = match ready!(Pin::new(&mut self.rx).poll_next(cx)) {
            Some(Some(value)) => value,
            Some(None) => return Poll::Ready(Some(None)),
            None => return Poll::Ready(None),
        };

        if let Ok(value) = (value as Box<dyn Any + 'static>).downcast::<T>() {
            return Poll::Ready(Some(Some(*value)));
        }

        panic!("downcast failed");
    }
}

impl<T> stream::FusedStream for Stream<T>
where
    T: Unpin + Any + Send + Sync + 'static,
{
    fn is_terminated(&self) -> bool {
        false
    }
}

#[derive(Default)]
struct Storage {
    value: Option<Box<dyn Any + Send + Sync + 'static>>,
    subs: Vec<Sender>,
}

impl Storage {
    /// Try to perform a send, or clean up if one fails.
    async fn try_send<S>(&mut self, send: S)
    where
        S: Fn() -> Option<Box<dyn Any + Send + Sync + 'static>>,
    {
        // Local collection of disconnected subscriptions to delete.
        let mut to_delete = smallvec::SmallVec::<[usize; 16]>::new();

        for (idx, s) in self.subs.iter().enumerate() {
            if s.tx.clone().send(send()).is_err() {
                to_delete.push(idx);
            }
        }

        if to_delete.is_empty() {
            return;
        }

        // The method we use to delete subscriptions works by swapping the given
        // element to remove with the last element in the collection, then
        // dropping and truncating it. This means we _have_ to delete elements
        // in a reverse order.
        for idx in to_delete.into_iter().rev() {
            let _ = self.subs.swap_remove(idx);
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
    /// When a child injector is dropped, all associated listeners are cleaned up as well.
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

    /// Clear the given value.
    pub async fn clear<T>(&self)
    where
        T: Clone + Any + Send + Sync + 'static,
    {
        self.clear_key(Key::<T>::of()).await
    }

    /// Clear the given value.
    pub async fn clear_key<T>(&self, key: impl AsRef<Key<T>>)
    where
        T: Clone + Any + Send + Sync + 'static,
    {
        let key = key.as_ref().as_raw_key();

        let mut storage = self.inner.storage.write().await;

        let storage = match storage.get_mut(&key) {
            Some(storage) => storage,
            None => return,
        };

        if storage.value.take().is_none() {
            return;
        }

        storage.try_send(|| None).await;
    }

    /// Set the given value and notify any subscribers.
    pub async fn update<T>(&self, value: T)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        self.update_key(Key::<T>::of(), value).await
    }

    /// Set the given value and notify any subscribers.
    pub async fn update_key<T>(&self, key: impl AsRef<Key<T>>, value: T)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let key = key.as_ref().as_raw_key();
        let mut storage = self.inner.storage.write().await;
        let storage = storage.entry(key).or_default();
        storage.try_send(|| Some(Box::new(value.clone()))).await;
        storage.value = Some(Box::new(value));
    }

    /// Get a value from the injector.
    pub async fn get<T>(&self) -> Option<T>
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        self.get_key(&Key::<T>::of()).await
    }

    /// Get a value from the injector with the given key.
    pub async fn get_key<T>(&self, key: impl AsRef<Key<T>>) -> Option<T>
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let key = key.as_ref().as_raw_key();

        let mut current = Some(self);

        while let Some(c) = current.take() {
            let storage = c.inner.storage.read().await;

            if let Some(storage) = storage.get(&key) {
                if let Some(value) = storage.value.as_ref() {
                    return Some(value.downcast_ref::<T>().expect("downcast failed").clone());
                }
            }

            current = c.inner.parent.as_ref();
        }

        None
    }

    /// Get an existing value and setup a stream for updates at the same time.
    pub async fn stream<T>(&self) -> (Stream<T>, Option<T>)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        self.stream_key(&Key::<T>::of()).await
    }

    /// Get an existing value and setup a stream for updates at the same time.
    pub async fn stream_key<T>(&self, key: impl AsRef<Key<T>>) -> (Stream<T>, Option<T>)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let raw_key = key.as_ref().as_raw_key();

        let mut rxs = Vec::new();
        let mut value = None;

        let mut current = Some(self);

        while let Some(c) = current.take() {
            let (tx, rx) = mpsc::unbounded_channel();

            rxs.push(rx);

            let mut storage = c.inner.storage.write().await;
            let storage = storage.entry(raw_key.clone()).or_default();
            storage.subs.push(Sender { tx: tx.clone() });

            value = value.or_else(|| match storage.value.as_ref() {
                Some(value) => Some(value.downcast_ref::<T>().expect("downcast failed").clone()),
                None => None,
            });

            current = c.inner.parent.as_ref();
        }

        let stream = Stream {
            rx: stream::select_all(rxs),
            marker: marker::PhantomData,
        };

        (stream, value)
    }

    /// Get a synchronized variable for the given configuration key.
    pub async fn var<T>(&self) -> Result<Var<Option<T>>, Error>
    where
        T: Any + Send + Sync + 'static + Clone + Unpin,
    {
        self.var_key(&Key::<T>::of()).await
    }

    /// Get a synchronized variable for the given configuration key.
    pub async fn var_key<T>(&self, key: impl AsRef<Key<T>>) -> Result<Var<Option<T>>, Error>
    where
        T: Any + Send + Sync + 'static + Clone + Unpin,
    {
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
    pub async fn drive(self) -> Result<(), Error> {
        let mut rx = self
            .inner
            .drivers_rx
            .lock()
            .await
            .take()
            .ok_or(Error::DriverAlreadyConfigured)?;

        let mut drivers = stream::FuturesUnordered::new();

        loop {
            while drivers.is_empty() {
                drivers.push(rx.next().await.ok_or(Error::EndOfDriverStream)?);
            }

            while !drivers.is_empty() {
                let result = select(rx.next(), drivers.select_next_some()).await;

                if let Either::Left((driver, _)) = result {
                    drivers.push(driver.ok_or(Error::EndOfDriverStream)?);
                }
            }
        }
    }
}

/// Used to calculate the type-id of the empty key.
enum Empty {}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct RawKey {
    type_id: TypeId,
    tag_type_id: TypeId,
    tag: hashkey::Key,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Key<T>
where
    T: Any,
{
    type_id: TypeId,
    tag_type_id: TypeId,
    tag: hashkey::Key,
    marker: std::marker::PhantomData<T>,
}

impl<T> Key<T>
where
    T: Any,
{
    /// Construct a new key without a tag.
    pub fn of() -> Self {
        Self {
            type_id: TypeId::of::<T>(),
            tag_type_id: TypeId::of::<Empty>(),
            tag: hashkey::Key::Unit,
            marker: std::marker::PhantomData,
        }
    }

    /// Construct a new key.
    pub fn tagged<K>(tag: K) -> Result<Self, Error>
    where
        K: Any + serde::Serialize,
    {
        Ok(Self {
            type_id: TypeId::of::<T>(),
            tag_type_id: TypeId::of::<K>(),
            tag: hashkey::to_key(&tag)?,
            marker: std::marker::PhantomData,
        })
    }

    /// Convert into a raw key.
    fn as_raw_key(&self) -> RawKey {
        RawKey {
            type_id: self.type_id,
            tag_type_id: self.tag_type_id,
            tag: self.tag.clone(),
        }
    }
}

impl<T: 'static> AsRef<Key<T>> for Key<T> {
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
