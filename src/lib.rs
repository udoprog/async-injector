#![feature(async_await)]
//! Asynchronous dependency injection for Rust.

use futures::{
    channel::mpsc,
    ready,
    stream::{self, StreamExt as _},
};
use hashbrown::HashMap;
use parking_lot::{Mutex, RwLock};
use std::{
    any::{Any, TypeId},
    error, fmt,
    future::Future,
    marker,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
};

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

#[derive(Debug, Clone, Copy)]
pub enum Error {
    /// Failed to perform work due to injector shutting down.
    Shutdown,
    /// Unexpected end of driver stream.
    EndOfDriverStream,
    /// Driver already configured.
    DriverAlreadyConfigured,
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Error::Shutdown => "injector is shutting down".fmt(fmt),
            Error::EndOfDriverStream => "end of driver stream".fmt(fmt),
            Error::DriverAlreadyConfigured => "driver already configured".fmt(fmt),
        }
    }
}

impl error::Error for Error {}

/// Use for sending information on updates.
struct Sender {
    tx: mpsc::UnboundedSender<Option<Box<dyn Any + Send + Sync + 'static>>>,
}

/// A stream of updates for values injected into this injector.
pub struct Stream<T> {
    rx: mpsc::UnboundedReceiver<Option<Box<dyn Any + Send + Sync + 'static>>>,
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

        match (value as Box<dyn Any + 'static>).downcast::<T>() {
            Ok(value) => Poll::Ready(Some(Some(*value))),
            Err(_) => panic!("downcast failed"),
        }
    }
}

impl<T> stream::FusedStream for Stream<T> {
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
    fn try_send<S>(&mut self, send: S)
    where
        S: Fn() -> Option<Box<dyn Any + Send + Sync + 'static>>,
    {
        // Local collection of disconnected subscriptions to delete.
        // TODO: handle this in driver instead.
        let mut to_delete = smallvec::SmallVec::<[usize; 16]>::new();

        for (idx, s) in self.subs.iter().enumerate() {
            if let Err(e) = s.tx.unbounded_send(send()) {
                if e.is_disconnected() {
                    to_delete.push(idx);
                    continue;
                }

                log::warn!("failed to send resource update: {}", e);
            }
        }

        if to_delete.is_empty() {
            return;
        }

        for (c, idx) in to_delete.into_iter().enumerate() {
            let _ = self.subs.swap_remove(idx.saturating_sub(c));
        }
    }
}

struct Inner {
    storage: RwLock<HashMap<RawKey, Storage>>,
    /// Channel where new drivers are sent.
    drivers: mpsc::UnboundedSender<Driver>,
    /// Receiver for drivers. Used by the run function.
    drivers_rx: Mutex<Option<mpsc::UnboundedReceiver<Driver>>>,
}

/// Use for handling injection.
#[derive(Clone)]
pub struct Injector {
    inner: Arc<Inner>,
}

impl Injector {
    /// Create a new injector instance.
    pub fn new() -> Self {
        let (drivers, drivers_rx) = mpsc::unbounded();

        Self {
            inner: Arc::new(Inner {
                storage: Default::default(),
                drivers,
                drivers_rx: Mutex::new(Some(drivers_rx)),
            }),
        }
    }

    /// Clear the given value.
    pub fn clear<T>(&self)
    where
        T: Clone + Any + Send + Sync + 'static,
    {
        self.clear_key::<T>(&Key::<T>::of())
    }

    /// Clear the given value.
    pub fn clear_key<T>(&self, key: &Key<T>)
    where
        T: Clone + Any + Send + Sync + 'static,
    {
        let key = key.as_raw_key();

        let mut storage = self.inner.storage.write();

        let storage = match storage.get_mut(&key) {
            Some(storage) => storage,
            None => return,
        };

        if let None = storage.value.take() {
            return;
        }

        storage.try_send(|| None);
    }

    /// Set the given value and notify any subscribers.
    pub fn update<T>(&self, value: T)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        self.update_key(&Key::<T>::of(), value)
    }

    /// Set the given value and notify any subscribers.
    pub fn update_key<T>(&self, key: &Key<T>, value: T)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let key = key.as_raw_key();
        let mut storage = self.inner.storage.write();
        let storage = storage.entry(key).or_default();
        storage.try_send(|| Some(Box::new(value.clone())));
        storage.value = Some(Box::new(value));
    }

    /// Get a value from the injector.
    pub fn get<T>(&self) -> Option<T>
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        self.get_key(&Key::<T>::of())
    }

    /// Get a value from the injector with the given key.
    pub fn get_key<T>(&self, key: &Key<T>) -> Option<T>
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let key = key.as_raw_key();

        let storage = self.inner.storage.read();
        let storage = storage.get(&key)?;
        let value = storage.value.as_ref()?;

        match value.downcast_ref::<T>() {
            Some(value) => Some(value.clone()),
            None => panic!("downcast failed"),
        }
    }

    /// Get an existing value and setup a stream for updates at the same time.
    pub fn stream<T>(&self) -> (Stream<T>, Option<T>)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        self.stream_key(&Key::<T>::of())
    }

    /// Get an existing value and setup a stream for updates at the same time.
    pub fn stream_key<T>(&self, key: &Key<T>) -> (Stream<T>, Option<T>)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let key = key.as_raw_key();

        let (tx, rx) = mpsc::unbounded();

        let value = {
            let mut storage = self.inner.storage.write();
            let storage = storage.entry(key).or_default();
            storage.subs.push(Sender { tx: tx.clone() });

            match storage.value.as_ref() {
                Some(value) => match value.downcast_ref::<T>() {
                    Some(value) => Some(value.clone()),
                    None => panic!("downcast failed"),
                },
                None => None,
            }
        };

        let stream = Stream {
            rx,
            marker: marker::PhantomData,
        };

        (stream, value)
    }

    /// Get a synchronized variable for the given configuration key.
    pub fn var<T>(&self) -> Result<Arc<RwLock<Option<T>>>, Error>
    where
        T: Any + Send + Sync + 'static + Clone + Unpin,
    {
        self.var_key(&Key::<T>::of())
    }

    /// Get a synchronized variable for the given configuration key.
    pub fn var_key<T>(&self, key: &Key<T>) -> Result<Arc<RwLock<Option<T>>>, Error>
    where
        T: Any + Send + Sync + 'static + Clone + Unpin,
    {
        use futures::StreamExt as _;

        let (mut stream, value) = self.stream_key(key);
        let value = Arc::new(RwLock::new(value));
        let future_value = value.clone();

        let future = async move {
            while let Some(update) = stream.next().await {
                *future_value.write() = update;
            }
        };

        let result = self.inner.drivers.unbounded_send(Driver {
            future: Box::pin(future),
        });

        if let Err(e) = result {
            // NB: normally happens when the injector is shutting down.
            if !e.is_disconnected() {
                return Err(Error::Shutdown);
            }
        }

        Ok(value)
    }

    /// Run the injector as a future, making sure all asynchronous processes
    /// associated with it are driven to completion.
    ///
    /// This has to be called for the injector to perform important tasks.
    pub async fn drive(self) -> Result<(), Error> {
        use futures::future;

        let mut rx = self
            .inner
            .drivers_rx
            .lock()
            .take()
            .ok_or(Error::DriverAlreadyConfigured)?;

        let mut drivers = Vec::new();

        'outer: loop {
            while drivers.is_empty() {
                drivers.push(rx.next().await.ok_or(Error::EndOfDriverStream)?);
            }

            while !drivers.is_empty() {
                let either = future::select(rx.next(), future::select_all(&mut drivers)).await;

                match either {
                    future::Either::Left((driver, _)) => {
                        let driver = driver.ok_or(Error::EndOfDriverStream)?;
                        drivers.push(driver);
                    }
                    future::Either::Right(((_, index, _), _)) => {
                        let _ = drivers.swap_remove(index);
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct RawKey {
    type_id: TypeId,
    tag: Option<String>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Key<T>
where
    T: Any,
{
    type_id: TypeId,
    tag: Option<String>,
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
            tag: None,
            marker: std::marker::PhantomData,
        }
    }

    /// Construct a new key.
    pub fn tagged(tag: &str) -> Self {
        Self {
            type_id: TypeId::of::<T>(),
            tag: Some(tag.to_owned()),
            marker: std::marker::PhantomData,
        }
    }

    /// Convert into a raw key.
    pub fn as_raw_key(&self) -> RawKey {
        RawKey {
            type_id: self.type_id,
            tag: self.tag.clone(),
        }
    }
}

/// The future that drives a synchronized variable.
struct Driver {
    future: Pin<Box<dyn Future<Output = ()> + Send + 'static>>,
}

impl Future for Driver {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.future.as_mut().poll(cx)
    }
}
