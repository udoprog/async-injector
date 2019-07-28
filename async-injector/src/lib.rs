#![feature(async_await)]
//! Asynchronous dependency injection for Rust.

use futures::{
    channel::mpsc,
    ready,
    stream::{self, StreamExt as _},
};
use hashbrown::{HashMap, HashSet};
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
    /// Unique id for this sender.
    id: u32,
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
    id: u32,
    storage: HashMap<TypeId, Box<dyn Any + Send + Sync + 'static>>,
    subs: HashMap<TypeId, Vec<Sender>>,
}

struct Inner {
    storage: RwLock<Storage>,
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
        let type_id = TypeId::of::<T>();

        let mut storage = self.inner.storage.write();

        if let None = storage.storage.remove(&type_id) {
            return;
        }

        self.try_send(&mut *storage, type_id, || None);
    }

    /// Set the given value and notify any subscribers.
    pub fn update<T>(&self, value: T)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let type_id = TypeId::of::<T>();
        let mut storage = self.inner.storage.write();
        self.try_send(&mut *storage, type_id, || Some(Box::new(value.clone())));
        storage.storage.insert(type_id, Box::new(value));
    }

    /// Get a value from the injector.
    pub fn get<T>(&self) -> Option<T>
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let type_id = TypeId::of::<T>();
        let storage = self.inner.storage.read();

        match storage.storage.get(&type_id) {
            Some(value) => match value.downcast_ref::<T>() {
                Some(value) => Some(value.clone()),
                None => panic!("downcast failed"),
            },
            None => None,
        }
    }

    /// Get an existing value and setup a stream for updates at the same time.
    pub fn stream<T>(&self) -> (Stream<T>, Option<T>)
    where
        T: Any + Send + Sync + 'static + Clone,
    {
        let type_id = TypeId::of::<T>();

        let mut storage = self.inner.storage.write();

        let value = match storage.storage.get(&type_id) {
            Some(value) => match value.downcast_ref::<T>() {
                Some(value) => Some(value.clone()),
                None => panic!("downcast failed"),
            },
            None => None,
        };

        let id = storage.id;
        storage.id += 1;
        let (tx, rx) = mpsc::unbounded();
        storage
            .subs
            .entry(type_id)
            .or_default()
            .push(Sender { id, tx });

        let stream = Stream {
            rx,
            marker: marker::PhantomData,
        };

        (stream, value)
    }

    /// Get a synchronized variable for the given configuration key.
    pub fn var<'a, T>(&self) -> Result<Arc<RwLock<Option<T>>>, Error>
    where
        T: Any + Send + Sync + 'static + Clone + Unpin,
    {
        use futures::StreamExt as _;

        let (mut stream, value) = self.stream();
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

    /// Try to perform a send, or clean up if one fails.
    fn try_send<S>(&self, storage: &mut Storage, type_id: TypeId, send: S)
    where
        S: Fn() -> Option<Box<dyn Any + Send + Sync + 'static>>,
    {
        // Local collection of disconnected subscriptions to delete.
        // TODO: handle this in driver instead.
        let mut to_delete = smallvec::SmallVec::<[u32; 16]>::new();

        if let Some(subs) = storage.subs.get(&type_id) {
            for s in subs {
                if let Err(e) = s.tx.unbounded_send(send()) {
                    if e.is_disconnected() {
                        to_delete.push(s.id);
                        continue;
                    }

                    log::warn!("failed to send resource update: {}", e);
                }
            }
        }

        if to_delete.is_empty() {
            return;
        }

        let to_delete = to_delete.into_iter().collect::<HashSet<_>>();

        if let Some(subs) = storage.subs.get_mut(&type_id) {
            let new_subs = subs
                .drain(..)
                .into_iter()
                .filter(|s| !to_delete.contains(&s.id))
                .collect();

            *subs = new_subs;
        }
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
