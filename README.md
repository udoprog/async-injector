# async-injector

[![Documentation](https://docs.rs/async-injector/badge.svg)](https://docs.rs/async-injector)
[![Crates](https://img.shields.io/crates/v/async-injector.svg)](https://crates.io/crates/async-injector)
[![Actions Status](https://github.com/udoprog/async-injector/workflows/Rust/badge.svg)](https://github.com/udoprog/async-injector/actions)

Asynchronous reactive dependency injection for Rust.

This crate provides a reactive dependency injection system that can
reconfigure your application dynamically from changes in dependencies.

It allows for subscribing to changes in application configuration keys using
asynchronous streams, like this:

```rust
use async_injector::Injector;
use tokio::{stream::StreamExt as _, time};
use std::error::Error;

#[derive(Clone)]
struct Database;

#[tokio::main]
async fn main() {
    let injector = Injector::new();
    let (mut database_stream, mut database) = injector.stream::<Database>().await;

    // Insert the database dependency in a different task in the background.
    tokio::spawn({
        let injector = injector.clone();

        async move {
            time::sleep(time::Duration::from_secs(2));
            injector.update(Database).await;
        }
    });

    assert!(database.is_none());

    // Every update to the stored type will be streamed, allowing you to
    // react to it.
    if let Some(update) = database_stream.next().await {
        database = update;
    }

    assert!(database.is_some());
}
```

With a bit of glue, this means that your application can be reconfigured
without restarting it. Providing a richer user experience.

### Example using `Key`

The following showcases how the injector can be shared across threads, and
how you can distinguish between different keys of the same type (`u32`)
using a tag (`Tag`).

The tag used must be serializable with [`serde`]. It must also not use any
components which [cannot be hashed], like `f32` and `f64` (this will cause
an error to be raised).

[`serde`]: https://serde.rs
[cannot be hashed]: https://internals.rust-lang.org/t/f32-f64-should-implement-hash/5436

```rust
use async_injector::{Key, Injector};
use serde::Serialize;
use std::{error::Error, time::Duration};
use tokio::{stream::StreamExt as _, time};

#[derive(Serialize)]
enum Tag {
    One,
    Two,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let injector = Injector::new();
    let one = Key::<u32>::tagged(Tag::One)?;
    let two = Key::<u32>::tagged(Tag::Two)?;

    tokio::spawn({
        let injector = injector.clone();
        let one = one.clone();

        async move {
            let mut interval = time::interval(Duration::from_secs(1));

            for i in 0u32.. {
                interval.tick().await;
                injector.update_key(&one, i).await;
            }
        }
    });

    tokio::spawn({
        let injector = injector.clone();
        let two = two.clone();

        async move {
            let mut interval = time::interval(Duration::from_secs(1));

            for i in 0u32.. {
                interval.tick().await;
                injector.update_key(&two, i * 2).await;
            }
        }
    });

    let (mut one_stream, mut one) = injector.stream_key(one).await;
    let (mut two_stream, mut two) = injector.stream_key(two).await;

    println!("one: {:?}", one);
    println!("two: {:?}", two);

    loop {
        tokio::select! {
            Some(update) = one_stream.next() => {
                one = update;
                println!("one: {:?}", one);
            }
            Some(update) = two_stream.next() => {
                two = update;
                println!("two: {:?}", two);
            }
        }
    }
}
```

## Example using Provider

The following is an example application that receives configuration changes
over HTTP.

```rust,compile_fail
use anyhow::Error;
use async_injector::{Provider, Injector, Key, async_trait};
use serde::Serialize;

#[derive(Serialize)]
pub enum Tag {
   DatabaseUrl,
   ConnectionLimit,
}

/// Provider that describes how to construct a database.
#[derive(Provider)]
#[provider(build = "DatabaseProvider::build", output = "Database")]
struct DatabaseProvider {
    #[dependency(tag = "Tag::DatabaseUrl")]
    url: String,
    #[dependency(tag = "Tag::DatabaseUrl")]
    connection_limit: u32,
}

impl DatabaseProvider {
    /// Constructor a new database and supply it to the injector.
    async fn build(self) -> Option<Database> {
        match Database::connect(&self.url, self.connection_limit).await {
            Ok(database) => Some(database),
            Err(e) => {
                log::warn!("failed to connect to database: {}: {}", self.url, e);
                None
            }
        }
    }
}

/// A fake webserver handler.
///
/// Note: there's no real HTTP framework that looks like this. This is just an
/// example.
async fn serve(injector: &Injector) -> Result<(), Error> {
    let server = Server::new()?;

    // Fake endpoint to set the database URL.
    server.on("POST", "/config/database/url", |url: String| {
        injector.update_key(Key::tagged(Tag::DatabaseUrl)?, url);
    });

    // Fake endpoint to set the database connection limit.
    server.on("POST", "/config/database/connection-limit", |limit: u32| {
        injector.update_key(Key::tagged(Tag::ConnectionLimit)?, limit);
    });

    // Listen for requests.
    server.await?;
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    let injector = Injector::new();

    /// Setup database provider.
    tokio::spawn({
        let injector = injector.clone();

        async move {
            DatabaseProvider::run(&injector).await;
        }
    });

    tokio::spawn({
        let injector = injector.clone();

        async move {
            serve(&injector).await.expect("web server errored");
        }
    });

    let (database_stream, database) = injector.stream::<Database>().await;

    let application = Application::new(database);

    loop {
        tokio::select! {
            // receive new databases when available.
            database = database_stream.next() => {
                application.database = database;
            },
            // run the application to completion.
            _ = &mut application => {
                log::info!("application finished");
            },
        }
    }
}
```
