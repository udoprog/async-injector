# async-injector

[![Documentation](https://docs.rs/async-injector/badge.svg)](https://docs.rs/async-injector)
[![Crates](https://img.shields.io/crates/v/async-injector.svg)](https://crates.io/crates/async-injector)
[![Actions Status](https://github.com/udoprog/async-injector/workflows/Rust/badge.svg)](https://github.com/udoprog/async-injector/actions)

Reactive dependency injection for Rust.

This project is _work in progress_. APIs will change.

## Rationale

This component was extracted and cleaned up from [`OxidizeBot`].

There it served as a central point for handling _live_ reconfiguration of the
application, without the need to restart it.

This crate provides a reactive dependency injection system that can reconfigure
your application dynamically from changes in your dependencies.

Using an `Injector` to deal with this complexity provides a nice option for a
clean architecture.

An injector is also a natural way for structuring an application that gracefully
degrades during the absence of configuration: any part of the dependency tree
that is not available can simply not be provided.

[`OxidizeBot`]: https://github.com/udoprog/OxidizeBot

## Example using `Key`s

The following showcases how the injector can be shared across threads, and how
you can distinguish between different keys of the same type (`u32`) using a
serde-serializable tag (`Tag`).

This example is runnable using:

```
cargo run --example key_injector
```

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

```rust
use anyhow::Error;
use async_injector::{Provider, Injector, Key, async_trait};

/// Provider that describes how to construct a database.
#[derive(Provider)]
struct DatabaseProvider {
    #[dependency(tag = "\"database/url\"")]
    url: String,
    #[dependency(tag = "\"database/connection-limit\"")]
    connection_limit: u32,
}

#[async_trait]
impl Provider for DatabaseProvider {
    type Output = Database;

    /// Constructor a new database and supply it to the injector.
    async fn build(self) -> Option<Self::Output> {
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
        injector.update_key(Key::tagged("database/url")?, url);
    });

    // Fake endpoint to set the database connection limit.
    server.on("POST", "/config/database/connection-limit", |limit: u32| {
        injector.update_key(Key::tagged("database/connection-limit")?, limit);
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
        futures::select! {
            // receive new databases when available.
            database = database_stream.next() => {
                application.database = database;
            },
            // run the application to completion.
            _ = application => {
                log::info!("application finished");
            },
        }
    }
}
```