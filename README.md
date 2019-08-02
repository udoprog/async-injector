# async-injector

[![Build Status](https://travis-ci.org/udoprog/async-injector.svg?branch=master)](https://travis-ci.org/udoprog/async-injector)

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

## Example

The following is an example application that receives configuration changes
over HTTP.

```rust
#![feature(async_await)]

use failure::Error;
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
        injector.update_key(Key::tagged("database/url"), url);
    });

    // Fake endpoint to set the database connection limit.
    server.on("POST", "/config/database/connection-limit", |limit: u32| {
        injector.update_key(Key::tagged("database/connection-limit"), limit);
    });

    // Listen for requests.
    server.await?;
    Ok(())
}

#[runtime::main]
async fn main() -> Result<(), Error> {
    let injector0 = Injector::new();

    /// Setup database provider.
    let injector = injector0.clone();

    runtime::spawn(async move {
        DatabaseProvider::run(&injector0).await;
    });

    let injector = injector0.clone();

    runtime::spawn(async move {
        serve(&injector).await.expect("web server errored");
    })

    let (database_stream, database) = injector0.stream::<Database>();

    let application = Application::new(database);

    loop {
        futures::select {
            // receive new databases when available.
            database = database_stream.next() => {
                application.database = database;
            }
            // run the application to completion.
            _ = application => {
                log::info!("application finished");
            }
        }
    }
}
```