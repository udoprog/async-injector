# async-injector

[![Documentation](https://docs.rs/async-injector/badge.svg)](https://docs.rs/async-injector)
[![Crates](https://img.shields.io/crates/v/async-injector.svg)](https://crates.io/crates/async-injector)
[![Actions Status](https://github.com/udoprog/async-injector/workflows/Rust/badge.svg)](https://github.com/udoprog/async-injector/actions)

Asynchronous dependency injection for Rust.

This crate provides a dependency injection system that can be used to
reactively reconfigure you're application while it's running. Reactive in
this case refers to the application being reconfigured as-the-value changes,
and not for other typical scenarios such as when it's being restarted.

Values are provided as [Stream]s of updates that can be subscribed to as
necessary throughout your application.

## Examples

In the following we'll showcase the injection of a *fake* `Database`. The
idea here would be that if something about the database connection changes,
a new instance of `Database` would be created and cause the application to
update.

> This is available as the `fake_database` example and you can run it
> yourself using:
> ```sh
> cargo run --example fake_database
> ```

```rust
use tokio::time;
use tokio_stream::StreamExt as _;

#[derive(Clone)]
struct Database;

#[tokio::main]
async fn main() {
    let injector = async_injector::Injector::new();
    let (mut database_stream, mut database) = injector.stream::<Database>().await;

    // Insert the database dependency in a different task in the background.
    tokio::spawn({
        let injector = injector.clone();

        async move {
            time::sleep(time::Duration::from_secs(2)).await;
            injector.update(Database).await;
        }
    });

    assert!(database.is_none());

    // Every update to the stored type will be streamed, allowing you to
    // react to it.
    if let Some(update) = database_stream.next().await {
        println!("Updating database!");
        database = update;
    } else {
        panic!("No database update received :(");
    }

    assert!(database.is_some());
}
```

The [Injector] provides a structured broadcast system of updates, that can
integrate cleanly into asynchronous contexts.

With a bit of glue, this means that your application can be reconfigured
without restarting it. Providing a richer user experience.

### Injecting multiple things of the same type

In the previous section you might've noticed that the injected value was
solely discriminated by its type: `Database`. In this example we'll show how
[Key] can be used to *tag* values of the same type under different names.
This can be useful when dealing with overly generic types like [String].

The tag used must be serializable with [serde]. It must also not use any
components which [cannot be hashed], like `f32` and `f64`. This will
otherwise cause an error to be raised as it's being injected.

```rust
use async_injector::Key;
use serde::Serialize;
use std::{error::Error, time::Duration};
use tokio::time;
use tokio_stream::StreamExt as _;

#[derive(Serialize)]
enum Tag {
    One,
    Two,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let injector = async_injector::Injector::new();
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

## The `Provider` derive

The following showcases how the [Provider] derive can be used to
conveniently wait for groups of dependencies to become available.

Below we're waiting for two database parameters to become updated:
* `url`
* `connection_limit`

Also note how they're being update asynchronously in a background thread to
simulate being updated "somewhere else". This could be an update event
caused by a multitude of things, like a configuration change in a frontend.

```rust
use async_injector::{Key, Provider, Injector};
use serde::Serialize;
use std::error::Error;
use std::time::Duration;
use tokio_stream::StreamExt as _;

/// Fake database connection.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Database {
    url: String,
    connection_limit: u32,
}

/// Provider that describes how to construct a database.
#[derive(Serialize)]
pub enum Tag {
    DatabaseUrl,
    ConnectionLimit,
}

/// A group of database params to wait for until they become available.
#[derive(Provider)]
struct DatabaseParams {
    #[dependency(tag = "Tag::DatabaseUrl")]
    url: String,
    #[dependency(tag = "Tag::ConnectionLimit")]
    connection_limit: u32,
}

async fn update_db_params(injector: Injector, db_url: Key<String>, connection_limit: Key<u32>) {
    tokio::time::sleep(Duration::from_secs(2));

    injector.update_key(&db_url, String::from("example.com")).await;
    injector.update_key(&connection_limit, 5).await;
}

/// Fake service that runs for two seconds with a configured database.
async fn service(db: Database) {
    tokio::time::sleep(Duration::from_secs(2));
}

#[tokio::test]
async fn test_provider() -> Result<(), Box<dyn Error>> {
    let db_url = Key::<String>::tagged(Tag::DatabaseUrl)?;
    let connection_limit = Key::<u32>::tagged(Tag::ConnectionLimit)?;

    let injector = Injector::new();

    /// Set up asynchronous task that updates the parameters in the background.
    tokio::spawn(update_db_params(injector.clone(), db_url, connection_limit));

    let provider = DatabaseParams::new(&injector).await?;

    loop {
        /// Wait until database is configured.
        let database = loop {
            if let Some(update) = provider.update().await {
                break Database {
                    url: update.url,
                    connection_limit: update.connection_limit,
                };
            }
        };

        assert_eq!(
            new_database,
            Database {
                url: String::from("example.com"),
                connection_limit: 5
            }
        );

        loop {
            tokio::select! {
                _ = service(database.clone()) => {
                    break;
                }
                update = provider.update().await {
                    match update {
                        None => break,
                    }
                }
            }
        }
    }

    Ok(())
}
```

[cannot be hashed]: https://internals.rust-lang.org/t/f32-f64-should-implement-hash/5436
[Injector]: https://docs.rs/async-injector/0/async_injector/struct.Injector.html
[Key]: https://docs.rs/async-injector/0/async_injector/struct.Key.html
[Provider]: https://docs.rs/async-injector-derive/0/async_injector_derive/derive.Provider.html
[serde]: https://serde.rs
[Stream]: https://docs.rs/futures-core/0/futures_core/stream/trait.Stream.html
