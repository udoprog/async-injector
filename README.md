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
automatically construct and inject dependencies.

```rust
use async_injector::{Key, Provider};
use serde::Serialize;
use tokio_stream::StreamExt as _;
use std::error::Error;

/// Fake database connection.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Database {
    url: String,
    connection_limit: u32,
}

impl Database {
    async fn build(provider: DatabaseProvider) -> Option<Self> {
        Some(Self {
            url: provider.url,
            connection_limit: provider.connection_limit,
        })
    }
}

/// Provider that describes how to construct a database.
#[derive(Serialize)]
pub enum Tag {
    DatabaseUrl,
    ConnectionLimit,
}

#[derive(Provider)]
#[provider(output = "Database", build = "Database::build")]
struct DatabaseProvider {
    #[dependency(tag = "Tag::DatabaseUrl")]
    url: String,
    #[dependency(tag = "Tag::ConnectionLimit")]
    connection_limit: u32,
}

#[tokio::test]
async fn test_provider() -> Result<(), Box<dyn Error>> {
    let db_url_key = Key::<String>::tagged(Tag::DatabaseUrl)?;
    let conn_limit_key = Key::<u32>::tagged(Tag::ConnectionLimit)?;

    let injector = async_injector::Injector::new();
    tokio::spawn(DatabaseProvider::run(injector.clone()));

    let (mut database_stream, database) = injector.stream::<Database>().await;

    // None of the dependencies are available, so it hasn't been constructed.
    assert!(database.is_none());

    assert!(injector
        .update_key(&db_url_key, String::from("example.com"))
        .await
        .is_none());

    assert!(injector.update_key(&conn_limit_key, 5).await.is_none());

    let new_database = database_stream
        .next()
        .await
        .expect("unexpected end of stream");

    // Database instance is available!
    assert_eq!(
        new_database,
        Some(Database {
            url: String::from("example.com"),
            connection_limit: 5
        })
    );

    Ok(())
}
```

[cannot be hashed]: https://internals.rust-lang.org/t/f32-f64-should-implement-hash/5436
[Injector]: https://docs.rs/async-injector/0/async_injector/struct.Injector.html
[Key]: https://docs.rs/async-injector/0/async_injector/struct.Key.html
[Provider]: https://docs.rs/async-injector-derive/0/async_injector_derive/derive.Provider.html
[serde]: https://serde.rs
[Stream]: https://docs.rs/futures-core/0/futures_core/stream/trait.Stream.html
