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

## The `Provider` derive

The following showcases how the [`Provider` derive] can be used to
automatically construct and inject dependencies.

```rust
use async_injector::{Injector, Key, Provider};
use serde::Serialize;
use tokio::stream::StreamExt as _;

/// Fake database connection.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Database {
    url: String,
    connection_limit: u32,
}

impl Database {
    async fn build(provider: DatabaseProvider2) -> Option<Self> {
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
struct DatabaseProvider2 {
    #[dependency(tag = "Tag::DatabaseUrl")]
    url: String,
    #[dependency(tag = "Tag::ConnectionLimit")]
    connection_limit: u32,
}

#[tokio::test]
async fn test_provider() -> Result<(), Box<dyn std::error::Error>> {
    let db_url_key = Key::<String>::tagged(Tag::DatabaseUrl)?;
    let conn_limit_key = Key::<u32>::tagged(Tag::ConnectionLimit)?;

    let injector = Injector::new();
    tokio::spawn(DatabaseProvider2::run(injector.clone()));

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

[`Provider` derive]: https://docs.rs/async-injector-derive/0/async_injector_derive/derive.Provider.html
