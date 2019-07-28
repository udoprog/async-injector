# async-injector

Asynchronous dependency injection for Rust.

## Rationale

Sometimes it's not clear when a resource will become available in a system.
It might have to wait for user input or some other component before it can be configured.

For this purpose, this crate introduces the thread-safe `Injector`.

```rust
use failure::Error;
use async_injector::Injector;

/// Middleware for setting up a database instance that depends on configuration.
async fn database(injector: &Injector) -> Result<(), Error> {
    let (mut stream, mut current) = injector.stream::<DatabaseConfig>();

    if let Some(current) = current {
        injector.update(setup_db(current));
    }

    loop {
        match stream.select_next_some().await {
            Some(config) => injector.update(setup_db(config)?),
            None => injector.clear::<Database>(),
        }
    }

    fn setup_db(config: DatabaseConfig) -> Database {
        /*  */
    }
}

/// Main application. Takes dependencies from the injector and uses them.
async fn application(injector: &Injector) -> Result<(), Error> {
    let (mut stream, mut db) = injector.stream::<Database>();

    /* run main logic with database updates */
}

fn main() -> Result<(), Error> {
    let rt = Runtime::new()?;

    let injector = Injector::new();

    let mut futures = Vec::new();

    futures.push(database(&injector));

    futures.push(move {
        injector.clone().driver().await?;
        Ok::<_, Error>(())
    });

    futures.push(application(&injector));

    rt.block_on(futures::try_join_all(futures))?;
    /* run application */
}
```