use async_injector::{Injector, Key, Provider};
use serde::Serialize;
use std::error::Error;
use std::future::pending;
use std::time::Duration;
use tokio::task::yield_now;
use tokio::time::sleep;

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
    Shutdown,
}

/// A group of database params to wait for until they become available.
#[derive(Provider)]
struct DatabaseParams {
    #[dependency(tag = "Tag::DatabaseUrl")]
    url: String,
    #[dependency(tag = "Tag::ConnectionLimit")]
    connection_limit: u32,
}

async fn update_db_params(
    injector: Injector,
    db_url: Key<String>,
    connection_limit: Key<u32>,
    shutdown: Key<bool>,
) {
    injector
        .update_key(&db_url, String::from("example.com"))
        .await;

    for limit in 5..10 {
        sleep(Duration::from_millis(100)).await;
        injector.update_key(&connection_limit, limit).await;
    }

    // Yield to give the update a chance to propagate.
    yield_now().await;
    injector.update_key(&shutdown, true).await;
}

/// Fake service that runs for two seconds with a configured database.
async fn service(database: Database) {
    println!("Starting new service with database: {:?}", database);
    pending::<()>().await;
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let db_url = Key::<String>::tagged(Tag::DatabaseUrl)?;
    let connection_limit = Key::<u32>::tagged(Tag::ConnectionLimit)?;
    let shutdown = Key::<bool>::tagged(Tag::Shutdown)?;

    let injector = Injector::new();

    // Set up asynchronous task that updates the parameters in the background.
    tokio::spawn(update_db_params(
        injector.clone(),
        db_url,
        connection_limit,
        shutdown.clone(),
    ));

    let mut provider = DatabaseParams::provider(&injector).await?;

    // Wait until database is configured.
    let params = provider.wait().await;

    let database = Database {
        url: params.url,
        connection_limit: params.connection_limit,
    };

    assert_eq!(
        database,
        Database {
            url: String::from("example.com"),
            connection_limit: 5
        }
    );

    let (mut shutdown, is_shutdown) = injector.stream_key(&shutdown).await;

    if is_shutdown == Some(true) {
        return Ok(());
    }

    let fut = service(database);
    tokio::pin!(fut);

    loop {
        tokio::select! {
            _ = &mut fut => {
                break;
            }
            is_shutdown = shutdown.recv() => {
                if is_shutdown == Some(true) {
                    break;
                }
            }
            params = provider.wait() => {
                fut.set(service(Database {
                    url: params.url,
                    connection_limit: params.connection_limit,
                }));
            }
        }
    }

    Ok(())
}
