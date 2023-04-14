#![allow(dead_code)]

use async_injector::{Key, Provider};
use serde::Serialize;

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

#[derive(Provider)]
struct DatabaseParams {
    #[dependency(tag = Tag::DatabaseUrl)]
    url: String,
    #[dependency(tag = Tag::ConnectionLimit)]
    connection_limit: u32,
}

#[tokio::test]
async fn test_provider() -> Result<(), Box<dyn std::error::Error>> {
    let db_url_key = Key::<String>::tagged(Tag::DatabaseUrl)?;
    let conn_limit_key = Key::<u32>::tagged(Tag::ConnectionLimit)?;

    let injector = async_injector::Injector::new();
    let mut database_params = DatabaseParams::provider(&injector).await?;
    let database_injector = injector.clone();

    tokio::spawn(async move {
        loop {
            match database_params.wait_for_update().await {
                Some(update) => {
                    database_injector
                        .update(Database {
                            url: update.url,
                            connection_limit: update.connection_limit,
                        })
                        .await;
                }
                None => {
                    database_injector.clear::<Database>().await;
                }
            }
        }
    });

    let (mut database_stream, database) = injector.stream::<Database>().await;

    // None of the dependencies are available, so it hasn't been constructed.
    assert!(database.is_none());

    assert!(injector
        .update_key(&db_url_key, String::from("example.com"))
        .await
        .is_none());

    assert!(injector.update_key(&conn_limit_key, 5).await.is_none());

    let new_database = database_stream.recv().await;

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
