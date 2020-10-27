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
