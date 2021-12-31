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
            injector.update(Database).await;
        }
    });

    assert!(database.is_none());
    // Every update to the stored type will be streamed, allowing you to react
    // to it.
    database = database_stream.recv().await;
    assert!(database.is_some());
}
