use tokio::time;
use tokio_stream::StreamExt as _;

#[derive(Clone)]
struct Database;

#[tokio::main]
async fn main() {
    let injector = async_injector::setup();
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
