#![allow(dead_code)]

use anyhow::Error;
use async_injector::{Key, Provider};
use std::sync::Arc;

/// A simple dummy database for injection purposes.
#[derive(Debug)]
struct Database;

/// Thing to be injected.
///
/// It has two dependencies: A title, and a database.
#[derive(Clone, Debug)]
struct Thing {
    title: String,
    db: Arc<Database>,
}

/// Provider that describes how to construct a `Thing`.
#[derive(Provider)]
struct ThingProvider {
    #[dependency(tag = "\"title\"")]
    title: String,
    #[dependency]
    db: Arc<Database>,
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    use std::{thread, time::Duration};

    let injector = async_injector::Injector::new();
    let thread_injector = injector.clone();

    let title_key = Key::<String>::tagged("title")?;

    // A separate thread which updates values in the injector once in a while.
    let t = tokio::spawn(async move {
        let injector = thread_injector;

        // Nothing will happen, since we don't have all the dependencies.
        thread::sleep(Duration::from_secs(1));
        injector
            .update_key(&title_key, String::from("New Title"))
            .await;

        // Set the database dependency and we will get the thing with `New Title`.
        thread::sleep(Duration::from_secs(1));
        injector.update(Arc::new(Database)).await;

        thread::sleep(Duration::from_secs(1));
        injector.clear_key(&title_key).await;

        thread::sleep(Duration::from_secs(1));
        injector
            .update_key(&title_key, String::from("Bye Bye"))
            .await;
    });

    // Showcases using asynchronized variable to observe `Thing`.
    // This uses `parking_lot::RwLock`.
    let thing_var = injector.var::<Thing>().await;

    // A thing that observes synchronized variables.
    let t2 = tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_secs(1)).await;
            let thing = thing_var.read().await;
            println!("Synchronized thing: {:?}", thing.as_deref());

            if let Some(thing) = thing.as_deref() {
                if thing.title == "Bye Bye" {
                    break;
                }
            }
        }
    });

    // Provides `Thing`.
    let mut provider = ThingProvider::provider(&injector).await?;

    // Future that observes changes to Thing.
    let task = async {
        let (mut thing_stream, thing) = injector.stream::<Thing>().await;
        println!("First thing: {:?}", thing);

        loop {
            let thing = thing_stream.recv().await;
            println!("New thing: {:?}", thing);

            if let Some(thing) = thing {
                if thing.title == "Bye Bye" {
                    break;
                }
            }
        }
    };
    tokio::pin!(task);

    // Just blocking over all futures, not checking errors.
    tokio::select! {
        _ = task => {},
        update = provider.wait_for_update() => {
            match update {
                Some(update) => {
                    injector.update(Thing {
                        title: update.title,
                        db: update.db,
                    }).await;
                }
                None => {
                    injector.clear::<Thing>().await;
                }
            }
        },
    }

    t.await.expect("thread didn't exit gracefully");
    t2.await.expect("thread didn't exit gracefully");

    Ok(())
}
