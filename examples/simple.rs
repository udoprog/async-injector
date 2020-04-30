use anyhow::Error;
use async_injector::{Injector, Key, Provider};
use futures::prelude::*;
use std::{pin::Pin, sync::Arc};

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
#[provider(build = "ThingProvider::build", output = "Thing")]
struct ThingProvider {
    #[dependency(tag = "\"title\"")]
    title: String,
    #[dependency]
    db: Arc<Database>,
}

impl ThingProvider {
    async fn build(self) -> Option<Thing> {
        Some(Thing {
            title: self.title,
            db: self.db,
        })
    }
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    use std::{thread, time::Duration};

    let injector = Injector::new();
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
    let thing_var = injector.var::<Thing>().await?;

    // A thing that observes synchronized variables.
    let t2 = tokio::spawn(async move {
        loop {
            tokio::time::delay_for(Duration::from_secs(1)).await;
            let thing = thing_var.read().await;
            println!("Synchronized thing: {:?}", *thing);

            if let Some(thing) = &*thing {
                if thing.title == "Bye Bye" {
                    break;
                }
            }
        }
    });

    let mut futures: Vec<Pin<Box<dyn Future<Output = Result<(), Error>>>>> = Vec::new();

    // Provides `Thing`.
    futures.push(Box::pin(async {
        ThingProvider::run(&injector)
            .await
            .expect("injector not to error");
        Ok(())
    }));

    // Keeps synchronized variables up-to-date.
    futures.push(Box::pin(injector.clone().drive().map_err(Into::into)));

    // Future that observes changes to Thing.
    futures.push(Box::pin(async {
        let (mut thing_stream, thing) = injector.stream::<Thing>().await;

        println!("First thing: {:?}", thing);

        while let Some(thing) = thing_stream.next().await {
            println!("New thing: {:?}", thing);

            if let Some(thing) = thing {
                if thing.title == "Bye Bye" {
                    break;
                }
            }
        }

        Ok(())
    }));

    // Just blocking over all futures, not checking errors.
    let _ = futures::future::select_all(futures).await;

    let _ = t.await.expect("thread didn't exit gracefully");
    let _ = t2.await.expect("thread didn't exit gracefully");

    Ok(())
}
