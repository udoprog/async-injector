use std::io::{BufRead, BufReader, Write};

use anyhow::{Context, Result};
use async_injector::{Injector, Key, Provider};

#[derive(Debug, Clone)]
struct Database {
    limit: usize,
}

#[derive(Debug, Provider)]
struct Service {
    #[dependency]
    database: Database,
}

async fn service(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
    let mut provider = Service::provider(&injector).await?;

    let Service { database } = provider.wait().await;
    println!(
        "Service got initial database with limit {}!",
        database.limit
    );

    let Service { database } = provider.wait().await;
    println!("Service got new database with limit {}!", database.limit);

    Ok(())
}

#[derive(Debug, Provider)]
struct Connect {
    #[dependency(tag = "url")]
    url: String,
    #[dependency(tag = "limit", optional)]
    limit: Option<usize>,
}

async fn connect(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
    let mut provider = Connect::provider(&injector).await?;

    loop {
        let connect = provider.wait().await;
        let limit = connect.limit.unwrap_or(10);
        println!(
            "Would connect to url {} with limit {}, but I'm not a real database!",
            connect.url, limit
        );
        injector.update(Database { limit }).await;
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let injector = Injector::new();

    let connector = connect(injector.clone());

    tokio::spawn(async move {
        if let Err(error) = connector.await {
            println!("Connector errored: {error}");
        }
    });

    let service = service(injector.clone());

    let service = tokio::spawn(async move {
        if let Err(error) = service.await {
            println!("Connector errored: {error}");
        }
    });

    let mut stdout = std::io::stdout();
    let stdin = std::io::stdin();
    let stdin = BufReader::new(stdin.lock());
    let mut lines = stdin.lines();

    write!(stdout, "Url for database? ")?;
    stdout.flush()?;
    let connection = lines.next().context("missing response")??;
    injector.update_key(Key::tagged("url")?, connection).await;

    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    write!(stdout, "Limit? ")?;
    stdout.flush()?;

    let limit = lines
        .next()
        .context("missing response")??
        .parse::<usize>()?;
    injector.update_key(Key::tagged("limit")?, limit).await;

    service.await?;
    println!("Bye!");
    Ok(())
}
