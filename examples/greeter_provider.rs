use std::io::{BufRead, BufReader, Write};

use anyhow::{Context, Result};
use async_injector::{Injector, Key, Provider};

#[derive(Provider)]
struct Dependencies {
    #[dependency(tag = "name")]
    name: String,
    #[dependency(tag = "fun")]
    fun: String,
}

async fn greeter(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
    let mut provider = Dependencies::provider(&injector).await?;
    let Dependencies { name, fun } = provider.wait().await;
    println!("Hi {name}! I see you do \"{fun}\" for fun!");
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    let injector = Injector::new();
    let greeter = greeter(injector.clone());

    let task = tokio::spawn(async move {
        if let Err(error) = greeter.await {
            println!("Greeter errored: {error}");
        }
    });

    let mut stdout = std::io::stdout();
    let stdin = std::io::stdin();
    let stdin = BufReader::new(stdin.lock());
    let mut lines = stdin.lines();

    let name_key = Key::<String>::tagged("name")?;
    let fun_key = Key::<String>::tagged("fun")?;

    write!(stdout, "What is your name? ")?;
    stdout.flush()?;
    let name = lines.next().context("missing response")??;

    injector.update_key(&name_key, name).await;

    write!(stdout, "What do you do for fun? ")?;
    stdout.flush()?;
    let fun = lines.next().context("missing response")??;
    injector.update_key(&fun_key, fun).await;

    task.await?;

    println!("Bye!");
    Ok(())
}
