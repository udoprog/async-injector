use std::io::{BufRead, BufReader, Write};

use anyhow::{Context, Result};
use async_injector::{Injector, Key};

async fn greeter(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
    let name = Key::<String>::tagged("name")?;
    let fun = Key::<String>::tagged("fun")?;

    let (mut name_stream, mut name) = injector.stream_key(name).await;
    let (mut fun_stream, mut fun) = injector.stream_key(fun).await;

    loop {
        tokio::select! {
            update = name_stream.recv() => {
                name = update;
            }
            update = fun_stream.recv() => {
                fun = update;
            }
        }

        let (Some(name), Some(fun)) = (&name, &fun) else {
            continue;
        };

        println!("Hi {name}! I see you do \"{fun}\" for fun!");
        return Ok(());
    }
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
