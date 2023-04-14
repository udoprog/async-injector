# async-injector

[<img alt="github" src="https://img.shields.io/badge/github-udoprog/async--injector-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/async-injector)
[<img alt="crates.io" src="https://img.shields.io/crates/v/async-injector.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/async-injector)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-async--injector-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/async-injector)
[<img alt="build status" src="https://img.shields.io/github/actions/workflow/status/udoprog/async-injector/ci.yml?branch=main&style=for-the-badge" height="20">](https://github.com/udoprog/async-injector/actions?query=branch%3Amain)

Asynchronous dependency injection for Rust.

This library provides the glue which allows for building robust decoupled
applications that can be reconfigured dynamically while they are running.

For a real world example of how this is used, see [`OxidizeBot`] for which
it was written.

<br>

## Usage

Add `async-injector` to your `Cargo.toml`.

```toml
[dependencies]
async-injector = "0.19.0"
```

<br>

## Example

In the following we'll showcase the injection of a *fake* `Database`. The
idea here would be that if something about the database connection changes,
a new instance of `Database` would be created and cause the application to
reconfigure itself.

```rust
use async_injector::{Key, Injector, Provider};

#[derive(Debug, Clone)]
struct Database;

#[derive(Debug, Provider)]
struct Service {
    #[dependency]
    database: Database,
}

async fn service(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
    let mut provider = Service::provider(&injector).await?;

    let Service { database } = provider.wait().await;
    println!("Service got initial database {database:?}!");

    let Service { database } = provider.wait().await;
    println!("Service got new database {database:?}!");

    Ok(())
}
```

> **Note:** This is available as the `database` example:
> ```sh
> cargo run --example database
> ```

The [`Injector`] above provides a structured broadcasting system that allows
for configuration updates to be cleanly integrated into asynchronous
contexts. The update itself is triggered by some other component that is
responsible for constructing the `Database` instance.

Building up the components of your application like this means that it can
be reconfigured without restarting it. Providing a much richer user
experience.

<br>

## Injecting multiple things of the same type

In the previous section you might've noticed that the injected value was
solely discriminated by its type: `Database`. In this example we'll show how
[`Key`] can be used to *tag* values of the same type with different names to
discriminate them. This can be useful when dealing with overly generic types
like [`String`].

The tag used must be serializable with [`serde`]. It must also not use any
components which [cannot be hashed], like `f32` and `f64`.

<br>

### A simple greeter

The following example showcases the use of `Key` to injector two different
values into an asynchronous `greeter`.

```rust
use async_injector::{Key, Injector};

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
```

> **Note:** you can run this using:
> ```sh
> cargo run --example greeter
> ```

The loop above can be implemented more easily using the [`Provider`] derive,
so let's do that.

```rust
use async_injector::{Injector, Provider};

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
```

> **Note:** you can run this using:
> ```sh
> cargo run --example greeter_provider
> ```

<br>

## The `Provider` derive

The [`Provider`] derive can be used to conveniently implement the mechanism
necessary to wait for a specific set of dependencies to become available.

It builds a companion structure next to the type being provided called
`<name>Provider` which in turn implements the following set of methods:

```rust
use async_injector::{Error, Injector};

impl Dependencies {
    /// Construct a new provider.
    async fn provider(injector: &Injector) -> Result<DependenciesProvider, Error>
}

struct DependenciesProvider {
    /* private fields */
}

impl DependenciesProvider {
    /// Try to construct the current value. Returns [None] unless all
    /// required dependencies are available.
    fn build(&mut self) -> Option<Dependencies>

    /// Wait until we can successfully build the complete provided
    /// value.
    async fn wait(&mut self) -> Dependencies

    /// Wait until the provided value has changed. Either some
    /// dependencies are no longer available at which it returns `None`,
    /// or all dependencies are available after which we return the
    /// build value.
    async fn wait_for_update(&mut self) -> Option<Dependencies>
}
```

<br>

### Fixed arguments to `Provider`

Any arguments which do not have the `#[dependency]` attribute are known as
"fixed" arguments. These must be passed in when calling the `provider`
constructor. They can also be used during tag construction.

```rust
use async_injector::{Injector, Key, Provider};

#[derive(Provider)]
struct Dependencies {
    name_tag: &'static str,
    #[dependency(tag = name_tag)]
    name: String,
}

async fn greeter(injector: Injector) -> Result<(), Box<dyn std::error::Error>> {
    let mut provider = Dependencies::provider(&injector, "name").await?;
    let Dependencies { name, .. } = provider.wait().await;
    println!("Hi {name}!");
    Ok(())
}
```

[`OxidizeBot`]: https://github.com/udoprog/OxidizeBot
[cannot be hashed]: https://internals.rust-lang.org/t/f32-f64-should-implement-hash/5436
[`Injector`]: https://docs.rs/async-injector/0/async_injector/struct.Injector.html
[`Key`]: https://docs.rs/async-injector/0/async_injector/struct.Key.html
[`Provider`]: https://docs.rs/async-injector/0/async_injector/derive.Provider.html
[`serde`]: https://serde.rs
[`Stream`]: https://docs.rs/futures-core/0/futures_core/stream/trait.Stream.html
[`String`]: https://doc.rust-lang.org/std/string/struct.String.html
