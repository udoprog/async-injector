#![allow(unused)]

use async_injector::{Error, Injector, Key, Provider};

#[derive(serde::Serialize)]
pub enum Tag {
    A,
}

#[derive(Provider)]
struct TestPlain {
    #[dependency]
    foo: String,
}

#[derive(Provider)]
struct TestFixed {
    fixed: String,
    #[dependency(tag = "bar")]
    foo: String,
}

#[derive(Provider)]
struct TestFixedLt<'a> {
    fixed: &'a str,
    #[dependency(tag = "bar")]
    foo: String,
}

#[derive(Provider)]
struct TestOptional {
    #[dependency(optional)]
    foo: Option<String>,
}

#[tokio::test]
async fn test_something() -> Result<(), Error> {
    use std::cell::Cell;

    let injector = async_injector::Injector::new();

    let bar_key = Key::<String>::tagged("bar")?;

    let finished = Cell::new(false);

    let test = async {
        let (mut value_stream, value) = injector.stream::<Value>().await;
        assert!(value.is_none());

        // Updating foo and bar should construct Foo.
        injector.update::<String>(String::from("hello")).await;
        injector.update_key(&bar_key, String::from("world")).await;

        let value_update = value_stream.recv().await;
        let value = value_update.expect("value for Foo");

        assert_eq!(
            Value(
                String::from("fixed"),
                String::from("hello"),
                String::from("world")
            ),
            value
        );

        // Clearing bar should unset the value for `Foo`.
        injector.clear_key(&bar_key).await;

        let value_update = value_stream.recv().await;
        assert!(value_update.is_none());

        finished.set(true);
    };
    tokio::pin!(test);

    let mut provider = Test::provider(&injector, "fixed").await?;

    loop {
        tokio::select! {
            _ = &mut test => {
                break;
            },
            update = provider.wait_for_update() => {
                match update {
                    Some(update) => injector.update(Value(update.fixed.to_string(), update.foo, update.bar)).await,
                    None => injector.clear::<Value>().await,
                }
            }
        };
    }

    assert!(finished.get());
    return Ok(());

    #[derive(Provider)]
    struct Test<'a> {
        fixed: &'a str,
        /// Dependency to untagged foo.
        #[dependency]
        foo: String,
        /// Dependency to tagged bar.
        #[dependency(tag = "bar")]
        bar: String,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Value(String, String, String);
}
