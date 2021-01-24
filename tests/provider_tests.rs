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
struct TestTagged {
    fixed: String,
    #[dependency(tag = "\"bar\"")]
    tag0: String,
    #[dependency(tag = "TestTagged::bar_tag(&fixed)")]
    tag1: String,
    #[dependency(tag = "42")]
    tag2: String,
}

impl TestTagged {
    fn bar_tag(fixed: &str) -> Tag {
        Tag::A
    }
}

#[derive(Provider)]
struct TestFixed {
    fixed: String,
    #[dependency(tag = "\"bar\"")]
    foo: String,
}

#[derive(Provider)]
struct TestFixedLt<'a> {
    fixed: &'a str,
    #[dependency(tag = "\"bar\"")]
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
        let (mut foo_stream, foo) = injector.stream::<Foo>().await;
        assert!(foo.is_none());

        // Updating foo and bar should construct Foo.
        injector.update::<String>(String::from("hello")).await;
        injector.update_key(&bar_key, String::from("world")).await;

        let foo_update = foo_stream.recv().await;
        let foo = foo_update.expect("value for Foo");

        assert_eq!(
            Foo(
                String::from("fixed"),
                String::from("hello"),
                String::from("world")
            ),
            foo
        );

        // Clearing bar should unset the value for `Foo`.
        injector.clear_key(&bar_key).await;

        let foo_update = foo_stream.recv().await;
        assert!(foo_update.is_none());

        finished.set(true);
    };
    tokio::pin!(test);

    let mut provider = Test::provider(&injector, "fixed").await?;

    loop {
        tokio::select! {
            _ = &mut test => {
                break;
            },
            update = provider.update() => {
                match update {
                    Some(update) => injector.update(Foo(update.fixed.to_string(), update.foo, update.bar)).await,
                    None => injector.clear::<Foo>().await,
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
        #[dependency(tag = "\"bar\"")]
        bar: String,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Foo(String, String, String);
}
