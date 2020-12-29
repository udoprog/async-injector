#![allow(unused)]

use futures::prelude::*;

use async_injector::{Error, Injector, Key, Provider};

#[derive(serde::Serialize)]
pub enum Tag {
    A,
}

#[derive(Provider)]
#[provider(output = "()")]
struct TestPlain {
    #[dependency]
    foo: String,
}

#[derive(Provider)]
#[provider(output = "()")]
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
#[provider(output = "()")]
struct TestFixed {
    fixed: String,
    #[dependency(tag = "\"bar\"")]
    foo: String,
}

#[derive(Provider)]
#[provider(output = "()")]
struct TestFixedLt<'a> {
    fixed: &'a str,
    #[dependency(tag = "\"bar\"")]
    foo: String,
}

#[derive(Provider)]
#[provider(output = "()")]
struct TestOptional {
    #[dependency(optional)]
    foo: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Foo(Option<String>, String, String);

#[test]
fn test_something() -> Result<(), Error> {
    let (injector, driver) = async_injector::setup_with_driver();

    let bar_key = Key::<String>::tagged("bar")?;
    let driver = Test::builder().fixed("fixed").build()?;

    futures::executor::block_on(async move {
        let mut finished = false;

        let test = Box::pin(async {
            let (mut foo_stream, foo) = injector.stream::<Foo>().await;
            assert!(foo.is_none());

            // Updating foo and bar should construct Foo.
            injector.update::<String>(String::from("hello")).await;
            injector.update_key(&bar_key, String::from("world")).await;

            let foo_update = foo_stream.select_next_some().await;
            let foo = foo_update.expect("value for Foo");

            assert_eq!(
                Foo(
                    Some(String::from("fixed")),
                    String::from("hello"),
                    String::from("world")
                ),
                foo
            );

            // Clearing bar should unset the value for `Foo`.
            injector.clear_key(&bar_key).await;

            let foo_update = foo_stream.select_next_some().await;
            assert!(foo_update.is_none());

            finished = true;
        });

        // Driver responsible for updating `Foo`.
        let driver = Box::pin(driver.run(injector.clone()));

        let future = futures::future::select(driver, test);
        let _ = future.await;

        assert!(finished);
    });

    return Ok(());

    #[derive(Provider)]
    #[provider(build = "Test::build", output = "Foo")]
    struct Test<'a> {
        fixed: &'a str,
        /// Dependency to untagged foo.
        #[dependency]
        foo: String,
        /// Dependency to tagged bar.
        #[dependency(tag = "\"bar\"")]
        bar: String,
    }

    impl<'a> Test<'a> {
        async fn build(self) -> Option<Foo> {
            Some(Foo(Some(self.fixed.to_string()), self.foo, self.bar))
        }
    }
}

#[test]
fn test_hierarchy() -> Result<(), Error> {
    use futures::prelude::*;

    let (injector, driver) = async_injector::setup_with_driver();
    let c1 = injector.child();
    let c2 = injector.child();

    let key = Key::<String>::tagged("foo")?;

    futures::executor::block_on(async move {
        let mut finished_updates = false;
        let mut finished_streams = false;

        let driver = Box::pin(driver.drive());

        let (tx, rx) = futures::channel::oneshot::channel::<()>();

        let test1 = Box::pin(async {
            let _ = rx.await.expect("successful receive");

            injector.update_key(&key, String::from("a")).await;
            c2.update_key(&key, String::from("b")).await;

            assert_eq!("a", c1.get_key(&key).await.expect("expected value: a"));
            assert_eq!("b", c2.get_key(&key).await.expect("expected value: b"));

            finished_updates = true;
        });

        let test2 = Box::pin(async {
            let (mut s1, _) = injector.stream_key(&key).await;
            let (mut s2, _) = c1.stream_key(&key).await;
            let (mut s3, _) = c2.stream_key(&key).await;

            tx.send(()).expect("successful send");

            let a = s1.select_next_some().await;
            let b = s2.select_next_some().await;
            let c = s3.select_next_some().await;

            assert_eq!("a", a.expect("expected value: a"));
            assert_eq!("a", b.expect("expected value: a"));
            assert_eq!("b", c.expect("expected value: b"));

            finished_streams = true;
        });

        let test = futures::future::join(test1, test2);

        let future = futures::future::select(driver, test);
        let _ = future.await;

        assert!(finished_updates);
        assert!(finished_streams);
    });

    Ok(())
}
