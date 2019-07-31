#![feature(async_await)]

use futures::prelude::*;

use async_injector::{async_trait, Injector, Key, Provider};

#[allow(unused)]
#[derive(Provider)]
struct TestPlain {
    #[dependency]
    foo: String,
}

#[async_trait]
impl Provider for TestPlain {
    type Output = ();
}

#[allow(unused)]
#[derive(Provider)]
struct TestTagged {
    #[dependency(tag = "bar")]
    foo: String,
}

#[async_trait]
impl Provider for TestTagged {
    type Output = ();
}

#[allow(unused)]
#[derive(Provider)]
struct TestFixed {
    fixed: String,
    #[dependency(tag = "bar")]
    foo: String,
}

#[async_trait]
impl Provider for TestFixed {
    type Output = ();
}

#[allow(unused)]
#[derive(Provider)]
struct TestFixedLt<'a> {
    fixed: &'a str,
    #[dependency(tag = "bar")]
    foo: String,
}

#[async_trait]
impl<'a> Provider for TestFixedLt<'a> {
    type Output = ();
}

#[allow(unused)]
#[derive(Provider)]
struct TestOptional {
    #[dependency(optional)]
    foo: Option<String>,
}

#[async_trait]
impl Provider for TestOptional {
    type Output = ();
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Foo(Option<String>, String, String);

#[test]
fn test_something() {
    let injector = Injector::new();

    futures::executor::block_on(async move {
        let bar_key = Key::<String>::tagged("bar");

        let mut finished = false;

        let test = Box::pin(async {
            let (mut foo_stream, foo) = injector.stream::<Foo>();
            assert!(foo.is_none());

            // Updating foo and bar should construct Foo.
            injector.update::<String>(String::from("hello"));
            injector.update_key(&bar_key, String::from("world"));

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
            injector.clear_key::<String>(&bar_key);

            let foo_update = foo_stream.select_next_some().await;
            assert!(foo_update.is_none());

            finished = true;
        });

        // Driver responsible for updating `Foo`.
        let driver = Test::builder().fixed("fixed").build();
        let driver = Box::pin(driver.run(&injector));

        let future = futures::future::select(driver, test);
        let _ = future.await;

        assert!(finished);
    });

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

    #[async_trait]
    impl<'a> Provider for Test<'a> {
        type Output = Foo;

        async fn build(self) -> Option<Self::Output> {
            Some(Foo(Some(self.fixed.to_string()), self.foo, self.bar))
        }
    }
}
