#![feature(async_await)]

use futures::prelude::*;

use async_injector::{Injector, Key};
use async_injector_derive::Provider;

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
        let driver = Test::builder().fixed(String::from("fixed")).build();
        let driver = Box::pin(driver.run(&injector));

        let future = futures::future::select(driver, test);
        let _ = future.await;

        assert!(finished);
    });

    #[derive(Provider)]
    #[provider(of = "Foo", constructor = "build", error = "()")]
    struct Test {
        fixed: String,
        /// Dependency to untagged foo.
        #[dependency]
        foo: String,
        /// Dependency to tagged bar.
        #[dependency(tag = "bar")]
        bar: String,
    }

    impl Test {
        async fn build(self) -> Result<Foo, ()> {
            Ok(Foo(Some(self.fixed), self.foo, self.bar))
        }
    }
}

/// Makes sure that the immediate run function is available if we don't have any fixed dependencies.
#[test]
fn test_immediate_run() {
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

            assert_eq!(Foo(None, String::from("hello"), String::from("world")), foo);

            // Clearing bar should unset the value for `Foo`.
            injector.clear_key::<String>(&bar_key);

            let foo_update = foo_stream.select_next_some().await;
            assert!(foo_update.is_none());

            finished = true;
        });

        // Driver responsible for updating `Foo`.
        // Can be specified without a builder because it doesn't have any fixed fields.
        let driver = Box::pin(Test::run(&injector));

        let future = futures::future::select(driver, test);
        let _ = future.await;

        assert!(finished);
    });

    #[derive(Provider)]
    #[provider(of = "Foo", constructor = "build", error = "()")]
    struct Test {
        #[dependency]
        foo: String,
        /// Dependency to tagged bar.
        #[dependency(tag = "bar")]
        bar: String,
    }

    impl Test {
        async fn build(self) -> Result<Foo, ()> {
            Ok(Foo(None, self.foo, self.bar))
        }
    }
}
