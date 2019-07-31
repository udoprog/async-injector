#![feature(async_await)]

use futures::prelude::*;

use async_injector::{Injector, Key, Provider};

#[allow(unused)]
#[derive(Provider)]
struct TestPlain {
    #[dependency]
    foo: String,
}

impl TestPlain {
    #[allow(unused)]
    async fn clear(injector: &Injector) {}

    #[allow(unused)]
    async fn build(self, injector: &Injector) {}
}

#[allow(unused)]
#[derive(Provider)]
#[provider(error = "&'static str")]
struct TestFallible {
    #[dependency]
    foo: String,
}

impl TestFallible {
    #[allow(unused)]
    async fn clear(injector: &Injector) -> Result<(), &'static str> {
        Ok(())
    }

    #[allow(unused)]
    async fn build(self, injector: &Injector) -> Result<(), &'static str> {
        Ok(())
    }
}

#[allow(unused)]
#[derive(Provider)]
#[provider(constructor = "build2", clear = "clear2")]
struct TestCustomHooks {
    #[dependency]
    foo: String,
}

impl TestCustomHooks {
    #[allow(unused)]
    async fn clear2(injector: &Injector) {}

    #[allow(unused)]
    async fn build2(self, injector: &Injector) {}
}

#[allow(unused)]
#[derive(Provider)]
struct TestTagged {
    #[dependency(tag = "bar")]
    foo: String,
}

impl TestTagged {
    #[allow(unused)]
    async fn clear(injector: &Injector) {}

    #[allow(unused)]
    async fn build(self, injector: &Injector) {}
}

#[allow(unused)]
#[derive(Provider)]
struct TestFixed {
    fixed: String,
    #[dependency(tag = "bar")]
    foo: String,
}

impl TestFixed {
    #[allow(unused)]
    async fn clear(injector: &Injector) {}

    #[allow(unused)]
    async fn build(self, injector: &Injector) {}
}

#[allow(unused)]
#[derive(Provider)]
struct TestFixedLt<'a> {
    fixed: &'a str,
    #[dependency(tag = "bar")]
    foo: String,
}

impl<'a> TestFixedLt<'a> {
    #[allow(unused)]
    async fn clear(injector: &Injector) {}

    #[allow(unused)]
    async fn build(self, injector: &Injector) {}
}

#[allow(unused)]
#[derive(Provider)]
struct TestOptional {
    #[dependency(optional)]
    foo: Option<String>,
}

impl TestOptional {
    #[allow(unused)]
    async fn clear(injector: &Injector) {}

    #[allow(unused)]
    async fn build(self, injector: &Injector) {}
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

    impl<'a> Test<'a> {
        async fn clear(injector: &Injector) {
            injector.clear::<Foo>();
        }

        async fn build(self, injector: &Injector) {
            injector.update(Foo(Some(self.fixed.to_string()), self.foo, self.bar));
        }
    }
}
