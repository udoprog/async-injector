#![allow(unused)]

use async_injector::Provider;

#[derive(serde::Serialize)]
pub enum Tag {
    A,
}

#[derive(Provider)]
struct ReusingFixed {
    fixed: String,
    #[dependency(tag = "bar")]
    tag0: String,
    #[dependency(tag = String::from(&fixed))]
    tag1: String,
    #[dependency(tag = 42)]
    tag2: String,
}

impl ReusingFixed {
    fn bar_tag(fixed: &str) -> Tag {
        Tag::A
    }
}
