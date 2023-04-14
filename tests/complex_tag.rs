#![allow(unused)]

use async_injector::Provider;

#[derive(serde::Serialize)]
pub enum Tag {
    A,
}

#[derive(Provider)]
struct TestTagged {
    fixed: String,
    #[dependency(tag = "bar")]
    tag0: String,
    #[dependency(tag = TestTagged::bar_tag(&fixed))]
    tag1: String,
    #[dependency(tag = 42)]
    tag2: String,
}

impl TestTagged {
    fn bar_tag(fixed: &str) -> Tag {
        Tag::A
    }
}
