#[cfg(feature = "tracing")]
mod defs {
    pub(crate) use tracing::{event, span, Level};

    pub fn init_subscriber() {
        tracing_subscriber::fmt::init()
    }
}

#[cfg(not(feature = "tracing"))]
mod defs {
    pub struct Span {}

    impl Span {
        pub fn entered(&self) -> Self {
            Self {}
        }
    }

    macro_rules! span {
        ($($any:tt)*) => {{
            use crate::tracing::Span;
            Span {}
        }};
    }

    pub(crate) use span;

    pub struct Event {}

    macro_rules! event {
        ($($any:tt)*) => {{
            use crate::tracing::Event;
            Event {}
        }};
    }

    pub(crate) use event;

    #[allow(dead_code)]
    pub fn init_subscriber() {}
}

pub(crate) use defs::*;
