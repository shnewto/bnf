#[cfg(feature = "tracing")]
mod defs {
    pub use tracing::span;
    pub use tracing::Level;
}

#[cfg(not(feature = "tracing"))]
mod defs {
    pub enum Level {
        OFF,
        ERROR,
        WARN,
        INFO,
        DEBUG,
        TRACE,
    }

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
}

pub(crate) use defs::*;
