#[cfg(feature = "tracing")]
mod defs {
    pub(crate) use tracing::span;
    pub(crate) use tracing::Level;
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
}

pub(crate) use defs::*;
