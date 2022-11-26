#[cfg(feature = "tracing")]
mod defs {
    pub(crate) use tracing::Level;

    pub(crate) use tracing::span;
}

#[cfg(not(feature = "tracing"))]
mod defs {
    enum Level {
        OFF,
        ERROR,
        WARN,
        INFO,
        DEBUG,
        TRACE,
    }

    macro_rules! span {
        ($($any:tt)*) => {};
    }

    pub(crate) use span;
}

pub(crate) use defs::*;

// #[cfg(feature="tracing")]
// pub(crate) struct Span {
//     inner: tracing::Span,
// }

// #[cfg(not(feature="tracing"))]
// pub(crate) struct Span {
// }

// #[cfg(feature="tracing")]
// pub(crate) fn span(level : Level, label: &'static str) -> Span {
//     use tracing::{Span, Metadata, Value};
//     let meta = Metadata::new(name, "unknown", level, None )
//     let inner = tracing::Span::new(meta, values);
//     Span { inner }
// }

// #[cfg(not(feature="tracing"))]
// pub(crate) fn span(level : Level) -> Span {
//     Span {}
// }
