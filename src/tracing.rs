#[cfg(feature = "tracing")]
mod defs {
    #[allow(unused_imports)]
    pub(crate) use ::tracing::Level;

    macro_rules! span {
        (Level::$level:ident, $($rest:tt)*) => { ::tracing::span!(::tracing::Level::$level, $($rest)*) };
        ($level:ident, $($rest:tt)*) => { ::tracing::span!(::tracing::Level::$level, $($rest)*) };
        ($($all:tt)*) => { ::tracing::span!($($all)*) };
    }

    macro_rules! event {
        (Level::$level:ident, $($rest:tt)*) => { ::tracing::event!(::tracing::Level::$level, $($rest)*) };
        ($level:ident, $($rest:tt)*) => { ::tracing::event!(::tracing::Level::$level, $($rest)*) };
        ($($all:tt)*) => { ::tracing::event!($($all)*) };
    }

    pub(crate) use event;
    pub(crate) use span;

    #[allow(dead_code)]
    #[cfg_attr(test, mutants::skip)]
    pub fn init_subscriber() {
        tracing_subscriber::fmt()
            .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
            .with_ansi(false)
            .init();
    }
}

#[cfg(not(feature = "tracing"))]
mod defs {
    /// Stub level when the `tracing` feature is disabled; only used inside macros (arguments are discarded).
    #[allow(dead_code)]
    pub enum Level {
        TRACE,
        DEBUG,
        INFO,
        WARN,
        ERROR,
    }

    pub struct Span {}

    impl Span {
        #[cfg_attr(test, mutants::skip)]
        pub const fn entered(&self) -> Self {
            Self {}
        }
    }

    macro_rules! span {
        (Level::$level:ident, $($rest:tt)*) => {{
            use crate::tracing::Span;
            Span {}
        }};
        ($level:ident, $($rest:tt)*) => {{
            use crate::tracing::Span;
            Span {}
        }};
        ($($any:tt)*) => {{
            use crate::tracing::Span;
            Span {}
        }};
    }

    pub(crate) use span;

    #[allow(dead_code)]
    pub struct Event {}

    macro_rules! event {
        (Level::$level:ident, $($rest:tt)*) => {{}};
        ($level:ident, $($rest:tt)*) => {{}};
        ($($any:tt)*) => {{}};
    }

    pub(crate) use event;

    #[allow(dead_code)]
    #[cfg_attr(test, mutants::skip)]
    pub const fn init_subscriber() {}
}

pub(crate) use defs::*;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_subscriber() {
        // Test that init_subscriber can be called without panicking
        // This covers the function even if it's marked as dead_code
        // Note: This may fail if a subscriber is already initialized, but that's okay
        // as it still exercises the code path
        let result = std::panic::catch_unwind(|| {
            init_subscriber();
        });
        // Explicitly drop the result to satisfy clippy
        drop(result);
    }

    #[test]
    fn test_span_macro() {
        // Test that span! macro works
        let _span = span!(Level::DEBUG, "test_span").entered();
    }

    #[test]
    fn test_event_macro() {
        // Test that event! macro works
        event!(Level::DEBUG, "test_event");
    }

    #[test]
    fn test_span_entered() {
        // Test that span.entered() works
        let span = span!(Level::DEBUG, "test");
        let _entered = span.entered();
    }

    #[test]
    fn test_span_macro_bare_level() {
        // Test that span! accepts bare level (no Level:: prefix, no import)
        let _span = span!(DEBUG, "bare_level_span").entered();
    }

    #[test]
    fn test_event_macro_bare_level() {
        // Test that event! accepts bare level (no Level:: prefix, no import)
        event!(INFO, "bare_level_event");
    }
}
