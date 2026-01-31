#[cfg(feature = "tracing")]
#[must_use]
pub fn init_tracing() -> impl Drop {
    use tracing_flame::FlameLayer;
    use tracing_subscriber::{fmt, prelude::*};
    let filter_layer = tracing_subscriber::EnvFilter::from_default_env();
    let fmt_layer = fmt::Layer::default();
    let (flame_layer, _guard) = FlameLayer::with_file("./tracing.folded").unwrap();

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .with(flame_layer)
        .init();

    _guard
}

#[cfg(not(feature = "tracing"))]
#[allow(clippy::missing_const_for_fn)]
pub fn init_tracing() {}
