//! OpenTelemetry setup for rewatch.
//!
//! Provides optional tracing export via OTLP HTTP when OTEL_EXPORTER_OTLP_ENDPOINT is set.
//! When the environment variable is not set, tracing is disabled (no-op).

use opentelemetry::trace::TracerProvider as _;
use opentelemetry_otlp::{Protocol, SpanExporter, WithExportConfig};
use opentelemetry_sdk::Resource;
use opentelemetry_sdk::trace::SdkTracerProvider;
use tracing_log::{AsLog, LogTracer};
use tracing_subscriber::EnvFilter;
use tracing_subscriber::layer::SubscriberExt;

/// Guard that ensures telemetry is properly flushed and shut down.
/// Drop this at the end of main to flush all spans.
pub struct TelemetryGuard {
    /// Present exactly when OTLP export was initialized (affects logger setup in main).
    provider: Option<SdkTracerProvider>,
}

impl TelemetryGuard {
    /// Returns whether OTLP span export was successfully initialized.
    pub fn otel_enabled(&self) -> bool {
        self.provider.is_some()
    }

    /// Install `console` as the global `log` logger, showing records up to
    /// `console_level` (the CLI verbosity).
    ///
    /// With OTLP export on, every record also goes to `tracing`, so `log::*`
    /// calls are exported as span events at the subscriber's own level
    /// (`RUST_LOG`, `debug` by default) without changing what the console shows.
    pub fn install_logger(&self, console: Box<dyn log::Log>, console_level: log::LevelFilter) {
        let (logger, max_level): (Box<dyn log::Log>, _) = if self.otel_enabled() {
            let export_level = tracing::level_filters::LevelFilter::current().as_log();
            (
                Box::new(ConsoleAndExportLogger {
                    console,
                    export: LogTracer::new(),
                }),
                console_level.max(export_level),
            )
        } else {
            (console, console_level)
        };
        log::set_max_level(max_level);
        log::set_boxed_logger(logger).expect("Failed to initialize logger");
    }
}

/// Sends each `log` record to the console logger and to `tracing` for export;
/// each side applies its own level filter.
struct ConsoleAndExportLogger {
    console: Box<dyn log::Log>,
    export: LogTracer,
}

impl log::Log for ConsoleAndExportLogger {
    fn enabled(&self, metadata: &log::Metadata) -> bool {
        self.console.enabled(metadata) || self.export.enabled(metadata)
    }

    fn log(&self, record: &log::Record) {
        if self.console.enabled(record.metadata()) {
            self.console.log(record);
        }
        self.export.log(record);
    }

    fn flush(&self) {
        self.console.flush();
        self.export.flush();
    }
}

impl Drop for TelemetryGuard {
    fn drop(&mut self) {
        if let Some(provider) = self.provider.take() {
            // Force flush - this exports any buffered spans
            if let Err(e) = provider.force_flush() {
                log::warn!("Error flushing tracer provider: {}", e);
            }
            // Shutdown
            if let Err(e) = provider.shutdown() {
                log::warn!("Error shutting down tracer provider: {}", e);
            }
        }
    }
}

/// Initialize OpenTelemetry tracing if OTEL_EXPORTER_OTLP_ENDPOINT is set.
///
/// Returns a guard that must be kept alive for the duration of the program.
/// When the guard is dropped, it flushes all pending spans.
///
/// If OTEL_EXPORTER_OTLP_ENDPOINT is not set, returns a no-op guard and
/// tracing calls become no-ops.
pub fn init_telemetry() -> TelemetryGuard {
    // Presence of either the general or trace-specific endpoint env var enables OTLP export.
    init_telemetry_for_endpoint_presence(
        std::env::var_os("OTEL_EXPORTER_OTLP_ENDPOINT").is_some(),
        std::env::var_os("OTEL_EXPORTER_OTLP_TRACES_ENDPOINT").is_some(),
    )
}

fn init_telemetry_for_endpoint_presence(endpoint_set: bool, traces_endpoint_set: bool) -> TelemetryGuard {
    if endpoint_set || traces_endpoint_set {
        init_with_otlp()
    } else {
        init_noop()
    }
}

/// Initialize with OTLP exporter.
fn init_with_otlp() -> TelemetryGuard {
    // Build a blocking reqwest-backed HTTP exporter. Blocking is fine here
    // because the batch span processor runs in its own background thread.
    //
    // The exporter reads OTEL_EXPORTER_OTLP_TRACES_ENDPOINT (used verbatim)
    // or falls back to OTEL_EXPORTER_OTLP_ENDPOINT (with /v1/traces appended),
    // matching the OTEL spec — so we pass no explicit endpoint here.
    let exporter = match SpanExporter::builder()
        .with_http()
        .with_protocol(Protocol::HttpBinary)
        .build()
    {
        Ok(exp) => exp,
        Err(e) => {
            log::warn!("Failed to create OTLP exporter: {}. Falling back to no-op.", e);
            return init_noop();
        }
    };

    // Resource::builder() applies the SdkProvidedResourceDetector and
    // EnvResourceDetector, which already pick up OTEL_SERVICE_NAME and
    // OTEL_RESOURCE_ATTRIBUTES from the environment. Only default
    // service.name = "rewatch" when the user hasn't supplied their own.
    let mut resource_builder = Resource::builder();
    if std::env::var_os("OTEL_SERVICE_NAME").is_none() {
        resource_builder = resource_builder.with_service_name("rewatch");
    }
    let resource = resource_builder.build();

    let provider = SdkTracerProvider::builder()
        .with_batch_exporter(exporter)
        .with_resource(resource)
        .build();

    // Bridge the `tracing` crate into this provider.
    let tracer = provider.tracer("rewatch");
    let telemetry_layer = tracing_opentelemetry::layer().with_tracer(tracer);

    // Default to debug level so that diagnostic tracing::debug! events
    // (e.g. in the watcher) are captured as OTEL span events. This filter
    // only decides what is exported: the console keeps following the CLI
    // verbosity, see `TelemetryGuard::install_logger`.
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("debug"));

    // `set_global_default` rather than `init`: `init` would also make
    // `tracing_log::LogTracer` the global `log` logger, which replaces the
    // console logger and leaves `log::*` output to this subscriber's filter.
    tracing::subscriber::set_global_default(
        tracing_subscriber::registry().with(filter).with(telemetry_layer),
    )
    .expect("the tracing subscriber is installed once, at startup");

    TelemetryGuard {
        provider: Some(provider),
    }
}

/// Initialize with no-op tracing (no export).
fn init_noop() -> TelemetryGuard {
    // Don't set up any subscriber - let main.rs handle logging normally
    TelemetryGuard { provider: None }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn noop_guard_reports_otel_disabled() {
        let guard = init_noop();
        assert!(!guard.otel_enabled());
        // Explicit drop — must not panic with provider == None.
        drop(guard);
    }

    #[test]
    fn noop_guard_drops_cleanly_without_explicit_shutdown() {
        // Implicit drop at end of scope: exercises Drop with no provider.
        let _guard = init_noop();
    }

    #[test]
    fn init_telemetry_without_env_is_noop() {
        let guard = init_telemetry_for_endpoint_presence(false, false);
        assert!(
            !guard.otel_enabled(),
            "expected no-op guard when OTEL endpoint env vars are unset"
        );
    }
}
