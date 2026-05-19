//! Optional OpenTelemetry setup for rewatch.
//!
//! OTLP export is enabled only when `OTEL_EXPORTER_OTLP_ENDPOINT` or
//! `OTEL_EXPORTER_OTLP_TRACES_ENDPOINT` is set. Otherwise tracing stays no-op.
//! This keeps beta builds opt-in: no telemetry is configured, exported, or
//! flushed unless the caller explicitly provides an OTLP endpoint.

use opentelemetry::trace::TracerProvider as _;
use opentelemetry_otlp::{Protocol, SpanExporter, WithExportConfig};
use opentelemetry_sdk::Resource;
use opentelemetry_sdk::trace::SdkTracerProvider;
use tracing_subscriber::EnvFilter;
use tracing_subscriber::fmt;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

pub struct TelemetryGuard {
    provider: Option<SdkTracerProvider>,
    otel_enabled: bool,
}

impl TelemetryGuard {
    pub fn otel_enabled(&self) -> bool {
        self.otel_enabled
    }
}

impl Drop for TelemetryGuard {
    fn drop(&mut self) {
        if let Some(provider) = self.provider.take() {
            if let Err(err) = provider.force_flush() {
                log::warn!("Error flushing tracer provider: {}", err);
            }
            if let Err(err) = provider.shutdown() {
                log::warn!("Error shutting down tracer provider: {}", err);
            }
        }
    }
}

pub fn init_telemetry() -> TelemetryGuard {
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

fn init_with_otlp() -> TelemetryGuard {
    let exporter = match SpanExporter::builder()
        .with_http()
        .with_protocol(Protocol::HttpBinary)
        .build()
    {
        Ok(exporter) => exporter,
        Err(err) => {
            log::warn!("Failed to create OTLP exporter: {}. Falling back to no-op.", err);
            return init_noop();
        }
    };

    let mut resource_builder = Resource::builder();
    if std::env::var_os("OTEL_SERVICE_NAME").is_none() {
        resource_builder = resource_builder.with_service_name("rewatch");
    }
    let resource = resource_builder.build();

    let provider = SdkTracerProvider::builder()
        .with_batch_exporter(exporter)
        .with_resource(resource)
        .build();
    let tracer = provider.tracer("rewatch");
    let telemetry_layer = tracing_opentelemetry::layer().with_tracer(tracer);

    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    let fmt_layer = fmt::layer().with_writer(std::io::stderr);

    tracing_subscriber::registry()
        .with(filter)
        .with(telemetry_layer)
        .with(fmt_layer)
        .init();

    TelemetryGuard {
        provider: Some(provider),
        otel_enabled: true,
    }
}

fn init_noop() -> TelemetryGuard {
    TelemetryGuard {
        provider: None,
        otel_enabled: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn noop_guard_reports_otel_disabled() {
        let guard = init_noop();
        assert!(!guard.otel_enabled());
    }

    #[test]
    fn init_telemetry_without_env_is_noop() {
        let guard = init_telemetry_for_endpoint_presence(false, false);
        assert!(!guard.otel_enabled());
    }
}
