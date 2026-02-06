//! Shared test helpers for parser modules.

use crate::parser::state::Parser;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// Default timeout for parsing operations (5 seconds - generous for ms-scale ops).
pub(crate) const PARSE_TIMEOUT: Duration = Duration::from_secs(5);

fn preview_source(source: &str) -> String {
    const MAX_PREVIEW_LEN: usize = 100;
    let mut chars = source.chars();
    let preview: String = chars.by_ref().take(MAX_PREVIEW_LEN).collect();
    if chars.next().is_some() {
        format!("{preview}...")
    } else {
        preview
    }
}

/// Parse using a fresh parser in a separate thread and fail fast on hangs.
pub(crate) fn parse_with_timeout<T, F>(source: &str, parse: F) -> T
where
    T: Send + 'static,
    F: FnOnce(&mut Parser<'_>) -> T + Send + 'static,
{
    let source_owned = source.to_string();
    let source_for_error = source_owned.clone();
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let mut parser = Parser::new("test.res", &source_owned);
        let parsed = parse(&mut parser);
        drop(tx.send(parsed));
    });

    match rx.recv_timeout(PARSE_TIMEOUT) {
        Ok(result) => result,
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!(
                "Parser timed out after {:?} for input: {}",
                PARSE_TIMEOUT,
                preview_source(&source_for_error)
            )
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!(
                "Parser thread panicked for input: {}",
                preview_source(&source_for_error)
            )
        }
    }
}
