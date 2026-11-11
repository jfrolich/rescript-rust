//! The macro engine of native builds: QuickJS, linked into the compiler.
//!
//! One engine per thread that expands macros, created on first use. QuickJS
//! has no file system and no network; `host.js` hides the clock and random
//! numbers from macro code.

use std::cell::RefCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use rquickjs::{Context, Function, Runtime};

use super::{HOST_JS, MacroHost};

/// The compiled JavaScript of a module, by module name.
pub type ModuleSources = Arc<dyn Fn(&str) -> Option<String> + Send + Sync>;

/// Memory one engine may use.
const MEMORY_LIMIT: usize = 512 * 1024 * 1024;
/// Time one macro call may take.
const TIME_LIMIT: Duration = Duration::from_secs(20);

static NEXT_HOST: AtomicU64 = AtomicU64::new(1);

/// A [`MacroHost`] that runs macros in QuickJS.
pub struct QuickJsHost {
    id: u64,
    /// Bumped when compiled modules change, so engines drop what they loaded.
    generation: AtomicU64,
    sources: ModuleSources,
}

struct Engine {
    host: u64,
    generation: u64,
    deadline: Arc<AtomicU64>,
    started: Instant,
    context: Context,
    // Dropped after the context.
    _runtime: Runtime,
}

thread_local! {
    static ENGINE: RefCell<Option<Engine>> = const { RefCell::new(None) };
}

impl QuickJsHost {
    pub fn new(sources: ModuleSources) -> Self {
        QuickJsHost {
            id: NEXT_HOST.fetch_add(1, Ordering::Relaxed),
            generation: AtomicU64::new(0),
            sources,
        }
    }

    /// Forget the modules engines have loaded: their JavaScript changed.
    pub fn invalidate(&self) {
        self.generation.fetch_add(1, Ordering::Relaxed);
    }

    fn engine(&self, generation: u64) -> Result<Engine, String> {
        let runtime = Runtime::new().map_err(|error| error.to_string())?;
        runtime.set_memory_limit(MEMORY_LIMIT);
        runtime.set_max_stack_size(4 * 1024 * 1024);
        let started = Instant::now();
        let deadline = Arc::new(AtomicU64::new(u64::MAX));
        let interrupt_deadline = deadline.clone();
        runtime.set_interrupt_handler(Some(Box::new(move || {
            started.elapsed().as_millis() as u64 > interrupt_deadline.load(Ordering::Relaxed)
        })));
        let context = Context::full(&runtime).map_err(|error| error.to_string())?;
        let sources = self.sources.clone();
        context
            .with(|ctx| -> rquickjs::Result<()> {
                let source = Function::new(ctx.clone(), move |name: String| -> Option<String> {
                    sources(&name)
                })?;
                ctx.globals().set("__rescript_macro_source", source)?;
                ctx.eval::<(), _>(HOST_JS)?;
                Ok(())
            })
            .map_err(|error| format!("cannot start the macro engine: {error}"))?;
        Ok(Engine {
            host: self.id,
            generation,
            deadline,
            started,
            context,
            _runtime: runtime,
        })
    }
}

impl MacroHost for QuickJsHost {
    fn call(&self, request: &str) -> Result<String, String> {
        let generation = self.generation.load(Ordering::Relaxed);
        ENGINE.with(|slot| {
            let mut slot = slot.borrow_mut();
            let reuse = matches!(&*slot, Some(engine) if engine.host == self.id && engine.generation == generation);
            if !reuse {
                *slot = None;
                *slot = Some(self.engine(generation)?);
            }
            let engine = slot.as_ref().expect("the engine was just created");
            engine.deadline.store(
                (engine.started.elapsed() + TIME_LIMIT).as_millis() as u64,
                Ordering::Relaxed,
            );
            let result = engine.context.with(|ctx| -> Result<String, String> {
                let call: Function = ctx
                    .globals()
                    .get("__rescript_macro_call")
                    .map_err(|error| error.to_string())?;
                call.call::<_, String>((request,)).map_err(|error| {
                    let thrown = ctx.catch();
                    match thrown.as_exception().and_then(|exception| exception.message()) {
                        Some(message) if message.contains("interrupted") => format!(
                            "a macro ran for more than {} seconds and was stopped",
                            TIME_LIMIT.as_secs()
                        ),
                        Some(message) => message,
                        None => error.to_string(),
                    }
                })
            });
            engine.deadline.store(u64::MAX, Ordering::Relaxed);
            if result.is_err() {
                // The engine may be out of memory or mid-call: start over.
                *slot = None;
            }
            result
        })
    }
}
