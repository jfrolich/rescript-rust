//! Typed TypeScript imports for ReScript.
//!
//! A ReScript file names what it wants from a TypeScript module:
//!
//! ```rescript
//! let {getUser, add} = %ts("./api.ts")
//! type user = %ts("./api.ts#User")
//! module Api = %ts("./api.ts")
//! ```
//!
//! and [`resolve`] answers with the ReScript declarations each of those
//! stands for: type declarations and `external`s whose types come from the
//! TypeScript checker (tsrs, the Rust port of the TypeScript compiler).
//!
//! TypeScript work is kept to what the imports need. The program's only root
//! is a virtual file importing the named modules, so the files loaded are
//! those modules and what they import. No file is type checked: the checker is
//! asked for the type of each requested export, and it resolves the
//! declarations that type depends on and nothing more.

mod convert;
mod model;
mod session;

use tsrs_ast::{Symbol, SymbolFlags};
use tsrs_compiler::Context;
use tsrs_core::P;

pub use convert::{Gap, Note};
pub use model::{Item, lower_ident, print_items};
pub use session::Files;

use convert::Converter;
use session::Session;

/// A value to import: `let {export: local} = %ts("module")`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueImport {
    pub export: String,
    pub local: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RequestKind {
    /// `let {a, b: c} = %ts("module")`
    Values(Vec<ValueImport>),
    /// `type local = %ts("module#Export")`
    Type { export: String, local: String },
    /// `module Local = %ts("module")`: every export.
    Module { local: String },
    /// `module Local = %ts("module#Class")`: a class as a module with
    /// `type t`, `make` and its static members.
    Class { export: String, local: String },
}

/// One `%ts` use in a ReScript file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    /// The module specifier as written.
    pub module: String,
    pub kind: RequestKind,
    /// The ReScript modules the use is nested in, outermost first.
    pub scope: Vec<String>,
}

/// What a request expands to.
#[derive(Clone, Debug)]
pub struct Expansion {
    pub items: Vec<Item>,
    /// Where the ReScript types say less than the TypeScript ones.
    pub notes: Vec<Note>,
}

impl Expansion {
    /// The ReScript source that replaces the `%ts` structure item.
    pub fn code(&self) -> String {
        print_items(&self.items)
    }
}

/// How much TypeScript was looked at.
#[derive(Clone, Debug, Default)]
pub struct Stats {
    /// Files parsed and bound, library files included.
    pub files: usize,
    /// Files among those that are TypeScript's own `lib.*.d.ts`.
    pub lib_files: usize,
    /// Lines in the non-library files.
    pub lines: usize,
    /// Types the checker created to answer the requests.
    pub types: usize,
    /// The non-library files, for dependency tracking.
    pub inputs: Vec<String>,
    /// The `tsconfig.json` whose options were used.
    pub tsconfig: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Resolution {
    /// One result per request, in order.
    pub expansions: Vec<Result<Expansion, String>>,
    pub stats: Stats,
}

/// Resolves every `%ts` use of one ReScript file.
///
/// `importer` is the absolute path of the ReScript file; module specifiers
/// are resolved from its directory, as TypeScript resolves an import.
pub fn resolve(files: &Files, importer: &str, requests: &[Request]) -> Result<Resolution, String> {
    let mut modules: Vec<String> = Vec::new();
    for request in requests {
        if !modules.contains(&request.module) {
            modules.push(request.module.clone());
        }
    }
    let session = Session::open(files, importer, &modules)?;
    let program = session.program;
    let context = Context::default();
    let mut handle = program.get_type_checker(&context);
    let checker = &mut *handle;
    let types_before = checker.type_count as usize;

    // The module symbol behind each specifier, or why there is none.
    let module_symbols: Vec<Result<P<Symbol>, String>> = modules
        .iter()
        .zip(&session.specifiers)
        .map(|(module, &specifier)| {
            checker
                .resolve_external_module_name_exported(specifier, None)
                .ok_or_else(|| format!("TypeScript cannot find the module \"{module}\" from {importer}"))
        })
        .collect();

    let mut converter = Converter::new(checker, program);
    let mut expansions = Vec::with_capacity(requests.len());
    for request in requests {
        let index = modules.iter().position(|module| *module == request.module).unwrap_or(0);
        let expansion = match &module_symbols[index] {
            Err(message) => Err(message.clone()),
            Ok(module_symbol) => expand(&mut converter, *module_symbol, request),
        };
        expansions.push(expansion);
    }
    let types = (converter.c.type_count as usize).saturating_sub(types_before);

    let mut stats = Stats { types, tsconfig: session.tsconfig.clone(), ..Stats::default() };
    for &file in program.source_files() {
        stats.files += 1;
        if program.is_source_file_default_library(file.path()) {
            stats.lib_files += 1;
        } else if file.path() != session.root.path() {
            stats.lines += file.text().lines().count();
            stats.inputs.push(file.file_name().to_string());
        }
    }
    Ok(Resolution { expansions, stats })
}

fn find_export(
    converter: &mut Converter<'_>,
    module_symbol: P<Symbol>,
    module: &str,
    export: &str,
) -> Result<P<Symbol>, String> {
    let exports = converter.c.get_exports_of_module_exported(module_symbol);
    match exports.iter().find(|symbol| symbol.name() == export) {
        Some(&symbol) => Ok(converter.c.skip_alias(symbol)),
        None => {
            let mut names: Vec<&str> = exports.iter().map(|symbol| symbol.name()).collect();
            names.sort_unstable();
            Err(format!(
                "\"{module}\" has no export named `{export}`. It exports: {}.",
                if names.is_empty() { "nothing".to_string() } else { names.join(", ") }
            ))
        }
    }
}

fn expand(
    converter: &mut Converter<'_>,
    module_symbol: P<Symbol>,
    request: &Request,
) -> Result<Expansion, String> {
    let module = request.module.as_str();
    converter.begin_request(&request.scope);
    let mut items: Vec<Item> = Vec::new();
    match &request.kind {
        RequestKind::Values(values) => {
            let mut externals = Vec::new();
            for value in values {
                let symbol = find_export(converter, module_symbol, module, &value.export)?;
                externals.extend(converter.value(module, &value.export, &value.local, symbol)?);
            }
            items.extend(converter.take_types());
            items.extend(externals);
        }
        RequestKind::Type { export, local } => {
            let symbol = find_export(converter, module_symbol, module, export)?;
            converter.named_type(module, export, Some(local), symbol)?;
            items.extend(converter.take_types());
        }
        RequestKind::Class { export, local } => {
            let symbol = find_export(converter, module_symbol, module, export)?;
            if !symbol.flags().intersects(SymbolFlags::Class) {
                return Err(format!(
                    "`{export}` in \"{module}\" is not a class. `module {local} = %ts(\"{module}#{export}\")` imports a class; use `%ts(\"{module}\")` for the whole module."
                ));
            }
            let class = converter.class_module(module, export, local, symbol);
            items.extend(converter.take_types());
            items.push(class);
        }
        RequestKind::Module { local } => {
            // The declarations live inside the generated module.
            let mut scope = request.scope.clone();
            scope.push(local.clone());
            converter.begin_request(&scope);
            let mut exports = converter.c.get_exports_of_module_exported(module_symbol);
            exports.sort_by_key(|symbol| {
                (symbol.declarations().first().map(|node| node.pos()), symbol.name())
            });
            // Types first, so each keeps its own name; then the values.
            let exports: Vec<(&str, P<Symbol>)> = exports
                .iter()
                .map(|&export_symbol| (export_symbol.name(), converter.c.skip_alias(export_symbol)))
                .collect();
            for &(export, symbol) in &exports {
                let flags = symbol.flags();
                if flags.intersects(SymbolFlags::Type) && !flags.intersects(SymbolFlags::Class) {
                    // An enum is both: its type is imported, its object is not.
                    converter.named_type(module, export, None, symbol)?;
                }
            }
            let mut values = Vec::new();
            for &(export, symbol) in &exports {
                let flags = symbol.flags();
                if flags.intersects(SymbolFlags::Class) {
                    values.push(converter.class_module(module, export, &model::upper_ident(export), symbol));
                } else if flags.intersects(SymbolFlags::Module) {
                    converter.skipped_export(export, "a namespace is not imported; import what it contains from its own module");
                } else if flags.intersects(SymbolFlags::Enum) {
                    converter.skipped_export(export, "the enum's type is imported; its object is not, write the constructors instead");
                } else if flags.intersects(SymbolFlags::Value) {
                    values.extend(converter.value(module, export, &lower_ident(export), symbol)?);
                }
            }
            let mut inner = converter.take_types();
            inner.extend(values);
            items.push(Item::Module(local.clone(), inner));
        }
    }
    Ok(Expansion { items, notes: converter.take_notes() })
}
