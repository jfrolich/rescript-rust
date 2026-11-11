//! Typed imports from TypeScript: `%ts`.
//!
//! Three structure items import from a TypeScript module, and the types come
//! from the TypeScript checker instead of being written by hand:
//!
//! ```rescript
//! let {getUser, add: plus} = %ts("./api.ts")   // values
//! let main = %ts("./api.ts#default")           // one value under another name
//! type user = %ts("./api.ts#User")             // a type
//! module Api = %ts("./api.ts")                 // every export
//! module Counter = %ts("./api.ts#Counter")     // a class: `t`, `make`, statics
//! ```
//!
//! This is a frontend step. It runs before the external and builtin PPXs and
//! replaces each of those items by ordinary ReScript declarations: type
//! declarations and `external`s. Everything after it (the type checker, the
//! backend, editor tooling) sees plain ReScript, so an import behaves exactly
//! like a binding written by hand.
//!
//! The declarations come from the `rescript-ts-import` crate, which asks the
//! TypeScript checker (tsrs) for the type of each imported export and nothing
//! else. They are produced as source text and parsed into this file's arena;
//! every node of the result is located at the `%ts` item it replaces, so a
//! diagnostic about a generated declaration points at the import.

use crate::binary_ast::ppx::PpxError;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::Parser;
use crate::parser::ast::{
    Constant, CoreTypeDesc, ExpressionDesc, ModuleExprDesc, PatternDesc, Payload, RecFlag,
    Structure, StructureItem, StructureItemDesc,
};
use rescript_ts_import::{Files, Request, RequestKind, ValueImport};

pub use rescript_ts_import::{Gap, Note, Stats};

/// The name of the extension: `%ts(...)`.
const EXTENSION: &str = "ts";

/// One `%ts` item of a file and what it expanded to.
#[derive(Debug, Clone)]
pub struct Import {
    pub request: Request,
    /// Byte offsets of the structure item in the source.
    pub start: usize,
    pub end: usize,
    /// The ReScript declarations that replace the item.
    pub code: Result<String, String>,
    pub notes: Vec<Note>,
}

/// Every `%ts` item of a file with its expansion, for tools that show what an
/// import means (the playground, `bsc -dts-import`).
#[derive(Debug, Clone, Default)]
pub struct Report {
    pub imports: Vec<Import>,
    pub stats: Stats,
}

impl Report {
    /// The source with each `%ts` item replaced by its declarations.
    pub fn expanded_source(&self, source: &str) -> String {
        let mut out = String::with_capacity(source.len());
        let mut at = 0;
        for import in &self.imports {
            let Ok(code) = &import.code else { continue };
            if import.start < at || import.end > source.len() {
                continue;
            }
            out.push_str(&source[at..import.start]);
            // Keep the indentation of the item for the lines that follow.
            let line_start = source[..import.start].rfind('\n').map_or(0, |index| index + 1);
            let indent: String = source[line_start..import.start]
                .chars()
                .take_while(|ch| ch.is_whitespace())
                .collect();
            for (index, line) in code.trim_end().lines().enumerate() {
                if index > 0 {
                    out.push('\n');
                    out.push_str(&indent);
                }
                out.push_str(line);
            }
            at = import.end;
        }
        out.push_str(&source[at..]);
        out
    }
}

/// A `%ts` item found in the structure, before it is resolved.
struct Use {
    request: Request,
    loc: LocIdx,
}

/// The module and, after a `#`, the export a `%ts("...")` payload names.
/// A specifier may itself start with `#` (a Node subpath import), so only a
/// `#` after the first character separates the export.
fn payload_target(arena: &ParseArena, payload: &Payload) -> Option<(String, Option<String>)> {
    let Payload::PStr(items) = payload else { return None };
    let [item] = items.as_slice() else { return None };
    let StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else { return None };
    let ExpressionDesc::Pexp_constant(Constant::String(text)) = &arena.get_expr(eval.0).pexp_desc else {
        return None;
    };
    // The parser keeps one `char` per source byte; TypeScript wants the text.
    let text = crate::source_text::decode_internal_utf8_runs(text.semantic(arena));
    match text.rfind('#') {
        Some(index) if index > 0 && index + 1 < text.len() => {
            Some((text[..index].to_string(), Some(text[index + 1..].to_string())))
        }
        _ if text.is_empty() => None,
        _ => Some((text.to_string(), None)),
    }
}

const USAGE: &str = "`%ts` takes one string: a module, `%ts(\"./api.ts\")`, or one export of a module, `%ts(\"./api.ts#User\")`.";

/// The request a structure item makes, when it is a `%ts` import.
fn use_of_item(
    arena: &ParseArena,
    item: &StructureItem,
    scope: &[String],
) -> Result<Option<Use>, PpxError> {
    let at = |message: String| PpxError::at_loc(item.pstr_loc, message);
    let target = |payload: &Payload| payload_target(arena, payload).ok_or_else(|| at(USAGE.to_string()));
    let request = |module: String, kind: RequestKind| {
        Ok(Some(Use { request: Request { module, kind, scope: scope.to_vec() }, loc: item.pstr_loc }))
    };
    match &item.pstr_desc {
        StructureItemDesc::Pstr_value((RecFlag::Nonrecursive, bindings)) => {
            let [binding] = arena.vb_list(*bindings) else { return Ok(None) };
            let ExpressionDesc::Pexp_extension(extension) = &arena.get_expr(binding.pvb_expr).pexp_desc
            else {
                return Ok(None);
            };
            if arena.get_string(extension.0.txt) != EXTENSION {
                return Ok(None);
            }
            let (module, export) = target(&extension.1)?;
            let var = |pat| match &arena.get_pat(pat).ppat_desc {
                PatternDesc::Ppat_var(name) => Some(arena.get_string(name.txt).to_string()),
                _ => None,
            };
            match (&arena.get_pat(binding.pvb_pat).ppat_desc, export) {
                (PatternDesc::Ppat_record(record), None) if record.2.is_none() => {
                    let mut values = Vec::new();
                    for field in arena.pat_field_list(record.0) {
                        let export = arena.lident_last(field.lid.txt).to_string();
                        let Some(local) = var(field.pat) else {
                            return Err(at(format!(
                                "`{export}` must be bound to a name: `{{{export}}}` or `{{{export}: name}}`."
                            )));
                        };
                        values.push(ValueImport { export, local });
                    }
                    request(module, RequestKind::Values(values))
                }
                (PatternDesc::Ppat_var(name), Some(export)) => {
                    let local = arena.get_string(name.txt).to_string();
                    request(module, RequestKind::Values(vec![ValueImport { export, local }]))
                }
                (PatternDesc::Ppat_var(name), None) => {
                    let local = arena.get_string(name.txt);
                    Err(at(format!(
                        "Name what to import: `let {{{local}}} = %ts(\"{module}\")` for the export `{local}`, or `let {local} = %ts(\"{module}#exportName\")`."
                    )))
                }
                _ => Err(at(format!(
                    "A value import is `let {{a, b}} = %ts(\"{module}\")` or `let a = %ts(\"{module}#exportName\")`."
                ))),
            }
        }
        StructureItemDesc::Pstr_type(declarations) => {
            let is_import = |manifest: Option<crate::parse_arena::CoreTypeIdx>| {
                manifest.and_then(|manifest| match &arena.get_core_type(manifest).ptyp_desc {
                    CoreTypeDesc::Ptyp_extension(extension)
                        if arena.get_string(extension.0.txt) == EXTENSION =>
                    {
                        Some(&extension.1)
                    }
                    _ => None,
                })
            };
            let [declaration] = declarations.1.as_slice() else {
                if declarations.1.iter().any(|declaration| is_import(declaration.ptype_manifest).is_some()) {
                    return Err(at("A `%ts` type import stands alone: it cannot be part of a `type ... and ...` group.".to_string()));
                }
                return Ok(None);
            };
            let Some(payload) = is_import(declaration.ptype_manifest) else { return Ok(None) };
            let local = arena.get_string(declaration.ptype_name.txt).to_string();
            match target(payload)? {
                (module, Some(export)) => request(module, RequestKind::Type { export, local }),
                (module, None) => Err(at(format!(
                    "A type import names the exported type: `type {local} = %ts(\"{module}#TypeName\")`."
                ))),
            }
        }
        StructureItemDesc::Pstr_module(binding) => {
            let ModuleExprDesc::Pmod_extension(extension) = &arena.get_mod_expr(binding.pmb_expr).pmod_desc
            else {
                return Ok(None);
            };
            if arena.get_string(extension.0.txt) != EXTENSION {
                return Ok(None);
            }
            let local = arena.get_string(binding.pmb_name.txt).to_string();
            match target(&extension.1)? {
                (module, None) => request(module, RequestKind::Module { local }),
                (module, Some(export)) => request(module, RequestKind::Class { export, local }),
            }
        }
        _ => Ok(None),
    }
}

/// The structure of `module X = { ... }`, with the name it adds to the scope.
fn nested_structure<'a>(
    arena: &'a ParseArena,
    item: &StructureItem,
) -> Option<(String, &'a [StructureItem])> {
    let StructureItemDesc::Pstr_module(binding) = &item.pstr_desc else { return None };
    let mut module_expr = arena.get_mod_expr(binding.pmb_expr);
    while let ModuleExprDesc::Pmod_constraint(inner, _) = &module_expr.pmod_desc {
        module_expr = arena.get_mod_expr(*inner);
    }
    let ModuleExprDesc::Pmod_structure(items) = &module_expr.pmod_desc else { return None };
    Some((arena.get_string(binding.pmb_name.txt).to_string(), items.as_slice()))
}

/// The `%ts` items of a structure in source order, nested modules included.
fn collect_uses(
    arena: &ParseArena,
    items: &[StructureItem],
    scope: &mut Vec<String>,
    uses: &mut Vec<Use>,
) -> Result<(), PpxError> {
    for item in items {
        if let Some(found) = use_of_item(arena, item, scope)? {
            uses.push(found);
        } else if let Some((name, inner)) = nested_structure(arena, item) {
            scope.push(name);
            collect_uses(arena, inner, scope, uses)?;
            scope.pop();
        }
    }
    Ok(())
}

/// The absolute path TypeScript resolves module specifiers from.
fn importer_path(filename: &str) -> String {
    let path = std::path::Path::new(filename);
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().unwrap_or_default().join(path)
    };
    absolute.to_string_lossy().replace('\\', "/")
}

fn resolve_uses(
    uses: &[Use],
    filename: &str,
    files: &Files,
) -> Result<rescript_ts_import::Resolution, String> {
    let requests: Vec<Request> = uses.iter().map(|found| found.request.clone()).collect();
    rescript_ts_import::resolve(files, &importer_path(filename), &requests)
}

fn files_of(memory: Option<&[(String, String)]>) -> Files {
    match memory {
        Some(files) => Files::Memory(files.to_vec()),
        None => Files::Os,
    }
}

/// Parses generated declarations into `arena` and locates every node at `loc`.
fn parse_generated(
    parser: &mut Parser<'_>,
    code: &str,
    loc: LocIdx,
) -> Result<Vec<StructureItem>, PpxError> {
    // The parser reads one `char` per source byte.
    let text: String = code.bytes().map(char::from).collect();
    let arena = std::mem::take(parser.arena_mut());
    let first_location = arena.location_count();
    let mut generated = Parser::in_arena(arena, &text);
    let items = crate::parser::module::parse_structure(&mut generated);
    let failed = generated.has_errors();
    let mut arena = generated.into_arena();
    arena.relocate_locations_from(first_location, loc);
    *parser.arena_mut() = arena;
    if failed {
        return Err(PpxError::at_loc(
            loc,
            format!("The declarations generated for this import do not parse. This is a bug in the TypeScript import.\n{code}"),
        ));
    }
    Ok(items)
}

/// Replaces the `%ts` items of `items`, consuming one expansion per item in
/// the order `collect_uses` found them.
fn replace_uses(
    parser: &mut Parser<'_>,
    items: Vec<StructureItem>,
    expansions: &mut std::vec::IntoIter<(LocIdx, Result<String, String>)>,
    scope: &mut Vec<String>,
) -> Result<Vec<StructureItem>, PpxError> {
    let mut out = Vec::with_capacity(items.len());
    for mut item in items {
        if use_of_item(parser.arena(), &item, scope)?.is_some() {
            let Some((loc, code)) = expansions.next() else {
                return Err(PpxError::at_loc(item.pstr_loc, "No expansion for this import."));
            };
            let code = code.map_err(|message| PpxError::at_loc(loc, message))?;
            out.extend(parse_generated(parser, &code, loc)?);
            continue;
        }
        if let StructureItemDesc::Pstr_module(binding) = &item.pstr_desc {
            let name = parser.arena().get_string(binding.pmb_name.txt).to_string();
            let mut target = binding.pmb_expr;
            while let ModuleExprDesc::Pmod_constraint(inner, _) = &parser.arena().get_mod_expr(target).pmod_desc {
                target = *inner;
            }
            let inner = match &mut parser.arena_mut().get_mod_expr_mut(target).pmod_desc {
                ModuleExprDesc::Pmod_structure(inner) => Some(std::mem::take(&mut **inner)),
                _ => None,
            };
            if let Some(inner) = inner {
                scope.push(name);
                let replaced = replace_uses(parser, inner, expansions, scope)?;
                scope.pop();
                if let ModuleExprDesc::Pmod_structure(slot) =
                    &mut parser.arena_mut().get_mod_expr_mut(target).pmod_desc
                {
                    **slot = replaced;
                }
            }
        }
        let _ = &mut item;
        out.push(item);
    }
    Ok(out)
}

/// The frontend step: every `%ts` item of `structure` becomes the ReScript
/// declarations it stands for. `memory_files` replaces the file system with
/// the given TypeScript files (tests, the playground).
pub fn expand_structure(
    parser: &mut Parser<'_>,
    structure: Structure,
    source: &str,
    filename: &str,
    memory_files: Option<&[(String, String)]>,
) -> Result<Structure, PpxError> {
    // Nearly every file has no import: one scan of the text settles that.
    if !source.contains("%ts") {
        return Ok(structure);
    }
    let mut uses = Vec::new();
    collect_uses(parser.arena(), &structure, &mut Vec::new(), &mut uses)?;
    let Some(first) = uses.first() else { return Ok(structure) };
    let resolution = resolve_uses(&uses, filename, &files_of(memory_files))
        .map_err(|message| PpxError::at_loc(first.loc, message))?;
    let expansions: Vec<(LocIdx, Result<String, String>)> = uses
        .iter()
        .zip(resolution.expansions)
        .map(|(found, expansion)| (found.loc, expansion.map(|expansion| expansion.code())))
        .collect();
    replace_uses(parser, structure, &mut expansions.into_iter(), &mut Vec::new())
}

/// What the `%ts` items of `source` expand to, without compiling the file.
pub fn report(
    source: &str,
    filename: &str,
    memory_files: Option<&[(String, String)]>,
) -> Result<Report, String> {
    if !source.contains("%ts") {
        return Ok(Report::default());
    }
    let mut parser = Parser::new(filename, source);
    let structure = crate::parser::module::parse_structure(&mut parser);
    let arena = parser.arena();
    let mut uses = Vec::new();
    collect_uses(arena, &structure, &mut Vec::new(), &mut uses)
        .map_err(|error| error.message_text().to_string())?;
    if uses.is_empty() {
        return Ok(Report::default());
    }
    let resolution = resolve_uses(&uses, filename, &files_of(memory_files))?;
    let imports = uses
        .into_iter()
        .zip(resolution.expansions)
        .map(|(found, expansion)| {
            let (code, notes) = match expansion {
                Ok(expansion) => (Ok(expansion.code()), expansion.notes),
                Err(message) => (Err(message), Vec::new()),
            };
            Import {
                request: found.request,
                start: arena.loc_start(found.loc).cnum.max(0) as usize,
                end: arena.loc_end(found.loc).cnum.max(0) as usize,
                code,
                notes,
            }
        })
        .collect();
    Ok(Report { imports, stats: resolution.stats })
}
