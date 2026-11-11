//! Macro expansion of one file.
//!
//! Expansion works on the file's source text. A pass parses the text, lowers
//! the quotes it finds, type checks, and collects the edits the type checker
//! recorded at each macro use ([`super::discover`]). The edits are applied
//! and the next pass starts from the new text; a pass that records nothing
//! ends the expansion. The result is ordinary ReScript, which the compiler
//! then compiles like any file, with every position mapped back to the
//! source as written ([`SourceText::origin`]).
//!
//! Type checking again from the start after each round of edits is the
//! simple way to give generated code everything hand-written code gets
//! (inference, the frontend passes, later macro uses inside it). Its cost is
//! one type check per level of nesting, and only for files that use macros.

use std::sync::Arc;

use anyhow::Result;
use serde_json::{Value, json};

use crate::cmi::persistent_env::ModuleRegistry;
use crate::driver::{self, CompilerOptions, UserDiagnostic};
use crate::location::Position;
use crate::parser::ast::StructureItemDesc;
use crate::parser::{Parser, code_frame, module};
use crate::types::typemod::type_structure;

use super::MacroHost;
use super::discover::{ComptimeSite, Discovery, InstanceTable, MacroDiagnostic, MacroMode};
use super::edit::{Edit, LineTable, SourceText};
use super::quote;

/// More passes than any real nesting of macros and types needs.
const MAX_PASSES: usize = 64;

/// A diagnostic at characters `start..end` of `text`, reported against the
/// source as written.
fn diagnostic(
    original: &str,
    text: &SourceText,
    filename: &str,
    start: u32,
    end: u32,
    message: &str,
) -> anyhow::Error {
    let lines = LineTable::new(original);
    let start = text.origin(start);
    let end = text.origin(end).max(start + 1);
    let position = |offset: u32| {
        let (line, bol) = lines.line_of(offset);
        Position::new(crate::intern::StrIdx::from_raw(0), line, bol as i32, offset as i32)
    };
    UserDiagnostic::new(
        code_frame::format_error_with_intro(
            "We've found a bug for you!",
            filename,
            original,
            &position(start),
            &position(end),
            message,
        ),
        2,
    )
    .into()
}

/// Expand the macros of a file. Returns the expanded text; it is the source
/// unchanged ([`SourceText::is_edited`] false) when the file has a problem
/// the ordinary compilation reports better (a syntax error, a type error
/// before the first macro).
pub fn expand_source(
    source: &str,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    host: Arc<dyn MacroHost>,
) -> Result<SourceText> {
    let mut text = Arc::new(SourceText::new(source));
    let mut instances = InstanceTable::default();
    let base_dir = std::path::Path::new(filename)
        .parent()
        .map(|dir| dir.to_path_buf())
        .unwrap_or_default();

    for _pass in 0..MAX_PASSES {
        let mut parser = Parser::for_expanded_source(filename, text.text());
        let structure = module::parse_structure(&mut parser);
        if parser.has_errors() {
            if !text.is_edited() {
                return Ok(SourceText::new(source));
            }
            return Err(generated_syntax_error(&parser, &text, filename));
        }

        let quote_edits = quote::lowering_edits(parser.arena(), &structure, &text, module_name);
        if !quote_edits.is_empty() {
            text = Arc::new(text.apply(quote_edits));
            continue;
        }

        let opens = top_level_opens(&parser, &structure, &text);
        let mut frontend_output = String::new();
        let frontend = match driver::run_implementation_frontend(
            &mut parser,
            structure,
            text.text(),
            filename,
            options,
            &mut frontend_output,
        ) {
            Ok(frontend) => frontend,
            Err(error) => {
                if !text.is_edited() {
                    return Ok(SourceText::new(source));
                }
                return Err(error.context("in the macro-expanded source of this file"));
            }
        };
        let structure = frontend.structure;
        parser.arena_mut().reserve_typecheck_synthetic_capacity();
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let arena = parser.arena();

        let mut pass_options = options.clone();
        pass_options.experimental_let_unwrap = frontend.experimental_let_unwrap;
        let type_ctx = driver::fresh_type_context();
        let pass = {
            let (mut tctx, env) = driver::in_process_type_check_context(
                &type_ctx,
                arena,
                &pass_options,
                registry,
                module_name,
                &frontend.file_config,
                &frontend.frontend_warning_specs,
            );
            tctx.macro_mode = MacroMode::Discover(Box::new(Discovery::new(
                host.clone(),
                text.clone(),
                base_dir.clone(),
                std::mem::take(&mut instances),
            )));
            // The result is not used: what counts is what the pass found.
            let _ = type_structure(&mut tctx, &env, arena, &structure);
            match std::mem::replace(&mut tctx.macro_mode, MacroMode::Off) {
                MacroMode::Discover(discovery) => discovery.finish(),
                MacroMode::Off => unreachable!("the discovery pass state was taken"),
            }
        };
        drop(parser);
        instances = pass.instances;
        let mut edits = pass.edits;
        let mut errors = pass.errors;

        for site in &pass.comptime {
            match evaluate_comptime(site, &opens, filename, module_name, options, registry, &host) {
                Ok(literal) => edits.push(Edit::replace(site.start, site.end, format!("({literal})"))),
                Err(message) => errors.push(MacroDiagnostic {
                    start: site.start,
                    end: site.end,
                    message,
                }),
            }
        }

        if edits.is_empty() {
            let first_error = errors.iter().min_by_key(|error| error.start);
            let first_failed_item = pass.failed_items.iter().min().copied();
            return match (first_error, first_failed_item) {
                // A type error comes first: the ordinary compilation reports it.
                (Some(error), Some(failed)) if failed < error.start => Ok(unwrap_text(text)),
                (Some(error), _) => Err(diagnostic(
                    source,
                    &text,
                    filename,
                    error.start,
                    error.end,
                    &error.message,
                )),
                (None, _) => Ok(unwrap_text(text)),
            };
        }
        text = Arc::new(text.apply(edits));
    }
    Err(UserDiagnostic::new(
        format!(
            "{filename}: macro expansion did not finish after {MAX_PASSES} passes. A macro probably generates a call to itself.\n"
        ),
        2,
    )
    .into())
}

/// Move every position of a parse of the expanded text to where it is in
/// the source as written. Generated code takes the position of the macro
/// use it was generated for.
pub fn remap_positions(arena: &mut crate::parse_arena::ParseArena, text: &SourceText, original: &str) {
    let lines = LineTable::new(original);
    // An ordinary parse counts a column in UTF-16 code units; only text
    // with characters outside the BMP makes that differ from characters.
    let wide: Option<Vec<char>> = original
        .chars()
        .any(|ch| ch.len_utf16() > 1)
        .then(|| original.chars().collect());
    arena.remap_positions(|position| {
        if position.cnum < 0 {
            return;
        }
        let offset = text.origin(position.cnum as u32);
        let (line, bol) = lines.line_of(offset);
        let column = match &wide {
            Some(chars) => chars[bol as usize..offset as usize]
                .iter()
                .map(|ch| ch.len_utf16() as u32)
                .sum(),
            None => offset - bol,
        };
        position.line = line;
        position.bol = bol as i32;
        position.cnum = (bol + column) as i32;
    });
}

fn unwrap_text(text: Arc<SourceText>) -> SourceText {
    Arc::try_unwrap(text).unwrap_or_else(|shared| (*shared).clone())
}

fn generated_syntax_error(parser: &Parser<'_>, text: &SourceText, filename: &str) -> anyhow::Error {
    let mut output = String::from(
        "A macro generated code with a syntax error. The frame shows the expanded source.\n\n",
    );
    for diagnostic in parser.diagnostics().iter().take(1) {
        output.push_str(&code_frame::format_error(
            filename,
            text.text(),
            &diagnostic.start_pos,
            &diagnostic.end_pos,
            &diagnostic.explain_with_source(Some(text.text())),
        ));
    }
    UserDiagnostic::new(output, 2).into()
}

/// The `open` statements at the top level of the file, as source text:
/// `%comptime` expressions are compiled in their scope.
fn top_level_opens(
    parser: &Parser<'_>,
    structure: &[crate::parser::ast::StructureItem],
    text: &SourceText,
) -> Vec<String> {
    structure
        .iter()
        .filter(|item| matches!(item.pstr_desc, StructureItemDesc::Pstr_open(_)))
        .map(|item| {
            let location = parser.arena().to_location(item.pstr_loc);
            text.slice(location.loc_start.cnum.max(0) as u32, location.loc_end.cnum.max(0) as u32)
                .to_string()
        })
        .collect()
}

/// `%comptime(expr)`: compile `let value = expr` as a module of its own,
/// run it, and write the value back as a literal.
fn evaluate_comptime(
    site: &ComptimeSite,
    opens: &[String],
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    host: &Arc<dyn MacroHost>,
) -> Result<String, String> {
    if site.shape.get("k") == Some(&json!("other")) {
        return Err(format!(
            "%comptime: a value of type {} cannot be written as a literal. Supported: int, float, string, bool, unit, arrays, tuples, options, dicts and records of those.",
            site.shape.get("name").and_then(Value::as_str).unwrap_or("this type"),
        ));
    }
    let source = format!("{}\nlet value = {}\n", opens.join("\n"), site.expression);
    let comptime_module = format!("{module_name}__comptime");
    let comptime_file = std::path::Path::new(filename)
        .with_file_name(format!("{comptime_module}.res"))
        .to_string_lossy()
        .into_owned();
    let mut comptime_options = options.clone();
    comptime_options.source_filename = Some(comptime_file.clone());
    comptime_options.module_name = Some(comptime_module.clone());
    comptime_options.capture_intermediates = false;
    comptime_options.skip_js_render = false;
    comptime_options.js_output_targets = Vec::new();
    let compiled = driver::compile_source_in_process(
        &source,
        &comptime_file,
        &comptime_module,
        &comptime_options,
        registry,
        false,
    )
    .map_err(|error| {
        format!(
            "%comptime: the expression is compiled on its own, before this file, so it can only use other modules.\n{error:#}"
        )
    })?;

    let base_dir = std::path::Path::new(filename)
        .parent()
        .map(|dir| dir.to_path_buf())
        .unwrap_or_default();
    let mut answers = serde_json::Map::new();
    for _ in 0..1024 {
        let request = json!({
            "kind": "eval",
            "source": compiled.js_output,
            "shape": site.shape,
            "answers": answers,
        });
        let response = super::call_host(&**host, &request.to_string())
            .map_err(|message| format!("%comptime: the macro engine failed: {message}"))?;
        let response: Value = serde_json::from_str(&response)
            .map_err(|error| format!("%comptime: the macro engine returned invalid JSON: {error}"))?;
        if let Some(literal) = response.get("ok").and_then(Value::as_str) {
            return Ok(literal.to_string());
        }
        if let Some(message) = response.get("error").and_then(Value::as_str) {
            return Err(format!("%comptime: {message}"));
        }
        let Some(question) = response.get("need").and_then(Value::as_str) else {
            return Err("%comptime: the macro engine returned an unknown response.".into());
        };
        let answer = super::discover::answer_input(&base_dir, question)
            .unwrap_or_else(|| json!({ "__error": format!("`{question}` cannot be answered in %comptime.") }));
        answers.insert(question.to_string(), answer);
    }
    Err("%comptime: the expression asked more than 1024 questions.".into())
}
