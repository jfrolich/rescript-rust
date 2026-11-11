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
/// source as written. One in generated code is reported at the macro use,
/// with a note about the generated code; `in_expansion` asks for that note
/// wherever the diagnostic is.
fn diagnostic(
    intro: &str,
    original: &str,
    text: &SourceText,
    filename: &str,
    (start, end): (u32, u32),
    in_expansion: bool,
    message: &str,
) -> anyhow::Error {
    let generated = text.generated_code(start, end).or_else(|| {
        (in_expansion && text.is_edited()).then(|| super::edit::GeneratedCode {
            start,
            end: end.max(start + 1),
            description: None,
            quote: None,
        })
    });
    let note = generated
        .map(|generated| {
            super::report::generated_code_note(
                text,
                &generated,
                false,
                driver::read_in_process_source,
            )
        })
        .unwrap_or_default();
    let (start, end) = text.original_range(start, end.max(start + 1));
    original_diagnostic(intro, original, filename, (start, end), &note, message)
}

/// A diagnostic at characters `start..end` of the source as written.
/// `note` goes between the code frame and the message.
fn original_diagnostic(
    intro: &str,
    original: &str,
    filename: &str,
    (start, end): (u32, u32),
    note: &str,
    message: &str,
) -> anyhow::Error {
    let lines = LineTable::new(original);
    let position = |offset: u32| {
        let (line, bol) = lines.line_of(offset);
        Position::new(
            crate::intern::StrIdx::from_raw(0),
            line,
            bol as i32,
            offset as i32,
        )
    };
    // Every line of the message is indented like the first.
    let mut body = String::from(note.strip_prefix("  ").unwrap_or(note));
    for (index, line) in message.lines().enumerate() {
        if index > 0 || !body.is_empty() {
            body.push_str(if line.is_empty() { "\n" } else { "\n  " });
        }
        body.push_str(line);
    }
    // A note ends with the blank line after its frame.
    let body = body.replace("\n\n\n", "\n\n");
    UserDiagnostic::new(
        code_frame::format_error_with_intro(
            intro,
            filename,
            original,
            &position(start),
            &position(end.max(start + 1)),
            &body,
        ),
        2,
    )
    .into()
}

const BUG: &str = "We've found a bug for you!";

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
    let mut unfinished: Option<(u32, u32)> = None;
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
            return Err(generated_syntax_error(&parser, &text, source, filename));
        }

        let quote_edits = quote::lowering_edits(
            parser.arena(),
            &structure,
            &text,
            source,
            filename,
            module_name,
        );
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
                MacroMode::Off | MacroMode::Expanded { .. } => {
                    unreachable!("the discovery pass state was taken")
                }
            }
        };
        drop(parser);
        instances = pass.instances;
        let mut edits = pass.edits;
        let mut errors = pass.errors;

        for site in &pass.comptime {
            match evaluate_comptime(
                site,
                &opens,
                filename,
                module_name,
                options,
                registry,
                &host,
            ) {
                Ok(literal) => {
                    edits.push(Edit::replace(site.start, site.end, format!("({literal})")))
                }
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
                    BUG,
                    source,
                    &text,
                    filename,
                    (error.start, error.end),
                    false,
                    &error.message,
                )),
                (None, _) => Ok(unwrap_text(text)),
            };
        }
        // The macro use that is still expanding when the passes run out.
        if let Some(edit) = edits
            .iter()
            .filter(|edit| edit.end > edit.start)
            .min_by_key(|edit| edit.start)
        {
            unfinished = Some(text.original_range(edit.start, edit.end));
        }
        text = Arc::new(text.apply(edits));
    }
    let message = format!(
        "Macro expansion did not finish after {MAX_PASSES} passes.\nA macro probably generates a use of itself."
    );
    Err(original_diagnostic(
        BUG,
        source,
        filename,
        unfinished.unwrap_or((0, 0)),
        "",
        &message,
    ))
}

/// Move every position of a parse of the expanded text to where it is in
/// the source as written. Generated code takes the position of the macro
/// use it was generated for: a location that starts or ends in generated
/// code covers that use.
pub fn remap_positions(
    arena: &mut crate::parse_arena::ParseArena,
    text: &SourceText,
    original: &str,
) {
    let lines = LineTable::new(original);
    // An ordinary parse counts a column in UTF-16 code units; only text
    // with characters outside the BMP makes that differ from characters.
    let wide: Option<Vec<char>> = original
        .chars()
        .any(|ch| ch.len_utf16() > 1)
        .then(|| original.chars().collect());
    let place = |position: &mut Position, offset: u32| {
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
    };
    let mut offsets = Vec::with_capacity(arena.position_count());
    let added = arena.remap_positions(
        |position| {
            offsets.push(position.cnum.max(0) as u32);
            if position.cnum >= 0 {
                place(position, text.origin(position.cnum as u32));
            }
        },
        |start, end| {
            if start.cnum < 0 || end.cnum <= start.cnum {
                return None;
            }
            let (from, to) = (start.cnum as u32, end.cnum as u32);
            let range = text.original_range(from, to);
            if range == (text.origin(from), text.origin(to)) {
                return None;
            }
            let (mut new_start, mut new_end) = (*start, *end);
            place(&mut new_start, range.0);
            place(&mut new_end, range.1);
            Some((new_start, new_end))
        },
    );
    for (index, from) in added {
        debug_assert_eq!(index as usize, offsets.len());
        offsets.push(offsets[from as usize]);
    }
    arena.set_expansion(Arc::new(super::edit::Expansion {
        text: text.clone(),
        offsets,
    }));
}

fn unwrap_text(text: Arc<SourceText>) -> SourceText {
    Arc::try_unwrap(text).unwrap_or_else(|shared| (*shared).clone())
}

fn generated_syntax_error(
    parser: &Parser<'_>,
    text: &SourceText,
    original: &str,
    filename: &str,
) -> anyhow::Error {
    let Some(error) = parser.diagnostics().first() else {
        return UserDiagnostic::new(
            format!("{filename}: a macro generated code that does not parse.\n"),
            2,
        )
        .into();
    };
    diagnostic(
        "Syntax error!",
        original,
        text,
        filename,
        (
            error.start_pos.cnum.max(0) as u32,
            error.end_pos.cnum.max(0) as u32,
        ),
        true,
        &error.explain_with_source(Some(text.text())),
    )
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
            text.slice(
                location.loc_start.cnum.max(0) as u32,
                location.loc_end.cnum.max(0) as u32,
            )
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
            site.shape
                .get("name")
                .and_then(Value::as_str)
                .unwrap_or("this type"),
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
        // What the report of the expression's own compilation says, without
        // its header: the expression is in this file, not in one of its own.
        let report = format!("{error:#}");
        let said = report
            .find(&comptime_file)
            .and_then(|at| report[at..].find("\n\n").map(|blank| &report[at + blank..]))
            .unwrap_or(&report);
        let said: Vec<&str> = said.trim_matches('\n').lines().map(str::trim_end).collect();
        let indent = said
            .iter()
            .filter(|line| !line.is_empty())
            .map(|line| line.len() - line.trim_start().len())
            .min()
            .unwrap_or(0);
        let said: Vec<&str> = said.iter().map(|line| line.get(indent..).unwrap_or("")).collect();
        format!(
            "{}\n\n%comptime compiles its expression on its own, before the rest of this file: it can use other modules, not what this file defines.",
            said.join("\n")
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
        let response: Value = serde_json::from_str(&response).map_err(|error| {
            format!("%comptime: the macro engine returned invalid JSON: {error}")
        })?;
        if let Some(literal) = response.get("ok").and_then(Value::as_str) {
            return Ok(literal.to_string());
        }
        if let Some(message) = response.get("error").and_then(Value::as_str) {
            return Err(
                if response.get("exception").and_then(Value::as_bool) == Some(true) {
                    format!("The expression of %comptime raised an exception:\n{message}")
                } else {
                    format!("%comptime: {message}")
                },
            );
        }
        let Some(question) = response.get("need").and_then(Value::as_str) else {
            return Err("%comptime: the macro engine returned an unknown response.".into());
        };
        let answer = super::discover::answer_input(&base_dir, question).unwrap_or_else(
            || json!({ "__error": format!("`{question}` cannot be answered in %comptime.") }),
        );
        answers.insert(question.to_string(), answer);
    }
    Err("%comptime: the expression asked more than 1024 questions.".into())
}
