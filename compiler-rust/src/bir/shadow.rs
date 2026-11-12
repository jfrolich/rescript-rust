//! Shadow oracles. `lambda-bridge` (S2.2) checks the bridge; `lambda-norm`
//! (S4.1) checks the normalising rules against `LamArena`'s constructors.
//! Neither replaces a pipeline stage: both opt-in modes retain the legacy
//! output until a later stage takes over.
use super::bridge::{export_lambda, import_lambda};
use crate::lambda::arena::{Lam, LamArena};
use std::hash::{Hash, Hasher};
use std::io::Write;

/// Backend migration mode. The default remains the legacy implementation.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum BackendMode {
    /// No bridge, validation, comparison, or reporting work.
    #[default]
    Legacy,
    /// Exercise supported bridges; lowering still uses the legacy backend in S2.2.
    New,
    /// Compare the bridge round trip and retain legacy output.
    Check,
}
impl BackendMode {
    /// Read `RESCRIPT_BACKEND` once when constructing compiler options. An absent
    /// or unrecognized value leaves the legacy backend selected.
    pub fn from_env() -> Self {
        match std::env::var("RESCRIPT_BACKEND").as_deref() {
            Ok("check") => Self::Check,
            Ok("new") => Self::New,
            _ => Self::Legacy,
        }
    }
}

/// One unit's shadow result. Files contain no source or generated program text.
#[derive(serde::Serialize)]
struct UnitReport<'a> {
    unit: &'a str,
    stage: &'static str,
    identical: bool,
    unsupported: Option<&'static str>,
    /// `lambda-norm`: smart-constructor calls replayed and rows fired.
    #[serde(skip_serializing_if = "Option::is_none")]
    norm: Option<NormReport>,
    /// `lambda-alias`: binders compared with the legacy identifier table,
    /// per kind of fact.
    #[serde(skip_serializing_if = "Option::is_none")]
    facts: Option<std::collections::BTreeMap<&'static str, u64>>,
}

#[derive(serde::Serialize)]
struct NormReport {
    calls: u64,
    replayed: std::collections::BTreeMap<&'static str, u32>,
    renormalised: std::collections::BTreeMap<&'static str, u32>,
    #[serde(skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    rules: std::collections::BTreeMap<&'static str, u64>,
    compared: u64,
}

fn report(
    unit: &str,
    stage: &'static str,
    unsupported: Option<&'static str>,
    norm: Option<NormReport>,
) -> anyhow::Result<()> {
    report_with_facts(unit, stage, unsupported, norm, None)
}

fn report_with_facts(
    unit: &str,
    stage: &'static str,
    unsupported: Option<&'static str>,
    norm: Option<NormReport>,
    facts: Option<std::collections::BTreeMap<&'static str, u64>>,
) -> anyhow::Result<()> {
    let Some(directory) = std::env::var_os("RESCRIPT_BACKEND_STATS") else {
        return Ok(());
    };
    let directory = std::path::Path::new(&directory);
    std::fs::create_dir_all(directory)?;
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    unit.hash(&mut hash);
    let directory = directory.join(format!("{:016x}", hash.finish()));
    std::fs::create_dir_all(&directory)?;
    // Immutable outcome files: repeated modes/processes never overwrite a
    // fallback with success. The collector groups them by source unit and
    // keeps a fallback if any invocation was unsupported.
    let outcome = unsupported.unwrap_or("identical").replace(' ', "_");
    // The bridge stage keeps its file names; later stages prefix theirs.
    let path = if stage == "lambda-bridge" {
        directory.join(format!("{outcome}.json"))
    } else {
        directory.join(format!("{stage}.{outcome}.json"))
    };
    let mut file = match std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
    {
        Ok(file) => file,
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => return Ok(()),
        Err(error) => return Err(error.into()),
    };
    let data = serde_json::to_vec(&UnitReport {
        unit,
        stage,
        identical: unsupported.is_none(),
        unsupported,
        norm,
        facts,
    })?;
    file.write_all(&data)?;
    Ok(())
}

/// Validate each imported unit and compare the existing Lambda s-expression
/// dumps. Unsupported is a recorded legacy fallback; a difference is an error.
#[cold]
pub fn check_lambda(arena: &LamArena, root: Lam, unit: &str) -> anyhow::Result<()> {
    // This hook already runs only off the default path. S4 rounds are Check
    // only: New still exercises the bridges without running rewrite rounds.
    if BackendMode::from_env() == BackendMode::Check {
        check_flatten(arena, root, unit)?;
        check_exits(arena, root, unit)?;
    }
    let imported = match import_lambda(arena, root) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, "lambda-bridge", Some(reason.0), None),
    };
    imported
        .arena
        .validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: lambda-bridge validation: {message}"))?;
    let exported = match export_lambda(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, "lambda-bridge", Some(reason.0), None),
    };
    let mut before = Vec::new();
    let mut after = Vec::new();
    crate::lambda::sexp_lambda::print_lambda(&arena.export(root), &mut before)?;
    crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after)?;
    if before != after {
        let before = String::from_utf8_lossy(&before);
        let after = String::from_utf8_lossy(&after);
        let line = before
            .lines()
            .zip(after.lines())
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count()))
            + 1;
        anyhow::bail!("{unit}: lambda-bridge mismatch at line {line}");
    }
    report(unit, "lambda-bridge", None, None)
}

/// Stage `lambda-norm`: replay the unit's lowering through the Bir
/// normalising rules and renormalise the lowered unit, each compared with
/// `LamArena`'s smart constructors (`bir::replay`). `raw` is the unit's raw
/// Lambda root, still present in the arena lowering returned.
#[cold]
pub fn check_norm(arena: &LamArena, raw: Lam, unit: &str) -> anyhow::Result<()> {
    let rows = |fired: [u32; super::l::norm::ROWS]| {
        super::l::norm::ROW_NAMES
            .into_iter()
            .zip(fired)
            .filter(|(_, count)| *count != 0)
            .collect()
    };
    match super::replay::compare(arena, raw, unit)? {
        Ok(stats) => report(
            unit,
            "lambda-norm",
            None,
            Some(NormReport {
                calls: stats.calls,
                replayed: rows(stats.replayed),
                renormalised: rows(stats.renormalised),
                compared: stats.compared,
                rules: Default::default(),
            }),
        ),
        Err(reason) => report(unit, "lambda-norm", Some(reason.0), None),
    }
}

/// Stage `js-bridge`: compare the post-pass program with a J-level round trip.
/// Both prints use the legacy printer, regardless of the selected output printer.
#[cold]
pub fn check_js(
    program: &crate::js_ir::arena::JsDepsProgram,
    resolver: &crate::js_ir::ModulePathResolver,
    directives: &[String],
    debug: bool,
    jsx_preserve: bool,
    emit_header: bool,
    unit: &str,
) -> anyhow::Result<()> {
    let imported = match super::bridge_j::import_js(program) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, "js-bridge", Some(reason.0), None),
    };
    imported.arena.validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: js-bridge validation: {message}"))?;
    let exported = match super::bridge_j::export_js(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, "js-bridge", Some(reason.0), None),
    };
    let print = |p| crate::js_ir::print_deps_program_with_directives_and_options(
        p, Some(resolver), directives, debug, jsx_preserve, emit_header,
    );
    let before = print(program);
    let after = print(&exported);
    if before != after {
        let line = before.lines().zip(after.lines()).position(|(a,b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count())) + 1;
        anyhow::bail!("{unit}: js-bridge mismatch at line {line}");
    }
    report(unit, "js-bridge", None, None)
}

/// The first deep_flatten cut in simplify_in_arena: its input is the lowered,
/// alias-collapsed root passed to check_lambda. Run the same first call on a
/// private legacy arena, with exactly its ident_stamp_bound counter seed.
/// Neither path touches the live pipeline or the legacy thread-local counter.
#[cold]
pub fn check_flatten(arena: &LamArena, root: Lam, unit: &str) -> anyhow::Result<()> {
    let mut imported = match import_lambda(arena, root) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, "lambda-flatten", Some(reason.0), None),
    };
    let stamp = arena.ident_stamp_bound();
    let stats = {
        let mut engine = super::engine::Engine::new(&mut imported.arena);
        engine.set_current_stamp(stamp as u32);
        engine.run(&super::l::flatten::FLATTEN, imported.root);
        engine.stats
    };
    for (var, source) in stats.renames {
        if let Err(reason) = imported.register_rename(var, source) {
            return report(unit, "lambda-flatten", Some(reason.0), None);
        }
    }
    imported.arena.validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: lambda-flatten validation: {message}"))?;
    let exported = match export_lambda(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, "lambda-flatten", Some(reason.0), None),
    };
    let generator = crate::context::IdGenerator::new();
    generator.set_current_stamp(stamp);
    let mut legacy = arena.clone();
    let expected = crate::lambda::lam_pass_deep_flatten::deep_flatten(&mut legacy, root, &generator);
    if super::l::flatten::identities(&legacy, expected)
        != super::l::flatten::identities(&exported.arena, exported.root)
    {
        anyhow::bail!("{unit}: lambda-flatten identifier mismatch (name, stamp or flags)");
    }
    let mut before = Vec::new();
    let mut after = Vec::new();
    crate::lambda::sexp_lambda::print_lambda(&legacy.export(expected), &mut before)?;
    crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after)?;
    if before != after {
        let before = String::from_utf8_lossy(&before);
        let after = String::from_utf8_lossy(&after);
        let line = before.lines().zip(after.lines()).position(|(a,b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count())) + 1;
        anyhow::bail!("{unit}: lambda-flatten mismatch at line {line}: expected {:?}, got {:?}",
            before.lines().nth(line - 1), after.lines().nth(line - 1));
    }
    report(unit, "lambda-flatten", None, Some(NormReport {
        calls: stats.entered,
        replayed: Default::default(),
        renormalised: Default::default(),
        compared: stats.compared,
        rules: stats.rules,
    }))
}

/// First exits cut: flatten then exits on each side, with one private counter.
/// Compare the ordered count too; structural CatchHeader::uses is not this fact.
#[cold]
pub fn check_exits(arena: &LamArena, root: Lam, unit: &str) -> anyhow::Result<()> {
    let mut imported = match import_lambda(arena, root) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, "lambda-exits", Some(reason.0), None),
    };
    let stamp = arena.ident_stamp_bound();
    let (stats, counts) = {
        let mut engine = super::engine::Engine::new(&mut imported.arena);
        engine.set_current_stamp(stamp as u32);
        engine.run(&super::l::flatten::FLATTEN, imported.root);
        let counts = super::l::exits::count(engine.bir(), imported.root);
        // Report only this round's rules, retaining flatten's fresh identities.
        engine.stats.rules.clear();
        engine.stats.entered = 0;
        engine.run(&super::l::exits::EXITS, imported.root);
        (engine.stats, counts)
    };
    for (var, source) in stats.renames {
        if let Err(reason) = imported.register_rename(var, source) {
            return report(unit, "lambda-exits", Some(reason.0), None);
        }
    }
    imported
        .arena
        .validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: lambda-exits validation: {message}"))?;
    let exported = match export_lambda(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, "lambda-exits", Some(reason.0), None),
    };
    let generator = crate::context::IdGenerator::new();
    generator.set_current_stamp(stamp);
    let mut legacy = arena.clone();
    let expected =
        crate::lambda::lam_pass_deep_flatten::deep_flatten(&mut legacy, root, &generator);
    let legacy_counts: std::collections::BTreeMap<_, _> =
        crate::lambda::lam_pass_exits::count_helper(&legacy, expected)
            .into_iter()
            .map(|(label, count)| (label as u32, count))
            .collect();
    if counts != legacy_counts {
        anyhow::bail!("{unit}: lambda-exits ordered count mismatch");
    }
    let expected = crate::lambda::lam_pass_exits::simplify_exits(&mut legacy, expected, &generator);
    if super::l::flatten::identities(&legacy, expected)
        != super::l::flatten::identities(&exported.arena, exported.root)
    {
        anyhow::bail!("{unit}: lambda-exits identifier mismatch (name, stamp or flags)");
    }
    let mut before = Vec::new();
    let mut after = Vec::new();
    crate::lambda::sexp_lambda::print_lambda(&legacy.export(expected), &mut before)?;
    crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after)?;
    if before != after {
        let before = String::from_utf8_lossy(&before);
        let after = String::from_utf8_lossy(&after);
        let line = before
            .lines()
            .zip(after.lines())
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count()))
            + 1;
        anyhow::bail!(
            "{unit}: lambda-exits mismatch at line {line}: expected {:?}, got {:?}",
            before.lines().nth(line - 1),
            after.lines().nth(line - 1)
        );
    }
    report(
        unit,
        "lambda-exits",
        None,
        Some(NormReport {
            calls: stats.entered,
            replayed: Default::default(),
            renormalised: Default::default(),
            compared: stats.compared,
            rules: stats.rules,
        }),
    )
}

/// The cross-module resolver of the real pipeline, as the alias round's
/// host: a function another module exports is imported as a detached tree.
struct InlineHost<'a, 'r> {
    resolver: &'a mut crate::lambda::lam_pass_remove_alias::ExternalInlineResolver<'r>,
    globals: Vec<crate::ident::Ident>,
    foreign: Vec<crate::ident::Ident>,
}
impl super::engine::Host for InlineHost<'_, '_> {
    fn external_function(
        &mut self,
        bir: &mut super::Bir,
        module: super::ImportId,
        field: &str,
    ) -> Result<Option<super::NodeId>, super::bridge::Unsupported> {
        let ident = self.globals[module.index()];
        let Some(function @ crate::lambda::Lambda::Lfunction(_)) = (self.resolver)(&ident, field)
        else {
            return Ok(None);
        };
        let mut arena = LamArena::new();
        let root = arena.import(&function);
        super::bridge::import_fragment(bir, &mut self.globals, &mut self.foreign, &arena, root)
            .map(Some)
    }
}

fn ident_text(id: crate::ident::Ident) -> String {
    format!("{}/{}", id.name(), id.stamp())
}

/// The entry `lam_pass_collect` recorded for a binder, as text. An entry the
/// alias pass cannot tell from no entry (an exported binding whose value is
/// not a function, a function entry without a definition) reads `na`.
fn legacy_fact(a: &LamArena, kind: Option<&crate::lambda::lam_stats::IdKind>) -> String {
    use crate::lambda::arena::Node;
    use crate::lambda::lam_compile_context::{BoxedNullable, RecFlag};
    use crate::lambda::lam_stats::{Element, IdKind};
    let simple = |l: Lam| match a.node(l) {
        Node::Var(id) => format!("var {}", ident_text(a.ident(id))),
        Node::Const(c) => format!("const {:?}", a.constant(c)),
        Node::Prim { .. } => {
            let (primitive, args, _) = a.as_prim(l).expect("primitive");
            match a.node(args[0]) {
                Node::GlobalModule(id) => format!("{primitive:?} of module {}", a.ident(id).name()),
                Node::Var(id) => format!("{primitive:?} of var {}", ident_text(a.ident(id))),
                _ => "other".to_string(),
            }
        }
        _ => "other".to_string(),
    };
    match kind {
        None | Some(IdKind::Na) => "na".to_string(),
        Some(IdKind::Exception) => "exception".to_string(),
        Some(IdKind::Parameter) => "param".to_string(),
        Some(IdKind::Constant(c)) => format!("const {:?}", a.constant(*c)),
        Some(IdKind::Module(id)) => format!("module {}", id.name()),
        Some(IdKind::NormalOptional(l)) => match a.node(*l) {
            Node::Var(_) | Node::Const(_) => format!("some {}", simple(*l)),
            _ => "some other".to_string(),
        },
        Some(IdKind::OptionalBlock(l, nullable)) => format!(
            "nullable {} {}",
            simple(*l),
            match nullable {
                BoxedNullable::Null => "null",
                BoxedNullable::Undefined => "undefined",
                BoxedNullable::NullUndefined => "both",
            }
        ),
        Some(IdKind::MutableBlock(_)) => "mutable".to_string(),
        Some(IdKind::ImmutableBlock(elements)) => format!(
            "block [{}]",
            elements
                .iter()
                .map(|element| match element {
                    Element::Na => "na".to_string(),
                    Element::SimpleForm(l) => simple(*l),
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Some(IdKind::FunctionId { lambda, arity }) => {
            let kind = match lambda {
                Some((l, rec)) => match a.node(*l) {
                    Node::Function { info, .. } => format!(
                        "function {} ({})",
                        match rec {
                            RecFlag::NonRec => "nonrec",
                            RecFlag::SelfRec => "selfrec",
                            RecFlag::Rec => "rec",
                        },
                        a.params(info)
                            .iter()
                            .map(|id| ident_text(*id))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    _ => "na".to_string(),
                },
                None => "na".to_string(),
            };
            format!("{kind} arity {arity:?}")
        }
    }
}

/// The entry the alias round reads for a binder, in the same text.
fn bir_fact(
    e: &super::engine::Engine<'_>,
    table: &mut super::l::alias::Table,
    idents: &[crate::ident::Ident],
    globals: &[crate::ident::Ident],
    arities: &super::l::arity::Arities,
    var: super::VarId,
) -> Result<String, super::bridge::Unsupported> {
    let kind = bir_entry(e, table, idents, globals, var)?;
    Ok(match arities.get(var) {
        super::l::arity::Recorded::Function(arity) => format!("{kind} arity {arity:?}"),
        super::l::arity::Recorded::Nothing | super::l::arity::Recorded::Other => kind,
    })
}

fn bir_entry(
    e: &super::engine::Engine<'_>,
    table: &mut super::l::alias::Table,
    idents: &[crate::ident::Ident],
    globals: &[crate::ident::Ident],
    var: super::VarId,
) -> Result<String, super::bridge::Unsupported> {
    use super::l::alias::{Elem, Entry, Rec};
    use super::{BoxedNullable, View};
    let b = e.bir();
    let name = |v: super::VarId| ident_text(idents[v.index()]);
    let constant = |c| super::bridge::export_constant(b, c).map(|c| format!("const {c:?}"));
    let simple = |element: Elem| -> Result<String, super::bridge::Unsupported> {
        Ok(match element {
            Elem::Na => "na".to_string(),
            Elem::Var(v) => format!("var {}", name(v)),
            Elem::Const(c) => constant(c)?,
            Elem::FieldOfGlobal(p, m) => format!(
                "{:?} of module {}",
                b.primitive(p).primitive,
                globals[m.index()].name()
            ),
            Elem::FieldOfVar(p, v) => format!("{:?} of var {}", b.primitive(p).primitive, name(v)),
        })
    };
    Ok(match table.entry(e, var) {
        Entry::Unset | Entry::Na => "na".to_string(),
        Entry::Param => "param".to_string(),
        Entry::Const(c) => constant(c)?,
        Entry::Module(m) => format!("module {}", globals[m.index()].name()),
        Entry::Optional(Elem::Na) => "some other".to_string(),
        Entry::Optional(element) => format!("some {}", simple(element)?),
        Entry::Nullable(v, kind) => format!(
            "nullable var {} {}",
            name(v),
            match kind {
                BoxedNullable::Null => "null",
                BoxedNullable::Undefined => "undefined",
                BoxedNullable::Both => "both",
            }
        ),
        Entry::Block { start, len } => {
            let elements: Vec<Elem> = table.elements(start, len).to_vec();
            format!(
                "block [{}]",
                elements
                    .into_iter()
                    .map(simple)
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            )
        }
        Entry::Function { node, rec, .. } => {
            let View::Fun { header, .. } = b.view(node) else {
                return Ok("na".to_string());
            };
            format!(
                "function {} ({})",
                match rec {
                    Rec::NonRec => "nonrec",
                    Rec::SelfRec => "selfrec",
                    Rec::Rec => "rec",
                },
                b.function(header)
                    .params
                    .iter()
                    .map(name)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    })
}

/// Compare, for every binder of the unit, the entry the alias round reads
/// (the maintained fact, frozen) with the entry the legacy table holds after
/// `collect_info`. A difference is an error naming the unit, the binder and
/// both. Returns the number of binders per kind.
fn compare_facts(
    e: &super::engine::Engine<'_>,
    root: super::NodeId,
    idents: &[crate::ident::Ident],
    globals: &[crate::ident::Ident],
    arities: &super::l::arity::Arities,
    legacy: &LamArena,
    table: &crate::lambda::lam_stats::IdentTable,
    unit: &str,
) -> anyhow::Result<Result<std::collections::BTreeMap<&'static str, u64>, super::bridge::Unsupported>>
{
    let mut entries = super::l::alias::Table::new(e);
    let mut counts = std::collections::BTreeMap::new();
    let mut work = vec![root];
    while let Some(n) = work.pop() {
        for var in e.bir().binders(n) {
            let ident = idents[var.index()];
            let ours = match bir_fact(e, &mut entries, idents, globals, arities, var) {
                Ok(text) => text,
                Err(reason) => return Ok(Err(reason)),
            };
            let theirs = legacy_fact(legacy, table.get(&ident));
            if ours != theirs {
                anyhow::bail!(
                    "{unit}: lambda-alias fact mismatch for {}: legacy table {theirs:?}, Bir {ours:?}",
                    ident_text(ident)
                );
            }
            let kind = ["na", "param", "const", "module", "some", "nullable", "block", "function"]
                .into_iter()
                .find(|kind| ours.split(' ').next() == Some(kind))
                .unwrap_or("other");
            *counts.entry(kind).or_default() += 1;
            if ours.contains(" arity ") {
                *counts.entry("arity").or_default() += 1;
            }
        }
        work.extend(e.bir().view(n).children());
    }
    Ok(Ok(counts))
}

type Facts = std::collections::BTreeMap<&'static str, u64>;

/// Mark the unit's exports in the arena (`Lam_stats.export_idents`).
pub(crate) fn mark_exports(imported: &mut super::bridge::Imported, exports: &[crate::ident::Ident]) {
    let export_set: crate::fast_hash::AHashSet<crate::ident::Ident> =
        exports.iter().copied().collect();
    let exported: Vec<(super::VarId, crate::name::Name)> = imported
        .idents()
        .iter()
        .enumerate()
        .filter(|(_, ident)| export_set.contains(*ident))
        .map(|(index, ident)| (super::VarId(index as u32), ident.name_atom()))
        .collect();
    for (var, name) in exported {
        imported.arena.export(var, name);
    }
}

/// One `collect_info` on the Bir side, for arities (`bir/l/arity.rs`).
pub(crate) fn collect_arities(
    imported: &mut super::bridge::Imported,
    arities: &mut super::l::arity::Arities,
    external_arity: &mut crate::lambda::lam_pass_collect::ExternalArityResolver<'_>,
) {
    let globals = imported.globals().to_vec();
    let root = imported.root;
    let engine = super::engine::Engine::new(&mut imported.arena);
    arities.collect(&engine, root, &mut |module, field| {
        external_arity(&globals[module.index()], field)
    });
}

/// The alias round on an imported unit whose earlier rounds are done and
/// registered and whose exports are marked: compare every binder's fact and
/// arity with the legacy table `table` (whose handles are in `legacy`), run
/// the round with the resolver as its host, and register what it created
/// with the bridge.
/// `Err` is a fallback, with the fact counts when the comparison was made.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_alias(
    imported: &mut super::bridge::Imported,
    exports: &[crate::ident::Ident],
    stamp: u32,
    jsx_preserve: bool,
    external_inline: &mut crate::lambda::lam_pass_remove_alias::ExternalInlineResolver<'_>,
    arities: &super::l::arity::Arities,
    legacy: &LamArena,
    table: &crate::lambda::lam_stats::IdentTable,
    unit: &str,
) -> anyhow::Result<Result<(super::engine::Stats, Facts), (&'static str, Option<Facts>)>> {
    let _ = exports;
    let idents = imported.idents().to_vec();
    let mut host = InlineHost {
        resolver: external_inline,
        globals: imported.globals().to_vec(),
        foreign: Vec::new(),
    };
    let root_node = imported.root;
    let (stats, facts) = {
        let mut engine = super::engine::Engine::new(&mut imported.arena);
        engine.set_current_stamp(stamp);
        let facts =
            match compare_facts(
                &engine,
                root_node,
                &idents,
                &host.globals,
                arities,
                legacy,
                table,
                unit,
            )? {
                Ok(facts) => facts,
                Err(reason) => return Ok(Err((reason.0, None))),
            };
        engine.jsx_preserve = jsx_preserve;
        engine.host = Some(&mut host);
        let _ = &mut engine;
        (engine.stats, facts)
    };
    if let Some(reason) = stats.unsupported {
        return Ok(Err((reason, Some(facts))));
    }
    let mut foreign = host.foreign.into_iter();
    for &(var, source) in &stats.renames {
        let registered = if var == source {
            let ident = foreign.next().expect("an identity for each imported variable");
            imported.register_foreign(var, ident)
        } else {
            imported.register_rename(var, source)
        };
        if let Err(reason) = registered {
            return Ok(Err((reason.0, Some(facts))));
        }
    }
    for &(fresh, source) in &stats.labels {
        imported.register_label(fresh, source);
    }
    imported.set_globals(host.globals);
    Ok(Ok((stats, facts)))
}

/// Stage `lambda-alias`: the first `simplify_alias` of `simplify_in_arena`.
/// The Bir side runs the flatten, exits and alias rounds; the legacy side
/// runs `deep_flatten`, `collect_info`, `simplify_exits`, `collect_info`,
/// `simplify_alias` on a private arena with the same counter seed, the same
/// resolvers and `jsx_preserve`. Before the alias round, every binder's fact
/// is compared with the legacy table.
#[cold]
pub fn check_alias(
    arena: &LamArena,
    root: Lam,
    unit: &str,
    jsx_preserve: bool,
    external_inline: &mut crate::lambda::lam_pass_remove_alias::ExternalInlineResolver<'_>,
    external_arity: &mut crate::lambda::lam_pass_collect::ExternalArityResolver<'_>,
) -> anyhow::Result<()> {
    const STAGE: &str = "lambda-alias";
    let mut imported = match import_lambda(arena, root) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, STAGE, Some(reason.0), None),
    };
    let stamp = arena.ident_stamp_bound();
    let exports: Vec<crate::ident::Ident> =
        crate::lambda::lam_compile_main::module_export(arena, root)
            .map(|(ids, _)| ids.to_vec())
            .unwrap_or_default();

    // The legacy pipeline up to and including the first `simplify_alias`.
    let mut meta = crate::lambda::lam_stats::LamStats::new(exports.clone());
    meta.id_gen.set_current_stamp(stamp);
    let id_gen = meta.id_gen.clone();
    let mut legacy = arena.clone();
    let flat = crate::lambda::lam_pass_deep_flatten::deep_flatten(&mut legacy, root, &id_gen);
    crate::lambda::lam_pass_collect::collect_info_with_external_arity(
        &legacy,
        &mut meta,
        flat,
        external_arity,
    );
    let cut = crate::lambda::lam_pass_exits::simplify_exits(&mut legacy, flat, &id_gen);
    crate::lambda::lam_pass_collect::collect_info_with_external_arity(
        &legacy,
        &mut meta,
        cut,
        external_arity,
    );
    let table = meta.ident_tbl.clone();
    // The round itself is compared from the commit that runs it; until
    // then the stage compares the facts, and the tree at the cut.
    let expected = cut;

    // The Bir side: the rounds before the cut, with a collection for
    // arities where the legacy pipeline has one.
    mark_exports(&mut imported, &exports);
    let mut arities = super::l::arity::Arities::default();
    let mut stamp = stamp as u32;
    for round in [&super::l::flatten::FLATTEN, &super::l::exits::EXITS] {
        let renames = {
            let mut engine = super::engine::Engine::new(&mut imported.arena);
            engine.set_current_stamp(stamp);
            engine.run(round, imported.root);
            stamp = engine.current_stamp();
            std::mem::take(&mut engine.stats.renames)
        };
        for (var, source) in renames {
            if let Err(reason) = imported.register_rename(var, source) {
                return report(unit, STAGE, Some(reason.0), None);
            }
        }
        collect_arities(&mut imported, &mut arities, external_arity);
    }
    let (stats, facts) = match run_alias(
        &mut imported,
        &exports,
        stamp,
        jsx_preserve,
        external_inline,
        &arities,
        &legacy,
        &table,
        unit,
    )? {
        Ok(done) => done,
        Err((reason, facts)) => return report_with_facts(unit, STAGE, Some(reason), None, facts),
    };
    imported
        .arena
        .validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: {STAGE} validation: {message}"))?;
    let exported = match export_lambda(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, STAGE, Some(reason.0), None),
    };
    if super::l::flatten::identities(&legacy, expected)
        != super::l::flatten::identities(&exported.arena, exported.root)
    {
        anyhow::bail!("{unit}: {STAGE} identifier mismatch (name, stamp or flags)");
    }
    let mut before = Vec::new();
    let mut after = Vec::new();
    crate::lambda::sexp_lambda::print_lambda(&legacy.export(expected), &mut before)?;
    crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after)?;
    if before != after {
        let before = String::from_utf8_lossy(&before);
        let after = String::from_utf8_lossy(&after);
        let line = before
            .lines()
            .zip(after.lines())
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count()))
            + 1;
        anyhow::bail!(
            "{unit}: {STAGE} mismatch at line {line}: expected {:?}, got {:?}",
            before.lines().nth(line - 1),
            after.lines().nth(line - 1)
        );
    }
    report_with_facts(
        unit,
        STAGE,
        None,
        Some(NormReport {
            calls: stats.entered,
            replayed: Default::default(),
            renormalised: Default::default(),
            compared: stats.compared,
            rules: stats.rules,
        }),
        Some(facts),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn both_opt_in_modes_keep_legacy_javascript() {
        let mut options = crate::driver::CompilerOptions {
            backend: BackendMode::Legacy,
            ..Default::default()
        };
        let source = "let answer = 42";
        let expected =
            crate::driver::compile_source_to_js_with_options(source, "Mode.res", &options).unwrap();
        for mode in [BackendMode::Check, BackendMode::New] {
            options.backend = mode;
            let actual =
                crate::driver::compile_source_to_js_with_options(source, "Mode.res", &options)
                    .unwrap();
            assert_eq!(actual, expected);
        }
    }
}
