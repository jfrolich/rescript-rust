//! The oracle of derived items: `RESCRIPT_DERIVED_PATH=check`
//! (`compiler-rust/docs/DERIVED_CODECS.md`, "The oracle").
//!
//! A unit with at least one planned item is compiled twice in the same
//! process, from the plans and from the general forms the plans stand for,
//! and what the two produce is compared: the warnings, the signature, the
//! unit reads, the JavaScript with its source map, and the export summary. A
//! difference fails the compile of the unit. The switch and this module go
//! when every supported item is planned.
//!
//! The signature is compared in its canonical form (`types::canonical_sig`).
//! The stored interface and its fingerprint are not: they record which type
//! nodes two values share, and a discharge instantiates each binding's
//! codec on its own, where typing a group of bindings shares the nodes of
//! one annotation. The types are the same.

use anyhow::Result;

use super::{
    CompilerOptions, DerivedRetry, DumpKind, InProcessCompileResult, InProcessPreJsCompileResult,
    InProcessSignatureReadyHook, LocationRetry, UntilJs, UserDiagnostic, compile_until_js,
};

/// The failure of a check: the unit, what differs, and where.
fn differs(unit: &str, what: &str, detail: String) -> anyhow::Error {
    UserDiagnostic::new(
        format!(
            "RESCRIPT_DERIVED_PATH=check: in {unit}, {what} of the plans and of the general form differ\n{detail}\n"
        ),
        2,
    )
    .into()
}

/// The check could not run on `unit`: its general form is missing.
fn no_general_form(unit: &str, error: &anyhow::Error) -> anyhow::Error {
    UserDiagnostic::new(
        format!(
            "RESCRIPT_DERIVED_PATH=check: internal error: {unit} was not checked, its general form could not be made: {error}\n"
        ),
        2,
    )
    .into()
}

/// The first line at which two texts differ: its number from 1, and the
/// line of each (empty past the end of a text). Cost: O(bytes).
fn first_difference<'a>(plans: &'a str, general: &'a str) -> Option<(usize, &'a str, &'a str)> {
    let (mut a, mut b) = (plans.lines(), general.lines());
    let mut number = 1;
    loop {
        match (a.next(), b.next()) {
            (None, None) => return None,
            (x, y) if x == y => number += 1,
            (x, y) => return Some((number, x.unwrap_or(""), y.unwrap_or(""))),
        }
    }
}

/// The top-level JavaScript binding that line `number` of `code` is in: the
/// name the nearest line at or above it declares. Cost: O(bytes above).
fn js_binding(code: &str, number: usize) -> &str {
    code.lines()
        .take(number)
        .filter_map(|line| {
            let rest = ["function ", "let ", "const ", "var "]
                .iter()
                .find_map(|keyword| line.strip_prefix(keyword))?;
            let end = rest
                .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '$'))
                .unwrap_or(rest.len());
            Some(&rest[..end])
        })
        .last()
        .unwrap_or("(none)")
}

/// Compare two texts line by line.
fn same_text(unit: &str, what: &str, plans: &str, general: &str) -> Result<()> {
    match first_difference(plans, general) {
        None => Ok(()),
        Some((number, a, b)) => Err(differs(
            unit,
            what,
            format!("  line {number}\n  plans:   {a}\n  general: {b}"),
        )),
    }
}

/// Compare two keyed tables: the first key, in order, whose entries differ.
fn same_entries(
    unit: &str,
    what: &str,
    mut plans: Vec<(&str, String)>,
    mut general: Vec<(&str, String)>,
) -> Result<()> {
    plans.sort();
    general.sort();
    let (mut a, mut b) = (plans.iter(), general.iter());
    loop {
        match (a.next(), b.next()) {
            (None, None) => return Ok(()),
            (x, y) if x == y => {}
            (x, y) => {
                let show = |entry: Option<&(&str, String)>| match entry {
                    Some((name, value)) => format!("{name} = {value}"),
                    None => "(none)".to_string(),
                };
                return Err(differs(
                    unit,
                    what,
                    format!(
                        "  binding `{}`\n  plans:   {}\n  general: {}",
                        x.or(y).map_or("", |entry| entry.0),
                        show(x),
                        show(y)
                    ),
                ));
            }
        }
    }
}

/// The `DumpKind::Sig` dump of a result.
fn signature_dump(dumps: &[(DumpKind, String)]) -> &str {
    dumps
        .iter()
        .find(|(kind, _)| *kind == DumpKind::Sig)
        .map_or("", |(_, text)| text)
}

/// Compile `unit` both ways up to the JS backend, compare what typing and
/// lowering report, and return the result of the plans carrying the
/// reference, which the JS backend compares in turn ([`compare_js`]).
/// Cost: two compiles of the unit.
pub(super) fn until_js(
    unit: &UntilJs<'_>,
    options: &CompilerOptions,
    gentype_interface: Option<crate::gentype::main::InterfaceRead>,
    signature_ready: Option<&mut InProcessSignatureReadyHook<'_>>,
) -> Result<InProcessPreJsCompileResult> {
    let name = unit.module_name;
    let mut both = options.clone();
    let wants_signature = both.dumps.contains(&DumpKind::Sig);
    if !wants_signature {
        both.dumps.push(DumpKind::Sig);
    }
    both.collect_unit_reads = true;
    let mut reference_options = both.clone();
    reference_options.derived_census = None;

    // The general form of the unit is what the frontend makes of its source
    // with plans off.
    // Not having it is a failure of the check itself, never a difference.
    let general_form = match &options.derived_reference {
        Some(frontend) => frontend(),
        None => Err(anyhow::anyhow!("the build gave no source to make it from")),
    };
    let (general_arena, general_structure) = match general_form {
        Ok(general_form) => general_form,
        Err(error) => return Err(no_general_form(name, &error)),
    };
    let general = UntilJs {
        arena: &general_arena,
        structure: &general_structure,
        ..*unit
    };
    // The reference first: it publishes nothing, and what the plans publish
    // is compared with it.
    let reference = compile_until_js(&general, &reference_options, gentype_interface.clone(), None);
    let result = compile_until_js(unit, &both, gentype_interface, signature_ready);

    let (mut result, reference) = match (result, reference) {
        (Ok(result), Ok(reference)) => (result, reference),
        // A compile that needs locations is retried with them, and checked
        // then; a unit whose plans cannot be used is compiled without them,
        // and has nothing to check.
        (Err(error), _) if error.is::<LocationRetry>() || error.is::<DerivedRetry>() => {
            return Err(error);
        }
        (_, Err(error)) if error.is::<LocationRetry>() => return Err(error),
        (Err(error), Err(reference)) => {
            same_text(name, "the diagnostics", &error.to_string(), &reference.to_string())?;
            return Err(error);
        }
        (Err(error), Ok(_)) => {
            return Err(differs(name, "the diagnostics", format!("  plans:   {error}\n  general: (none)")));
        }
        (Ok(_), Err(reference)) => {
            return Err(differs(name, "the diagnostics", format!("  plans:   (none)\n  general: {reference}")));
        }
    };

    same_text(name, "the warnings", &result.warnings, &reference.warnings)?;
    same_text(
        name,
        "the signature",
        signature_dump(&result.dumps),
        signature_dump(&reference.dumps),
    )?;
    let reads = |result: &InProcessPreJsCompileResult| {
        let mut reads: Vec<String> = result
            .unit_reads
            .iter()
            .map(|read| format!("{read:?}"))
            .collect();
        reads.sort();
        reads.dedup();
        reads.join("\n")
    };
    same_text(name, "the unit reads", &reads(&result), &reads(&reference))?;

    if !wants_signature {
        result.dumps.retain(|(kind, _)| *kind != DumpKind::Sig);
    }
    if !options.collect_unit_reads {
        result.unit_reads.clear();
    }
    result.derived_reference = Some(Box::new(reference));
    Ok(result)
}

/// The entries of an export table, printed.
fn printed<V: std::fmt::Debug>(table: &ahash::AHashMap<String, V>) -> Vec<(&str, String)> {
    table
        .iter()
        .map(|(name, value)| (name.as_str(), format!("{value:?}")))
        .collect()
}

/// Compare what the JS backend printed for the two compiles of `unit`: the
/// JavaScript and its source map for each output.
/// Cost: O(bytes of the outputs).
pub(super) fn compare_js(
    unit: &str,
    plans: &InProcessCompileResult,
    general: &InProcessCompileResult,
) -> Result<()> {
    let javascript = |what: &str, a: &str, b: &str| match first_difference(a, b) {
        None => Ok(()),
        Some((number, x, y)) => Err(differs(
            unit,
            what,
            format!(
                "  binding `{}`, line {number}\n  plans:   {x}\n  general: {y}",
                js_binding(a, number)
            ),
        )),
    };
    javascript("the JavaScript", &plans.js_output, &general.js_output)?;
    if plans.js_outputs.len() != general.js_outputs.len() {
        return Err(differs(
            unit,
            "the JavaScript outputs",
            format!(
                "  plans:   {} files\n  general: {} files",
                plans.js_outputs.len(),
                general.js_outputs.len()
            ),
        ));
    }
    for (a, b) in plans.js_outputs.iter().zip(&general.js_outputs) {
        javascript("the JavaScript", &a.code, &b.code)?;
        same_text(
            unit,
            "the source map",
            a.source_map.as_deref().unwrap_or(""),
            b.source_map.as_deref().unwrap_or(""),
        )?;
    }
    Ok(())
}

/// Compare the export summary of the plans (`is_pure` and the three tables
/// dependents read, as the backend hands them over) with the reference's.
/// Cost: O(exports), each printed once.
pub(super) fn compare_exports(
    unit: &str,
    is_pure: bool,
    constants: &ahash::AHashMap<String, crate::cmi::persistent_env::CmjExportConstant>,
    arities: &ahash::AHashMap<String, crate::cmi::persistent_env::CmjExportArity>,
    lambdas: &crate::lambda::CmjExportLambdas,
    general: &InProcessCompileResult,
) -> Result<()> {
    if is_pure != general.is_pure {
        return Err(differs(
            unit,
            "the purity",
            format!("  plans:   {is_pure}\n  general: {}", general.is_pure),
        ));
    }
    same_entries(
        unit,
        "the exported constants",
        printed(constants),
        printed(&general.cmj_export_constants),
    )?;
    same_entries(
        unit,
        "the exported arities",
        printed(arities),
        printed(&general.cmj_export_arities),
    )?;
    same_entries(
        unit,
        "the inlinable bodies",
        printed(lambdas),
        printed(&general.cmj_export_lambdas),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::JsOutput;

    fn output(code: &str) -> InProcessCompileResult {
        InProcessCompileResult {
            js_outputs: vec![JsOutput {
                path: "Unit.res.mjs".into(),
                code: code.to_string(),
                source_map: None,
            }],
            ..Default::default()
        }
    }

    #[test]
    fn equal_results_pass() {
        let code = "function ids_encode(v) {\n  return 1;\n}\n";
        assert!(compare_js("Unit", &output(code), &output(code)).is_ok());
    }

    /// A difference names the unit and the binding it is in.
    #[test]
    fn a_difference_names_the_unit_and_the_binding() {
        let plans = "function id_encode(v) {\n  return 1;\n}\n\nfunction ids_encode(v) {\n  return 2;\n}\n";
        let general = "function id_encode(v) {\n  return 1;\n}\n\nfunction ids_encode(v) {\n  return 3;\n}\n";
        let error = compare_js("Unit", &output(plans), &output(general)).unwrap_err();
        let report = error.downcast::<UserDiagnostic>().unwrap();
        assert_eq!(
            report.output(),
            "RESCRIPT_DERIVED_PATH=check: in Unit, the JavaScript of the plans and of the general form differ\n  \
             binding `ids_encode`, line 6\n  plans:     return 2;\n  general:   return 3;\n"
        );
    }

    #[test]
    fn a_differing_export_names_the_binding() {
        let mut plans = output("");
        let general = output("");
        plans.is_pure = true;
        let exports = |plans: &InProcessCompileResult| {
            compare_exports(
                "Unit",
                plans.is_pure,
                &plans.cmj_export_constants,
                &plans.cmj_export_arities,
                &plans.cmj_export_lambdas,
                &general,
            )
        };
        assert!(exports(&general).is_ok());
        assert!(exports(&plans).unwrap_err().to_string().contains("the purity"));
        let entries = |value: &str| vec![("a", "1".to_string()), ("b", value.to_string())];
        let error = same_entries("Unit", "the exported arities", entries("2"), entries("3")).unwrap_err();
        assert!(error.to_string().contains("binding `b`\n  plans:   b = 2\n  general: b = 3"), "{error}");
    }
}
