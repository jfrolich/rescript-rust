//! Compiler driver utilities.
//!
//! This module wires together parsing, type-checking, Lambda conversion, and
//! JS IR codegen to produce JavaScript output.

mod derived_check;
mod type_clash;

use crate::types::path::PathView;

use std::ffi::OsString;
use std::fmt;
use std::path::{Component, Path as FsPath, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

use ahash::AHashSet;
use anyhow::{Context, Result, anyhow};
use tracing::info_span;

use crate::binary_ast::ppx;
use crate::cmi::persistent_env::{
    CmjExportArity, CmjExportConstant, ModuleRegistry, PersistentEnv, PersistentEnvError,
};
use crate::cmi::portable_types::{PortablePersStruct, SignaturePublicationMode};
use crate::context::IdGenerator;
use crate::diagnostics::WarningConfig;
use crate::ident::Ident;
use crate::js_ir::arena::JsDepsProgram as DepsProgram;
use crate::js_ir::{
    Kind, ModuleFormat, ModuleId, ModulePathResolutionError, ModulePathResolver,
    print_deps_program_with_directives_and_options, print_deps_program_with_source_map,
};
use crate::lambda::lam_compile::LambdaCompiler;
use crate::location::Location;
use crate::parse_arena::{ExprIdx, LocIdx, ParseArena, StrIdx};
use crate::parser::ast::{
    ArgLabel as ParserArgLabel, Attributes, ExpressionDesc, Payload, Signature, SignatureItemDesc,
    Structure, StructureItemDesc,
};
use crate::parser::{Longident, Parser, code_frame, jsx_ppx, module};
use crate::types::printtyp::{TAG_ERROR as ERROR, TAG_INFO as INFO, TAG_RESET as RESET};
use crate::types::sexp_typedtree::{
    print_typed_signature, print_typed_signature_with_locs, print_typed_structure,
    print_typed_structure_with_locs,
};
use crate::types::typecore::{BuiltinExtensionError, TypeCoreError, TypeCoreWarning};
use crate::types::typemod::{TypeExtensionMismatch, TypeModError, UnboundTypeVarDetail};
use crate::types::{
    ArgLabel as TypeArgLabel, TypeCheckContext, TypeClashContext, TypeContext, TypeDesc,
    TypeExprRef, initial_env, transl_signature, type_structure,
};

// OCaml's Predef sets `Ident.set_current_time 999`. OCaml's Parmatch.extra_pat
// then eagerly creates Ident.create "+" consuming stamp 1000.
// We match this by starting at 999 and consuming one stamp.
const OCAML_NON_PREDEF_STAMP_START: i32 = 999;
static SKIP_CLI_CLEANUP: AtomicBool = AtomicBool::new(false);

/// Internal control flow: discard a location-free attempt before publishing
/// it, then compile the same source with location side tables enabled.
#[derive(Debug, thiserror::Error, Clone, Copy, PartialEq, Eq)]
pub enum LocationRetry {
    /// A warning has to be reported.
    #[error("warning reporting requires source locations")]
    Warning,
    /// An error has to be reported.
    #[error("diagnostic compilation requires source locations")]
    Diagnostic,
    /// The output (source maps, GenType, typed artifacts) records locations.
    #[error("generated output requires source locations")]
    Output,
}

/// An obligation of a derived item's plan failed in the checker, which
/// abandoned the unit before publishing anything, and the compile had no
/// [`DerivedFallback`] to continue the unit's attempt loop
/// on. Whoever holds the unit's source makes that general syntax with
/// [`DerivedPath::Fallback`].
#[derive(Debug, thiserror::Error, Clone, Copy, PartialEq, Eq)]
#[error("a derived item's plan could not be used")]
pub struct DerivedRetry;

/// A compile failure whose report is already formatted for the user: print
/// `output` as is and exit with `exit_code`.
#[derive(Debug)]
pub struct UserDiagnostic {
    output: String,
    exit_code: i32,
}

impl UserDiagnostic {
    /// Wrap a formatted report, decoding the internal UTF-8 escapes the
    /// report printers emit.
    pub fn new(output: String, exit_code: i32) -> Self {
        let output = match crate::source_text::decode_internal_utf8_runs(&output) {
            std::borrow::Cow::Borrowed(_) => output,
            std::borrow::Cow::Owned(decoded) => decoded,
        };
        Self { output, exit_code }
    }

    /// The report text.
    pub fn output(&self) -> &str {
        &self.output
    }

    /// The process exit code `bsc` uses for this failure.
    pub fn exit_code(&self) -> i32 {
        self.exit_code
    }
}

impl fmt::Display for UserDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.output)
    }
}

impl std::error::Error for UserDiagnostic {}

/// Leak large per-compile state instead of freeing it, for a one-shot
/// process that is about to exit.
pub fn enable_cli_cleanup_skip() {
    SKIP_CLI_CLEANUP.store(true, Ordering::Relaxed);
}

pub use crate::misc::module_name_from_source_filename;

/// A concrete JavaScript output target for one compile.
#[derive(Clone)]
pub struct JsOutputTarget {
    /// Where the JavaScript is written.
    pub path: PathBuf,
    /// The module system of the written JavaScript.
    pub module_format: ModuleFormat,
}

/// Rendered JavaScript for one concrete output path.
pub struct JsOutput {
    /// Where the JavaScript is written.
    pub path: PathBuf,
    /// The JavaScript source.
    pub code: String,
    /// External source map contents for linked/hidden modes.
    pub source_map: Option<String>,
}

/// An intermediate representation an in-process compile can capture, printed
/// as the matching `bsc` flag prints it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DumpKind {
    /// `-dtyped-sexp`
    TypedTree,
    /// `-dtyped-sexp-locs`
    TypedTreeLocs,
    /// `-drawlambda`
    RawLambda,
    /// `-dlambda-sexp`
    Lambda,
    /// `-dlambda-sexp-locs`
    LambdaLocs,
    /// The unit's exported signature in canonical form
    /// (`types::canonical_sig`): for an interface file, and for an
    /// implementation without one.
    Sig,
}

impl DumpKind {
    /// Every dump kind.
    pub const ALL: [DumpKind; 6] = [
        DumpKind::TypedTree,
        DumpKind::TypedTreeLocs,
        DumpKind::RawLambda,
        DumpKind::Lambda,
        DumpKind::LambdaLocs,
        DumpKind::Sig,
    ];

    /// The name used on the command line and as the dump file extension.
    pub fn name(self) -> &'static str {
        match self {
            DumpKind::TypedTree => "typedtree",
            DumpKind::TypedTreeLocs => "typedtree-locs",
            DumpKind::RawLambda => "rawlambda",
            DumpKind::Lambda => "lambda",
            DumpKind::LambdaLocs => "lambda-locs",
            DumpKind::Sig => "sig",
        }
    }

    /// The dump kind named `name` (see [`DumpKind::name`]).
    pub fn from_name(name: &str) -> Option<DumpKind> {
        DumpKind::ALL.into_iter().find(|kind| kind.name() == name)
    }

    fn is_lambda(self) -> bool {
        matches!(
            self,
            DumpKind::RawLambda | DumpKind::Lambda | DumpKind::LambdaLocs
        )
    }

    /// Whether the dump prints source locations or text, so that the
    /// compile needs a parse that stores them.
    pub fn needs_locations(self) -> bool {
        match self {
            DumpKind::TypedTree
            | DumpKind::TypedTreeLocs
            | DumpKind::RawLambda
            | DumpKind::Lambda
            | DumpKind::LambdaLocs => true,
            DumpKind::Sig => false,
        }
    }
}

/// The `DumpKind::Sig` dump of a unit's exported signature.
fn canonical_signature_dump(
    type_ctx: &TypeContext,
    module_name: &str,
    signature: &[crate::types::decl::SignatureItem],
    deprecated: Option<&str>,
    arena: &ParseArena,
) -> (DumpKind, String) {
    let text = crate::types::canonical_sig::canonical_signature(
        type_ctx,
        module_name,
        signature,
        deprecated,
        Some(arena),
    );
    (DumpKind::Sig, latin1_dump(text.into_bytes()))
}

/// The dump's bytes, one `char` per byte. Dump printers write source text
/// byte for byte, so the bytes need not be UTF-8; writers turn each `char`
/// back into its byte.
fn latin1_dump(bytes: Vec<u8>) -> String {
    bytes.into_iter().map(char::from).collect()
}

/// See [`CompilerOptions::warning_locations`].
pub type WarningLocations =
    std::sync::Arc<dyn Fn() -> Option<crate::parse_arena::ParseArena> + Send + Sync>;

/// Place the warnings of a location-free compile in a located parse of the
/// same source (`warning_locations` of the syntax that was checked),
/// replacing each warning's location identity with the matching location
/// of `located` (parsed on first use). Returns false when any
/// warning cannot be placed with certainty; the caller then retries the
/// whole compile with locations. A located compile needs no placement.
fn place_location_free_warnings(
    arena: &crate::parse_arena::ParseArena,
    warning_locations: Option<&WarningLocations>,
    located: &mut Option<crate::parse_arena::ParseArena>,
    warnings: &mut [TypeCoreWarning],
) -> bool {
    if arena.stores_locations() || warnings.is_empty() {
        return true;
    }
    let Some(slots) = warnings
        .iter()
        .map(|warning| arena.located_parse_slot(warning.loc))
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    if located.is_none() {
        let Some(parse) = warning_locations.and_then(|parse| parse()) else {
            return false;
        };
        // Both parses must have issued the same locations, or identities and
        // located indices do not correspond.
        if !parse.stores_locations()
            || parse.parse_location_slot_count() != arena.parse_location_slot_count()
        {
            return false;
        }
        *located = Some(parse);
    }
    for (warning, slot) in warnings.iter_mut().zip(slots) {
        warning.loc = slot;
    }
    true
}

/// Publish the signature a compilation registered for `module_name`. In
/// signature check mode the publication is also compared with the frozen
/// shared graph and reported; a difference fails the compilation.
fn publish_signature(
    env: &PersistentEnv,
    options: &CompilerOptions,
    module_name: &str,
    filename: &str,
    type_ctx: &TypeContext,
    arena: &ParseArena,
    publication: SignaturePublicationMode,
) -> Result<(Option<std::sync::Arc<PortablePersStruct>>, Option<crate::cmi::signature_check::PreparedReport>)> {
    let (unit, report) = if let Some(check) = &options.signature_check {
        match env.extract_module_update_checked(module_name, type_ctx, Some(arena), publication) {
            Some((unit, comparison)) => (Some(unit), Some(check.prepare(filename, &comparison)?)),
            None => (None, None),
        }
    } else {
        (env.extract_module_update(module_name, type_ctx, Some(arena), publication), None)
    };
    if options.checker == CheckerChoice::Both
        && let Some(unit) = &unit
    {
        crate::tc::bridge::from_old::check_published(unit).map_err(anyhow::Error::msg)?;
    }
    Ok((unit, report))
}

/// The path derived items take: the switch `RESCRIPT_DERIVED_PATH`
/// (`compiler-rust/docs/DERIVED_CODECS.md`, "The oracle"). It exists until
/// every supported item is planned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerivedPath {
    /// Unset: the items the classifier supports are planned.
    Plans,
    /// `general`: the classifier keeps every item on the general path.
    General,
    /// `check`: a unit with a planned item is compiled both ways in the
    /// same process, and a difference between the two fails its compile.
    Check,
    /// Not a value of the switch: the path of one unit after
    /// [`DerivedRetry`]. Every item of the unit is on the general path.
    Fallback,
}

impl DerivedPath {
    /// Read the switch once per process; later calls are O(1). A value that
    /// is not one of the three ends the process with a message.
    pub fn from_env() -> DerivedPath {
        static PATH: std::sync::OnceLock<DerivedPath> = std::sync::OnceLock::new();
        *PATH.get_or_init(|| match std::env::var("RESCRIPT_DERIVED_PATH").as_deref() {
            Err(_) | Ok("") => DerivedPath::Plans,
            Ok("general") => DerivedPath::General,
            Ok("check") => DerivedPath::Check,
            Ok(other) => {
                eprintln!(
                    "RESCRIPT_DERIVED_PATH is `{other}`; it is unset, `general` or `check`"
                );
                std::process::exit(2)
            }
        })
    }
}

impl crate::types::context::CheckMode {
    /// O(1) per unit after the first environment read. `explain` disables the
    /// success attempt for diagnostic comparisons and regression bisection.
    fn from_env() -> Self {
        static MODE: std::sync::OnceLock<crate::types::context::CheckMode> = std::sync::OnceLock::new();
        *MODE.get_or_init(|| match std::env::var("RESCRIPT_CHECK_MODE").as_deref() {
            Err(_) | Ok("") => Self::Success,
            Ok("explain") => Self::Explain,
            Ok(other) => {
                eprintln!("RESCRIPT_CHECK_MODE is `{other}`; it is unset or `explain`");
                std::process::exit(2)
            }
        })
    }
}

impl DerivedPath {
    /// Why the derive seam plans no item of a unit on this path, or `None`
    /// when it plans. Cost: O(1).
    pub fn plans_off(self) -> Option<crate::binary_ast::derive::GeneralReason> {
        use crate::binary_ast::derive::GeneralReason;
        match self {
            DerivedPath::Plans | DerivedPath::Check => None,
            DerivedPath::General => Some(GeneralReason::Switch),
            DerivedPath::Fallback => Some(GeneralReason::FailedObligation),
        }
    }
}

/// See [`CompilerOptions::derived_reference`].
pub type DerivedReference =
    std::sync::Arc<dyn Fn() -> Result<(crate::parse_arena::ParseArena, Structure)> + Send + Sync>;

/// The syntax of a unit with every derived item as code
/// ([`DerivedPath::Fallback`]): what a unit is checked from once a plan of
/// it could not be used. Made by whoever holds the unit's source.
pub struct GeneralSyntax<S> {
    /// Node storage of `tree`, ready for type checking.
    pub arena: crate::parse_arena::ParseArena,
    /// The unit's tree after the frontend.
    pub tree: S,
    /// For a location-free `arena`: its located parse, in which warnings
    /// are placed ([`CompilerOptions::warning_locations`] of this syntax).
    pub warning_locations: Option<WarningLocations>,
}

/// Borrowed general-syntax provider, called only after a derived plan fails.
/// O(1) to pass; no ownership or allocation on the successful first attempt.
pub type DerivedFallback<'a> = &'a dyn Fn() -> Result<GeneralSyntax<Structure>>;

/// See [`CompilerOptions::derived_differences`].
pub type DerivedDifferences = std::sync::Arc<std::sync::Mutex<Vec<String>>>;

/// Unit checker selection; the old checker remains the default during construction.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum CheckerChoice {
    /// Use the existing checker.
    #[default]
    Old,
    /// Offer units to the new checker first.
    New,
    /// Compare both checkers on covered units.
    Both,
}

impl CheckerChoice {
    /// O(1): parse one of three fixed-length mode names.
    fn parse(value: &str) -> Option<Self> {
        match value {
            "" | "old" => Some(Self::Old),
            "new" => Some(Self::New),
            "both" => Some(Self::Both),
            _ => None,
        }
    }

    /// O(1) after the first call; reads the environment once per process.
    pub fn from_env() -> Self {
        static CHOICE: std::sync::OnceLock<CheckerChoice> = std::sync::OnceLock::new();
        *CHOICE.get_or_init(|| {
            let value = std::env::var("RESCRIPT_CHECKER").unwrap_or_default();
            Self::parse(&value).unwrap_or_else(|| {
                eprintln!("checker choice must be old, new or both; got `{value}`");
                std::process::exit(2)
            })
        })
    }
}

#[cfg(test)]
mod checker_choice_tests {
    use super::CheckerChoice;

    #[test]
    fn checker_choice_names_and_layout() {
        assert_eq!(std::mem::size_of::<CheckerChoice>(), 1);
        assert_eq!(CheckerChoice::parse(""), Some(CheckerChoice::Old));
        assert_eq!(CheckerChoice::parse("old"), Some(CheckerChoice::Old));
        assert_eq!(CheckerChoice::parse("new"), Some(CheckerChoice::New));
        assert_eq!(CheckerChoice::parse("both"), Some(CheckerChoice::Both));
        assert_eq!(CheckerChoice::parse("other"), None);
    }

    /// The names check starts a capture under `Both` only, and a panic in the
    /// checked unit leaves no capture running.
    #[cfg(debug_assertions)]
    #[test]
    fn only_both_captures_the_names_of_a_unit() {
        use super::names_replayed;
        use crate::tc::scope_trace::on;
        for choice in [CheckerChoice::Old, CheckerChoice::New] {
            assert_eq!(names_replayed(choice, "Unit", on), Ok(false));
        }
        assert_eq!(names_replayed(CheckerChoice::Both, "Unit", on), Ok(true));
        assert!(!on());
        let panicked = std::panic::catch_unwind(|| {
            names_replayed(CheckerChoice::Both, "Unit", || panic!("unit failed"))
        });
        assert!(panicked.is_err());
        assert!(!on());
    }

    #[test]
    fn both_compares_fake_observations_but_does_not_force_declined_ones() {
        use super::checker_results_agree;
        use crate::tc::Declined;
        // Signature, ordered diagnostics, and unit reads are independent observations.
        let old = ("signature", "warning:1:2", [3, 5]);
        assert!(checker_results_agree(Ok(old), || old));
        assert!(!checker_results_agree(Ok(("different", old.1, old.2)), || old));
        assert!(!checker_results_agree(Ok((old.0, "warning:2:3", old.2)), || old));
        assert!(!checker_results_agree(Ok((old.0, old.1, [3, 6])), || old));
        assert!(checker_results_agree::<()>(Err(Declined::NotBuilt), || panic!("declined")));
    }
}

/// O(1) on a decline; otherwise the cost of producing and comparing observations.
/// The old observations are lazy: declined units need no canonicalization.
fn checker_results_agree<T: PartialEq>(
    new: Result<T, crate::tc::Declined>,
    old: impl FnOnce() -> T,
) -> bool {
    match new {
        Err(crate::tc::Declined::NotBuilt) => true,
        Ok(new) => new == old(),
    }
}

/// O(1) per unit, before the old checker can emit warnings or publish anything.
/// No successful new result exists in R0; Both's comparison is consequently empty.
fn offer_unit_to_checker(choice: CheckerChoice, filename: &str) {
    if choice == CheckerChoice::Old {
        return;
    }
    let new = crate::tc::check_unit();
    let Err(reason) = new;
    log::debug!(target: "rescript_checker", "tc-declined {reason:?} {filename}");
    if choice == CheckerChoice::Both {
        assert!(checker_results_agree(new.map(|never| match never {}), || ()));
    }
}

/// Compiler options that can be passed to the driver.
#[derive(Clone)]
pub struct CompilerOptions {
    /// Selected once at setup; all modes currently use the old checker.
    pub checker: CheckerChoice,
    /// Optional derived-code census output, read once when options are created.
    pub derived_census: Option<PathBuf>,
    /// The path derived items take, read once when options are created.
    pub derived_path: DerivedPath,
    /// For `RESCRIPT_DERIVED_PATH=check`: the frontend's result for the
    /// unit's source with [`DerivedPath::General`], ready for type checking,
    /// or why the frontend could not give it (the error names the source it
    /// read). The reference compile of a check runs on it.
    pub derived_reference: Option<DerivedReference>,
    /// For `RESCRIPT_DERIVED_PATH=check`: where a build collects what the
    /// check found, to report every unit before it fails. With it a unit
    /// that differs goes on with the result of its plans; without it the
    /// first difference fails the unit's compile. Locked once per
    /// difference, never for a unit that passes.
    pub derived_differences: Option<DerivedDifferences>,
    /// Dormant backend migration mode, selected before compiling modules.
    pub backend: crate::bir::shadow::BackendMode,
    /// Dormant publication equality oracle; configured once, not per unit.
    pub signature_check: Option<crate::cmi::signature_check::SignatureCheck>,
    /// Experimental JavaScript printer, selected once when options are created.
    pub js_printer: crate::emit::PrinterMode,
    /// Stop after typing and publish the interface without generating code.
    pub check_only: bool,
    /// Print the Lambda IR to stderr (like OCaml's -drawlambda)
    pub dump_lambda: bool,
    /// Print the typed tree as sexp to stderr (like OCaml's -dtyped-sexp)
    pub dump_typed_sexp: bool,
    /// Print the typed tree as sexp with locations to stderr (like OCaml's -dtyped-sexp-locs)
    pub dump_typed_sexp_locs: bool,
    /// Print the Lambda IR as sexp to stderr (like OCaml's -dlambda-sexp)
    pub dump_lambda_sexp: bool,
    /// Print the Lambda IR as sexp with locations to stderr (like OCaml's -dlambda-sexp-locs)
    pub dump_lambda_sexp_locs: bool,
    /// Include paths for finding .cmi files (from -I flags)
    pub include_paths: Vec<PathBuf>,
    /// Runtime package path (from -runtime-path flag)
    /// Used to locate stdlib CMIs at {runtime_path}/lib/rescript/
    pub runtime_path: Option<PathBuf>,
    /// Additional modules opened implicitly from `-open` flags.
    pub open_modules: Vec<String>,
    /// Record what an in-process compile read of other units
    /// (`unit_reads` of the results), for incremental builds.
    pub collect_unit_reads: bool,
    /// For a location-free compile: parse the same source again with
    /// locations (the same frontend included). Warnings are then placed in
    /// that parse instead of compiling the unit a second time.
    pub warning_locations: Option<WarningLocations>,
    /// Warning enable/disable specs from `-w` flags.
    pub warning_specs: Vec<String>,
    /// Warning-as-error specs from `-warn-error` flags.
    pub warning_error_specs: Vec<String>,
    /// Source filename for interface constraint propagation.
    /// When set, after type_structure, checks for a matching .cmi and
    /// unifies implementation value types with interface types.
    pub source_filename: Option<String>,
    /// Output path used for module-format and relative-import resolution.
    pub output_path: Option<PathBuf>,
    /// Output module format from the build config. When absent, legacy callers
    /// infer it from `output_path`.
    pub output_module_format: Option<crate::js_ir::ModuleFormat>,
    /// Extra concrete JS outputs for in-process callers that need the same
    /// typed/lambda result rendered for multiple package specs.
    pub js_output_targets: Vec<JsOutputTarget>,
    /// The package's `-bs-package-output` specs, which import paths follow
    /// (see `js_ir::JsPackageSpec`).
    pub js_package_specs: Vec<crate::js_ir::JsPackageSpec>,
    /// Source map output mode.
    pub source_map: crate::js_ir::source_map::SourceMapMode,
    /// Include original source text in generated source maps.
    pub source_map_sources_content: bool,
    /// Optional sourceRoot emitted in generated source maps.
    pub source_map_root: String,
    /// JSX version from CLI `-bs-jsx` (e.g. 4). When set, enables JSX PPX rewrite.
    pub jsx_version: Option<i32>,
    /// JSX module from CLI `-bs-jsx-module` (`Js_config.jsx_module`); `None`
    /// is OCaml's default `React`.
    pub jsx_module: Option<String>,
    /// Experimental LetUnwrap feature from `-enable-experimental LetUnwrap`.
    pub experimental_let_unwrap: bool,
    /// Preserve transformed JSX syntax in the final JS dumper.
    pub jsx_preserve: bool,
    /// Enable debug-mode JS emission (like OCaml's -bs-g / Js_config.debug).
    pub debug: bool,
    /// Suppress the generated version/header comment (`-bs-no-version-header`).
    pub no_version_header: bool,
    /// Mirror `Js_config.check_div_by_zero` for checked integer/bigint lowering.
    pub check_div_by_zero: bool,
    /// Mirror `Js_config.cross_module_inline` / `-bs-cross-module-opt`.
    pub cross_module_inline: bool,
    /// Mirror `Clflags.no_assert_false` / `-bs-noassertfalse`.
    pub no_assert_false: bool,
    /// Mirror `Clflags.noassert` / `-noassert`.
    pub noassert: bool,
    /// Mirror `Clflags.transparent_modules` / `-no-alias-deps`.
    pub transparent_modules: bool,
    /// Mirror `Js_config.no_builtin_ppx` / `-bs-no-builtin-ppx`.
    pub no_builtin_ppx: bool,
    /// Run the builtin Spice mapper in place of a configured spice PPX
    pub spice_ppx: bool,
    /// When true, do not implicitly open Pervasives and Stdlib.
    pub nopervasives: bool,
    /// The module name being compiled. Used to filter self-opens.
    pub module_name: Option<String>,
    /// Current npm package name from `-bs-package-name`.
    pub package_name: Option<String>,
    /// Source package root, used only to derive relocation-stable declaration
    /// identities as package name plus the path within the package.
    pub package_root: Option<PathBuf>,
    /// Compile the runtime package (`-make-runtime`).
    pub make_runtime: bool,
    /// Mirror `Clflags.assume_no_mli := Mli_exists` from `-bs-read-cmi`.
    pub assume_compiled_interface: bool,
    /// GenType configuration derived from `-bs-gentype-*` flags.
    pub gentype_config: Option<std::sync::Arc<crate::gentype::config::T>>,
    /// Build-scoped GenType module resolver shared by in-process compilations.
    pub gentype_resolver: Option<std::sync::Arc<crate::gentype::module_resolver::Resolver>>,
    /// Run GenType only to register the module's type declarations (for the
    /// modules that import its types), without generating output.
    pub gentype_declarations_only: bool,
    /// The build's conservative dependency closure can prove this module's
    /// declarations unreachable from every genType output. Standalone compiles
    /// default to true because they have no whole-build dependency graph.
    pub gentype_declarations_needed: bool,
    /// When true, `compile_source_in_process` captures the typed tree,
    /// raw lambda, and lambda sexps for display (used by the playground).
    pub capture_intermediates: bool,
    /// Intermediate representations an in-process compile captures into its
    /// result's `dumps`, in this order.
    pub dumps: Vec<DumpKind>,
    /// Build typed/lambda/JS IR metadata but skip rendering JavaScript text.
    /// Used by runtime seeding, which only needs signatures, purity, and
    /// closed constants in memory.
    pub skip_js_render: bool,
    /// Publish a portable in-process signature for downstream module lookup.
    /// Rewatch can disable this for implementations whose interface already
    /// supplies the published signature. OCaml still saves before Lambda translation
    /// (`compiler/ml/typemod.ml:1779-1788`; `compiler/ml/translmod.ml:267`);
    /// this only skips the Rust-only portable registry extraction when no
    /// downstream lookup can observe it.
    pub publish_in_process_signature: bool,
    /// The input is a `.ast`/`.iast` written by `bsc -bs-ast`. OCaml reads the
    /// already-preprocessed tree (compiler/core/js_implementation.ml:189-196),
    /// so frontend warnings were reported by the `-bs-ast` run and are not
    /// repeated. Rust re-runs the frontend from source, silently.
    pub frontend_already_reported: bool,
    /// Package roots whose in-process units are on the load path (the `-I`
    /// directories of a file build). `None` makes every registered unit visible.
    pub visible_package_roots: Option<Vec<PathBuf>>,
    /// `Clflags.keep_locs` (`-keep-locs`/`-no-keep-locs`): whether saved
    /// signatures keep source locations (subst.ml:57-67 `Subst.for_saving`).
    pub keep_locs: bool,
}

/// `Subst.signature (Subst.for_saving ...)` with `Clflags.keep_locs = false`
/// (subst.ml:57-67): saved signatures replace every location, including the
/// attributes', with `Location.none`.
fn strip_saved_signature_locations(sig: &mut [crate::types::decl::SignatureItem]) {
    use crate::types::decl::{Attribute, SignatureLocationVisitor};
    // `Subst.loc` and `Subst.attrs` (compiler/ml/subst.ml:57-67).
    struct Strip;
    impl SignatureLocationVisitor for Strip {
        fn location(&mut self, loc: &mut crate::types::DeclLoc) {
            *loc = crate::types::DeclLoc::none();
        }
        fn attribute(&mut self, attr: &mut Attribute) {
            self.location(&mut attr.attr_loc);
            self.location(&mut attr.attr_name.loc);
            if let Some(loc) = attr.attr_payload.invalid_escape_loc_mut() {
                self.location(loc);
            }
        }
    }
    crate::types::decl::walk_signature_locations(sig, &mut Strip);
}

/// `bsc -format` (rescript_compiler_main.ml:168-182 via
/// res_multi_printer.ml:1-30): parse `.res`/`.resi` source in printer mode and
/// print it back with its comments. Sources are Latin-1 byte strings like the
/// parser's input; the result keeps the original byte encoding. A file with
/// parse errors fails with the diagnostic report (`Res_diagnostics.print_report`).
pub fn format_source(source: &[u8], filename: &str) -> std::result::Result<Vec<u8>, String> {
    let (report, output) = format_source_with(source, filename, false);
    output.ok_or(report)
}

/// `Res_multi_printer.print ~ignore_parse_errors`: the parse diagnostics
/// report (empty without errors) and the formatted source, which is `None`
/// when parse errors are not ignored.
pub fn format_source_with(
    source: &[u8],
    filename: &str,
    ignore_parse_errors: bool,
) -> (String, Option<Vec<u8>>) {
    // res_multi_printer.ml: parse the source as it is and print the line
    // breaks the printer writes with the newline of the parsed source.
    let raw_source = crate::source_text::latin1_bytes_to_string(source.to_vec());
    let source: &str = &raw_source;
    let is_interface = filename.ends_with(".resi");
    let mut parser = Parser::new(filename, source);
    let (report, output) = if is_interface {
        let signature = module::parse_signature(&mut parser);
        let report = parse_diagnostics_report(&parser, source, filename);
        if parser.has_errors() && !ignore_parse_errors {
            return (report, None);
        }
        let comments = parser.comments().to_vec();
        let newline = parser.newline();
        let output = crate::parser::printer::print_signature_with_comments(
            &signature,
            comments,
            newline,
            parser.arena_mut(),
        );
        (report, output)
    } else {
        let structure = module::parse_structure(&mut parser);
        let report = parse_diagnostics_report(&parser, source, filename);
        if parser.has_errors() && !ignore_parse_errors {
            return (report, None);
        }
        let comments = parser.comments().to_vec();
        let newline = parser.newline();
        let output = crate::parser::printer::print_structure_with_comments(
            &structure,
            comments,
            newline,
            parser.arena_mut(),
        );
        (report, output)
    };
    // res_multi_printer.ml:31-34: keep a byte order mark, which the scanner
    // skips.
    let bom = crate::parser::scanner::byte_order_mark(source);
    (
        report,
        Some(bom.chars().chain(output.chars()).map(|c| c as u8).collect()),
    )
}

fn parse_diagnostics_report(parser: &Parser<'_>, source: &str, filename: &str) -> String {
    let report: String = parser
        .diagnostics()
        .iter()
        .map(|diag| {
            code_frame::format_error(
                filename,
                source,
                &diag.start_pos,
                &diag.end_pos,
                &diag.explain_with_source(Some(source)),
            )
        })
        .collect();
    // Source text is Latin-1 chars standing for bytes; the frame adds real
    // Unicode (box drawing). Write each back as the bytes OCaml prints.
    let mut bytes = Vec::with_capacity(report.len());
    for c in report.chars() {
        if (c as u32) <= 0xFF {
            bytes.push(c as u8);
        } else {
            let mut buf = [0u8; 4];
            bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        }
    }
    String::from_utf8_lossy(&bytes).into_owned()
}

impl CompilerOptions {
    /// O(path bytes), one owned identity per compilation when package metadata
    /// exists, otherwise borrow the standalone filename. Never called per node.
    fn location_identity<'a>(&self, filename: &'a str) -> std::borrow::Cow<'a, str> {
        let (Some(package), Some(root)) = (&self.package_name, &self.package_root) else {
            return std::borrow::Cow::Borrowed(filename);
        };
        // Package discovery supplies normalized roots and source paths. Check
        // the separator boundary in bytes instead of walking every component
        // again for every implementation/interface compilation.
        let relative = root.to_str().and_then(|root| {
            let suffix = filename.strip_prefix(root)?;
            if root.ends_with(std::path::is_separator) || suffix.is_empty() {
                Some(suffix)
            } else {
                suffix.strip_prefix(std::path::is_separator)
            }
        }).unwrap_or(filename);
        #[cfg(windows)]
        let relative = relative.replace('\\', "/");
        std::borrow::Cow::Owned(format!("{package}/{relative}"))
    }

    /// Read the census switch once per process. Subsequent option creation is
    /// O(1) when disabled, or O(path bytes) to copy an enabled output path.
    pub fn derived_census_from_env() -> Option<PathBuf> {
        static OUTPUT: std::sync::OnceLock<Option<PathBuf>> = std::sync::OnceLock::new();
        OUTPUT.get_or_init(|| {
            let path = std::env::var_os("RESCRIPT_DERIVED_CENSUS").map(PathBuf::from);
            if path.is_some() { crate::timing::enable_for_census(); }
            path
        }).clone()
    }
}

impl Default for CompilerOptions {
    fn default() -> Self {
        Self {
            checker: CheckerChoice::from_env(),
            derived_census: Self::derived_census_from_env(),
            derived_path: DerivedPath::from_env(),
            derived_reference: None,
            derived_differences: None,
            backend: crate::bir::shadow::BackendMode::from_env(),
            signature_check: crate::cmi::signature_check::SignatureCheck::from_env(),
            js_printer: crate::emit::PrinterMode::from_env(),
            check_only: false,
            dump_lambda: false,
            dump_typed_sexp: false,
            dump_typed_sexp_locs: false,
            dump_lambda_sexp: false,
            dump_lambda_sexp_locs: false,
            include_paths: Vec::new(),
            runtime_path: None,
            open_modules: Vec::new(),
            collect_unit_reads: false,
            warning_locations: None,
            warning_specs: Vec::new(),
            warning_error_specs: Vec::new(),
            source_filename: None,
            output_path: None,
            output_module_format: None,
            js_output_targets: Vec::new(),
            js_package_specs: Vec::new(),
            source_map: crate::js_ir::source_map::SourceMapMode::None,
            source_map_sources_content: false,
            source_map_root: String::new(),
            jsx_version: None,
            jsx_module: None,
            experimental_let_unwrap: false,
            jsx_preserve: false,
            debug: false,
            no_version_header: false,
            check_div_by_zero: true,
            cross_module_inline: false,
            no_assert_false: false,
            noassert: false,
            transparent_modules: false,
            no_builtin_ppx: false,
            spice_ppx: false,
            nopervasives: false,
            module_name: None,
            package_name: None,
            package_root: None,
            make_runtime: false,
            assume_compiled_interface: false,
            gentype_config: None,
            gentype_resolver: None,
            gentype_declarations_only: false,
            gentype_declarations_needed: true,
            capture_intermediates: false,
            dumps: Vec::new(),
            skip_js_render: false,
            publish_in_process_signature: true,
            frontend_already_reported: false,
            visible_package_roots: None,
            keep_locs: true,
        }
    }
}

impl CompilerOptions {
    /// Whether the built-in spice derive rewrites the current AST directly.
    pub fn builtin_spice(&self) -> bool {
        self.spice_ppx
    }

    /// `Env.get_unit_name ()`: js_implementation.ml sets it to
    /// `Ext_filename.module_name outputprefix`, the module name the build
    /// registers the file under.
    fn current_unit_name(&self) -> Option<String> {
        self.module_name.clone().or_else(|| {
            self.source_filename
                .as_deref()
                .map(module_name_from_source_filename)
                .filter(|name| !name.is_empty())
        })
    }
}

fn apply_warning_options(tctx: &mut TypeCheckContext<'_>, options: &CompilerOptions) {
    for spec in &options.warning_specs {
        tctx.apply_warning_spec(spec);
    }
    for spec in &options.warning_error_specs {
        tctx.apply_warning_error_spec(spec);
    }
}

fn apply_warning_specs_to_config(
    config: &mut WarningConfig,
    warning_specs: &[String],
    warning_error_specs: &[String],
) {
    apply_warning_ops_to_config(
        config,
        warning_specs
            .iter()
            .map(|spec| (false, spec.as_str()))
            .chain(warning_error_specs.iter().map(|spec| (true, spec.as_str()))),
    );
}

/// Apply `(as_error, spec)` warning operations in order. Malformed specs are
/// skipped, leaving the configuration unchanged for them.
fn apply_warning_ops_to_config<'a>(
    config: &mut WarningConfig,
    ops: impl IntoIterator<Item = (bool, &'a str)>,
) {
    for (as_error, spec) in ops {
        let _ = if as_error {
            config.parse_as_error(spec)
        } else {
            config.parse(spec)
        };
    }
}

/// Apply `(as_error, spec)` warning operations to the type checker's state.
fn apply_warning_ops<'a>(
    tctx: &mut TypeCheckContext<'_>,
    ops: impl IntoIterator<Item = (bool, &'a str)>,
) {
    for (as_error, spec) in ops {
        if as_error {
            tctx.apply_warning_error_spec(spec);
        } else {
            tctx.apply_warning_spec(spec);
        }
    }
}

fn apply_file_config_warning_options(
    tctx: &mut TypeCheckContext<'_>,
    config: &FileConfigOverrides,
) {
    apply_warning_ops(tctx, file_config_warning_ops(config));
}

fn apply_leading_warning_attribute_options(
    tctx: &mut TypeCheckContext<'_>,
    specs: &[ppx::WarningAttributeSpec],
) {
    apply_warning_ops(tctx, leading_warning_ops(specs));
}

fn file_config_warning_ops(config: &FileConfigOverrides) -> impl Iterator<Item = (bool, &str)> {
    config
        .warning_ops
        .iter()
        .map(|(as_error, spec)| (*as_error, spec.as_str()))
}

fn leading_warning_ops(specs: &[ppx::WarningAttributeSpec]) -> impl Iterator<Item = (bool, &str)> {
    specs.iter().map(|spec| (spec.as_error, spec.spec.as_str()))
}

fn warning_config_for_options(options: &CompilerOptions) -> WarningConfig {
    let mut config = WarningConfig::new();
    apply_warning_specs_to_config(
        &mut config,
        &options.warning_specs,
        &options.warning_error_specs,
    );
    config
}

/// The warning state when `Ast_config.process_str` first runs: command-line
/// options plus the leading `@@warning` attributes applied by
/// `Bs_ast_invariant.iter_warnings_on_stru` (compiler/frontend/ppx_entry.ml:46-48).
fn warning_config_for_options_and_leading_attrs(
    options: &CompilerOptions,
    leading_specs: &[ppx::WarningAttributeSpec],
) -> WarningConfig {
    let mut config = warning_config_for_options(options);
    apply_warning_ops_to_config(&mut config, leading_warning_ops(leading_specs));
    config
}

fn warning_config_for_options_file_config_and_leading_attrs(
    options: &CompilerOptions,
    file_config: &FileConfigOverrides,
    leading_specs: &[ppx::WarningAttributeSpec],
) -> WarningConfig {
    // OCaml compiler/frontend/ppx_entry.ml:28-47 calls
    // Bs_ast_invariant.iter_warnings_on_stru/sigi before builtin PPX
    // rewriting; those leading attributes mutate Warnings.current before
    // @deriving and external warnings are emitted.
    let mut config = warning_config_for_options_and_leading_attrs(options, leading_specs);
    apply_file_config_warning_ops(&mut config, file_config);
    config
}

fn apply_file_config_warning_ops(config: &mut WarningConfig, file_config: &FileConfigOverrides) {
    apply_warning_ops_to_config(config, file_config_warning_ops(file_config));
}

/// `Js_config.string_of_jsx_module !Js_config.jsx_module`
/// (compiler/common/js_config.ml:66-76): the module the JSX rewrite targets.
/// File-level `@@config` flags are parsed after the command line, so they win.
pub fn jsx_module_name<'a>(
    options: &'a CompilerOptions,
    file_config: Option<&'a FileConfigOverrides>,
) -> &'a str {
    let configured = file_config
        .and_then(|config| config.jsx_module.as_deref())
        .or(options.jsx_module.as_deref());
    match configured {
        Some(module) if !module.eq_ignore_ascii_case("react") => module,
        _ => "react",
    }
}

/// `-bs-jsx-module` (compiler/bsc/rescript_compiler_main.ml:267-276): set the
/// JSX module; any module but `react` is generic JSX, which implies JSX v4.
pub fn apply_jsx_module_flag(
    module: &str,
    jsx_module: &mut Option<String>,
    jsx_version: &mut Option<i32>,
) {
    *jsx_module = Some(module.to_string());
    if !module.eq_ignore_ascii_case("react") {
        *jsx_version = Some(4);
    }
}

/// The JSX version: the command line's, else 4 when the file's
/// `@@config` sets `-bs-jsx` (or a generic `-bs-jsx-module`).
pub fn jsx_version_for_structure(
    structure: &Structure,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> Option<i32> {
    options
        .jsx_version
        .or_else(|| extract_file_config_from_structure(structure, arena).jsx_version)
}

/// Whether `let?` is enabled, by the command line or the file's
/// `@@config`.
pub fn experimental_let_unwrap_for_structure(
    structure: &Structure,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    options.experimental_let_unwrap
        || extract_file_config_from_structure(structure, arena).let_unwrap
}

/// `builtin_ppx_warnings` receives the warnings the JSX and builtin mappers
/// print, including those emitted before a mapper error.
fn preprocess_signature_for_typecheck_with_source(
    signature: Signature,
    options: &CompilerOptions,
    file_config: &FileConfigOverrides,
    arena: &mut crate::parse_arena::ParseArena,
    source: &str,
    filename: &str,
    builtin_ppx_warnings: &mut Vec<ppx::PpxWarning>,
) -> Result<Signature> {
    // Ppx_entry.rewrite_signature reads the JSX settings after
    // `Ast_config.process_sig` (compiler/frontend/ppx_entry.ml:27-37).
    let signature = if let Some(jsx_version) = options.jsx_version.or(file_config.jsx_version) {
        // The JSX warnings come first, those raised before an error included.
        let (signature, jsx_warnings) = jsx_ppx::transform_signature_collecting_warnings(
            signature,
            jsx_version,
            jsx_module_name(options, Some(file_config)),
            arena,
        );
        builtin_ppx_warnings.extend(jsx_preprocessor_warnings_to_ppx(arena, jsx_warnings));
        signature.map_err(|e| jsx_ppx_error_to_anyhow(e, arena, source, filename))?
    } else {
        signature
    };

    if file_config.no_builtin_ppx(options) {
        Ok(signature)
    } else {
        arena.set_builtin_spice(options.builtin_spice());
        let (rewritten, warnings) =
            ppx::rewrite_signature_with_warnings(
                &signature,
                arena,
                options.experimental_let_unwrap || file_config.let_unwrap,
            );
        builtin_ppx_warnings.extend(warnings);
        rewritten.map_err(|e| ppx_error_to_anyhow(e, arena, source, filename))
    }
}

fn ppx_error_to_anyhow(
    err: ppx::PpxError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    let mut prefix = String::new();
    for warning in err.warnings() {
        prefix.push_str(&format_compiler_warning_report(
            arena,
            source,
            filename,
            &TypeCoreWarning {
                loc: warning.loc,
                warning: warning.warning.clone(),
                is_error: false,
            },
        ));
    }
    if err.loc().is_none() && err.message_text().starts_with("Fatal error: exception ") {
        return UserDiagnostic::new(format!("{prefix}{}", err.message_text()), 2).into();
    }
    if let Some(loc) = err.loc() {
        let message = err.message_text();
        let mut report = if message.contains('\n') {
            let mut raw_message = String::with_capacity(message.len() + 2);
            raw_message.push_str("  ");
            raw_message.push_str(message);
            format_compiler_error_report_raw_message(arena, source, filename, loc, &raw_message)
        } else {
            format_compiler_error_report(arena, source, filename, loc, message)
        };
        if !prefix.is_empty() {
            report.insert_str(0, &prefix);
        }
        UserDiagnostic::new(report, 2).into()
    } else {
        let mut report = format_compiler_error_report_for_file(filename, err.message_text());
        if !prefix.is_empty() {
            report.insert_str(0, &prefix);
        }
        UserDiagnostic::new(report, 2).into()
    }
}

fn jsx_ppx_error_to_anyhow(
    err: jsx_ppx::JsxPreprocessorError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    let loc = arena.to_location(err.loc);
    // Location.print_loc (location.ml:75-92) prints the location's own
    // pos_fname; a range-less `Location.in_file file_name` (jsx_v4.ml
    // empty_loc) names the module rather than the source file.
    let loc_file = arena.get_string(loc.loc_start.file_name);
    let filename =
        if !code_frame::has_printable_range(&loc.loc_start, &loc.loc_end) && !loc_file.is_empty() {
            loc_file
        } else {
            filename
        };
    let output = match err.message_style {
        jsx_ppx::JsxPreprocessorMessageStyle::PrefixedLines => {
            format_compiler_error_report_from_location(source, filename, &loc, &err.message)
        }
        jsx_ppx::JsxPreprocessorMessageStyle::FirstLineOnlyPrefix => {
            let mut output = String::new();
            push_compiler_error_report_header_from_location(&mut output, source, filename, &loc);
            for (idx, line) in err.message.lines().enumerate() {
                if idx == 0 {
                    output.push_str("  ");
                }
                output.push_str(line);
                output.push('\n');
            }
            output.push('\n');
            output
        }
    };
    UserDiagnostic::new(output, 2).into()
}

fn jsx_preprocessor_warnings_to_ppx(
    arena: &mut ParseArena,
    warnings: Vec<jsx_ppx::JsxPreprocessorWarning>,
) -> Vec<ppx::PpxWarning> {
    warnings
        .into_iter()
        .map(|warning| ppx::PpxWarning {
            loc: arena.mk_loc_from_positions(&warning.start_pos, &warning.end_pos),
            // jsx_common.ml reports a deprecated payload through
            // `Location.deprecated`, everything else as a preprocessor warning.
            warning: if warning.deprecated {
                crate::diagnostics::Warning::Deprecated {
                    message: warning.message,
                    def_loc: crate::location::Location::none(),
                    use_loc: crate::location::Location::none(),
                    can_be_automigrated: false,
                }
            } else {
                crate::diagnostics::Warning::Preprocessor {
                    message: warning.message,
                }
            },
        })
        .collect()
}

/// Parser warnings (e.g. the deprecated `(. ...)` syntax) are reported by OCaml
/// through `Location.prerr_warning` while parsing, under the command-line warning
/// settings (compiler/syntax/src/res_core.ml:291-298). Emit them before any syntax
/// errors and report whether one was configured as an error.
pub fn emit_parser_warnings(
    parser: &mut Parser<'_>,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> bool {
    let mut out = String::new();
    let has_error = format_parser_warnings(parser, source, filename, options, &mut out);
    write_stderr(&out);
    has_error
}

fn write_stderr(output: &str) {
    if !output.is_empty() {
        write_stderr_raw(&crate::source_text::decode_internal_utf8_runs(output));
    }
}

/// Write `output` to stderr as is. Failures to write diagnostics are ignored.
fn write_stderr_raw(output: &str) {
    let mut stderr = std::io::stderr();
    let _ = std::io::Write::write_all(&mut stderr, output.as_bytes());
    let _ = std::io::Write::flush(&mut stderr);
}

/// Like [`emit_parser_warnings`], appending the reports to `out`.
fn format_parser_warnings(
    parser: &mut Parser<'_>,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    out: &mut String,
) -> bool {
    let parser_warnings = parser.warnings().to_vec();
    if parser_warnings.is_empty() {
        return false;
    }
    let mut warnings = Vec::with_capacity(parser_warnings.len());
    for warning in parser_warnings {
        let message = match warning.kind {
            crate::parser::ParserWarningKind::DeprecatedUncurriedDotSyntax => {
                "The `(. ...)` uncurried syntax is deprecated. Uncurried is now the default in ReScript — remove the leading dot.".to_string()
            }
        };
        let arena = parser.arena_mut();
        let start = arena.push_position(warning.start_pos);
        let end = arena.push_position(warning.end_pos);
        let loc = arena.mk_loc(start, end);
        let location = arena.to_location(loc);
        warnings.push(ppx::PpxWarning {
            loc,
            warning: crate::diagnostics::Warning::Deprecated {
                message,
                def_loc: location,
                use_loc: location,
                can_be_automigrated: false,
            },
        });
    }
    let warning_config = warning_config_for_options(options);
    format_ppx_warnings_with_config(
        parser.arena(),
        source,
        filename,
        &warning_config,
        &warnings,
        out,
    )
}

/// The builtin mapper's warnings under the default warning settings, as
/// `Location.prerr_warning` prints them in a tool that sets no `-w` flags,
/// such as `res_parser` (compiler/ext/warnings.ml:266-267 applies
/// `Bsc_warnings.defaults_w` when the module loads).
pub fn format_ppx_warnings(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warnings: &[ppx::PpxWarning],
) -> String {
    let mut out = String::new();
    format_ppx_warnings_with_config(
        arena,
        source,
        filename,
        &WarningConfig::new(),
        warnings,
        &mut out,
    );
    out
}

/// Append the active warnings' reports to `out`; returns whether one is an error.
fn format_ppx_warnings_with_config(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warning_config: &WarningConfig,
    warnings: &[ppx::PpxWarning],
    out: &mut String,
) -> bool {
    let mut has_error = false;
    for warning in warnings {
        if !warning_config.is_active(&warning.warning) {
            continue;
        }
        let is_error = warning_config.is_error(&warning.warning);
        has_error |= is_error;
        out.push_str(&format_compiler_warning_report(
            arena,
            source,
            filename,
            &TypeCoreWarning {
                loc: warning.loc,
                warning: warning.warning.clone(),
                is_error,
            },
        ));
    }
    has_error
}

/// Format a parser's syntax errors as a [`UserDiagnostic`].
pub fn parser_error_to_anyhow(parser: &Parser<'_>, source: &str, filename: &str) -> anyhow::Error {
    let mut output = String::new();
    for diagnostic in parser.diagnostics().iter() {
        output.push_str(&code_frame::format_error(
            filename,
            source,
            &diagnostic.start_pos,
            &diagnostic.end_pos,
            &diagnostic.explain_with_source(Some(source)),
        ));
    }
    UserDiagnostic::new(output, 1).into()
}

fn directive_payload_error_to_anyhow(
    err: DirectivePayloadError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    UserDiagnostic::new(
        format_compiler_error_report(arena, source, filename, err.loc, err.message),
        2,
    )
    .into()
}

/// Remove SGR style escapes (`ESC [ ... m`).
fn strip_style_escapes(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("\x1b[") {
        out.push_str(&rest[..start]);
        let after = &rest[start + 2..];
        match after.find('m') {
            Some(end)
                if after[..end]
                    .bytes()
                    .all(|b| b.is_ascii_digit() || b == b';') =>
            {
                rest = &after[end + 1..];
            }
            _ => {
                out.push_str("\x1b[");
                rest = after;
            }
        }
    }
    out.push_str(rest);
    out
}

fn type_mod_error_to_anyhow(
    err: TypeModError,
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    suppress_info_style: bool,
) -> anyhow::Error {
    let error = type_mod_error_to_anyhow_styled(
        err,
        type_ctx,
        arena,
        source,
        filename,
        suppress_info_style,
    );
    // The snippets the report re-parsed printed their parser warnings first
    // (`Error_message_utils.Parser.parse_source`, Location.prerr_warning).
    let reparse_warnings = format_reparse_warnings(type_ctx);
    let error = if reparse_warnings.is_empty() {
        error
    } else {
        match error.downcast::<UserDiagnostic>() {
            Ok(diagnostic) => UserDiagnostic {
                output: format!("{reparse_warnings}{}", diagnostic.output),
                exit_code: diagnostic.exit_code,
            }
            .into(),
            Err(error) => error,
        }
    };
    if !suppress_info_style {
        return error;
    }
    // OCaml compiler/ext/misc.ml:337-392: once a printed warning has run
    // `Location.setup_colors` with colors disabled, the style tags of later
    // error messages print nothing.
    match error.downcast::<UserDiagnostic>() {
        Ok(diagnostic) => UserDiagnostic {
            output: strip_style_escapes(&diagnostic.output),
            exit_code: diagnostic.exit_code,
        }
        .into(),
        Err(error) => error,
    }
}

/// The parser warnings of the snippets an error report re-parsed, at their
/// `<none>` locations (no code frame), as `Location.prerr_warning` prints
/// them.
fn format_reparse_warnings(type_ctx: &TypeContext) -> String {
    let warnings = type_ctx.take_reparse_warnings();
    if warnings.is_empty() {
        return String::new();
    }
    let config = type_ctx.report_warning_config();
    let mut output = String::new();
    for parser_warning in warnings {
        let warning = match parser_warning.kind {
            crate::parser::ParserWarningKind::DeprecatedUncurriedDotSyntax => {
                crate::diagnostics::Warning::Deprecated {
                    message: "The `(. ...)` uncurried syntax is deprecated. Uncurried is now the default in ReScript — remove the leading dot.".to_string(),
                    def_loc: crate::location::Location::none(),
                    use_loc: crate::location::Location::none(),
                    can_be_automigrated: false,
                }
            }
        };
        if !config.is_active(&warning) {
            continue;
        }
        let is_error = config.is_error(&warning);
        code_frame::mark_color_setup();
        output.push_str("\n  ");
        output.push_str(&code_frame::colorize_intro(
            &format!("Warning number {}", warning.number()),
            is_error,
        ));
        if is_error {
            output.push_str(" (configured as error) ");
        }
        output.push_str("\n  ");
        let location = code_frame::format_location(
            "<none>",
            &parser_warning.start_pos,
            &parser_warning.end_pos,
        );
        output.push_str(&code_frame::colorize_location(&location));
        output.push_str("\n\n  ");
        output.push_str(&warning.message());
        output.push_str("\n\n");
    }
    output
}

/// Run `f` with the typed environment recorded for an error, or an empty one
/// when none was captured. Error printers only read the environment.
fn with_typed_env_or_empty<R>(
    type_ctx: &TypeContext,
    env: Option<crate::types::typedtree::EnvRef>,
    f: impl FnOnce(&crate::types::Env) -> R,
) -> R {
    match env.and_then(|env| type_ctx.get_typed_env(env)) {
        Some(env) => f(&env),
        None => f(&crate::types::Env::empty()),
    }
}

fn type_mod_error_to_anyhow_styled(
    err: TypeModError,
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    suppress_info_style: bool,
) -> anyhow::Error {
    let err = match err {
        TypeModError::CoreError(TypeCoreError::ModuleError(module_error)) => {
            return type_mod_error_to_anyhow(
                *module_error,
                type_ctx,
                arena,
                source,
                filename,
                suppress_info_style,
            );
        }
        err => err,
    };
    match &err {
        TypeModError::CoreError(TypeCoreError::UncurriedArityMismatch {
            loc,
            function_type,
            expected_arity,
            provided_arity,
            provided_args,
            arity_suggestion,
            ..
        }) => UserDiagnostic::new(
            format_uncurried_arity_mismatch_report(
                type_ctx,
                ReportSite::new(arena, source, filename, *loc),
                *function_type,
                *expected_arity,
                *provided_arity,
                provided_args,
                arity_suggestion.as_deref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ConstructorArityMismatch {
            loc,
            name,
            is_inline_record,
            expected,
            provided,
        }) => UserDiagnostic::new(
            format_constructor_arity_mismatch_report(
                ReportSite::new(arena, source, filename, *loc),
                name,
                *is_inline_record,
                *expected,
                *provided,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::MultiplyBoundVariable { loc, name }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!("Variable {name} is bound several times in this pattern"),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IllegalValueName { loc, name }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!("'{name}' is not a valid value identifier."),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::OrpatVars {
            loc,
            id,
            valid_idents,
        }) => UserDiagnostic::new(
            format_orpat_vars_report(arena, source, filename, *loc, id, valid_idents),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::OrPatternTypeClash {
            loc,
            id,
            trace,
            env,
        }) => {
            let message = with_typed_env_or_empty(type_ctx, *env, |env| {
                type_clash::render_error_message(|ppf| {
                    type_clash::print_or_pattern_type_clash(ppf, type_ctx, env, id.name(), trace)
                })
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::BreakOutsideLoop { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "`break` can only be used directly inside a loop body.",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ContinueOutsideLoop { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "`continue` can only be used inside a loop body.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::BreakOutOfFinally { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "`break` cannot leave a `finally` block. Only a loop inside the block can be \
                 broken out of.",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ContinueOutOfFinally { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "`continue` cannot leave a `finally` block. Only a loop inside the block can \
                     be continued.",
                ),
                2,
            )
            .into()
        },
        TypeModError::CoreError(TypeCoreError::JsxComponentWithoutMake {
            loc,
            module_lid,
            alternatives,
        }) => {
            let mut message = format!(
                "The module {INFO}{module_lid}{RESET} can't be used as a JSX component, because it doesn't define {INFO}make{RESET}.\n\nA component module defines its component as {INFO}make{RESET}, for example:\n\n  {INFO}@react.component{RESET}\n  let make = (~label) => ..."
            );
            // typecore.ml report_error: `Typetexp.spellcheck_value`.
            if let Some(hint) = super_spellcheck_hint("make", alternatives) {
                message.push_str(&format!("\n\n{INFO}Hint: Did you mean {hint}?{RESET}"));
            }
            UserDiagnostic::new(
                format_compiler_error_report(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::JsxNotEnabled { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Cannot compile JSX expression because JSX support is not enabled. Add \"jsx\" settings to rescript.json to enable JSX support.",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ExtensionError(error)) => {
            UserDiagnostic::new(
                format_builtin_extension_error_report(arena, source, filename, error),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ExtensionAlreadyDisplayed) => {
            UserDiagnostic::new(String::new(), 2).into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidForLoopIndex { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Invalid for-loop index: only variables and _ are allowed.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidForOfPattern { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Invalid for...of binding: only variables and _ are allowed.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IllegalLetrecPat { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Only variables are allowed as left-hand side of `let rec`",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IllegalLetrecExpr { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This kind of expression is not allowed as right-hand side of `let rec`",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::EmptyRecordLiteral { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Empty record literal {} should be type annotated or used in a record context.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidInterval { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Only int and char intervals are supported in patterns.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NoValueClauses { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "None of the patterns in this switch match values.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ExceptionPatternBelowToplevel { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Exception patterns must be at the top level of a match case.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ModulesNotAllowed { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Modules are not allowed in this pattern.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::CannotInferSignature { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "The signature for this packaged module couldn't be inferred.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NotAPackedModule { loc, ty }) => {
            // typecore.ml:5438-5440.
            let ty = format_type_expr(type_ctx, *ty);
            UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &type_clash::render_error_message(|ppf| {
                    ppf.str("This expression is packed module, but the expected type is");
                    ppf.space();
                    crate::types::printtyp::pp_doc(ppf, &ty);
                }),
            ),
            2,
        )
        .into()
        }
        TypeModError::CoreError(TypeCoreError::InlinedRecordExpected { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This constructor expects an inlined record argument.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::CannotApplyModule { loc, mty, origin }) => {
            UserDiagnostic::new(
                format_cannot_apply_module_report(type_ctx, arena, source, filename, *loc, mty, origin.as_ref()),
                2,
            )
            .into()
        }
        TypeModError::NotAPackedModule { loc, ty } => {
            // typemod.ml:1932-1934.
            let ty = format_type_expr(type_ctx, *ty);
            UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &type_clash::render_error_message(|ppf| {
                    ppf.str("This expression is not a packed module. It has type");
                    ppf.space();
                    crate::types::printtyp::pp_doc(ppf, &ty);
                }),
            ),
            2,
        )
        .into()
        }
        TypeModError::CannotApply { loc, mty, origin } => UserDiagnostic::new(
            format_cannot_apply_module_report(type_ctx, arena, source, filename, *loc, mty, origin.as_ref()),
            2,
        )
        .into(),
        TypeModError::MissingModule {
            loc,
            path,
            expanded,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format_missing_module_message(path, expanded),
            ),
            2,
        )
        .into(),
        TypeModError::CannotScrapeAlias { loc, path } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("This is an alias for module {}, which is missing", path.name()),
            ),
            2,
        )
        .into(),
        TypeModError::IllegalValueName { loc, name } => UserDiagnostic::new(
            format_compiler_error_report_from_external_location(
                type_ctx,
                filename,
                loc,
                &format!("'{name}' is not a valid value identifier."),
            ),
            2,
        )
        .into(),
        TypeModError::CannotEliminateDependency { loc, mty } => UserDiagnostic::new(
            format_cannot_eliminate_dependency_report(
                type_ctx, arena, source, filename, *loc, mty,
            ),
            2,
        )
        .into(),
        TypeModError::RecursiveModuleRequiresExplicitType { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Recursive modules require an explicit module type.",
            ),
            2,
        )
        .into(),
        TypeModError::ApplyGenerative { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This is a generative functor. It can only be applied to ()",
            ),
            2,
        )
        .into(),
        TypeModError::NotAllowedInFunctorBody { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This expression creates fresh types.\nIt is not allowed inside applicative functors.",
            ),
            2,
        )
        .into(),
        TypeModError::IncompletePackedModule { loc, ty } => {
            // typemod.ml:1935-1938.
            let ty = format_package_type_expr_for_error(type_ctx, arena, *ty);
            UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &type_clash::render_error_message(|ppf| {
                    ppf.str("The type of this first-class module still contains type variables:");
                    ppf.space();
                    crate::types::printtyp::pp_doc(ppf, &ty);
                }),
            ),
            2,
        )
        .into()
        }
        TypeModError::ScopingPack { loc, lid, ty } => {
            // typemod.ml:1939-1941.
            let lid = format_longident_for_report(arena, lid);
            let ty = format_type_expr(type_ctx, *ty);
            UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &type_clash::render_error_message(|ppf| {
                    ppf.str(&format!("The type {lid} in this module cannot be exported."));
                    ppf.space();
                    ppf.str("Its type contains local dependencies:");
                    ppf.space();
                    crate::types::printtyp::pp_doc(ppf, &ty);
                }),
            ),
            2,
        )
        .into()
        }
        TypeModError::StructureExpected { loc, mty } => UserDiagnostic::new(
            format_structure_expected_report(type_ctx, arena, source, filename, *loc, mty),
            2,
        )
        .into(),
        TypeModError::WithNoComponent { loc, lid } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "The signature constrained by `with' has no component named {}",
                    format_longident_for_report(arena, lid)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::WithMismatch { loc, lid, error } => UserDiagnostic::new(
            format_with_mismatch_report(type_ctx, arena, source, filename, *loc, lid, error),
            2,
        )
        .into(),
        TypeModError::WithChangesModuleAlias { loc, lid, id, path } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "This `with' constraint on {} changes {}, which is aliased \nin the constrained signature (as {}).",
                    format_longident_for_report(arena, lid),
                    path.name(),
                    id.name()
                ),
            ),
            2,
        )
        .into(),
        TypeModError::WithMakesApplicativeFunctorIllTyped {
            loc,
            lid,
            path,
            error,
        } => UserDiagnostic::new(
            format_with_makes_applicative_functor_ill_typed_report(
                type_ctx,
                ReportSite::new(arena, source, filename, *loc),
                lid,
                path,
                error,
            ),
            2,
        )
        .into(),
        TypeModError::WithCannotRemoveConstrainedType { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Destructive substitutions are not supported for constrained \ntypes (other than when replacing a type constructor with \na type constructor with the same arguments).",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::LiteralOverflow { loc, ty }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "Integer literal exceeds the range of representable integers of type {ty}"
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::PolyvarLiteralOverflow { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Integer literal exceeds int32 range. Use float or BigInt if larger values are required.",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::InvalidStringEscapeAt { loc }) => {
            invalid_string_escape_report(type_ctx, filename, loc)
        }
        TypeModError::CoreError(TypeCoreError::InvalidStringEscapeSequence { loc }) => UserDiagnostic::new(
            format_compiler_error_report(arena, source, filename, *loc, "Invalid string escape sequence"),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::FixedArgumentOutsideExternal { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Fixed arguments are only allowed in external declarations",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UnknownLiteral {
            loc,
            literal,
            modifier,
        }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!("Unknown modifier '{modifier}' for literal {literal}{modifier}"),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ExprTypeClash {
            loc,
            trace,
            context,
            env,
        }) => {
            let report = with_typed_env_or_empty(type_ctx, *env, |env| {
                format_expr_type_clash_report_ocaml(
                    type_ctx, arena, source, filename, *loc, trace, context, env,
                )
            });
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::PatternTypeClash {
            loc: Some(loc),
            trace,
            env,
        }) => {
            let message = with_typed_env_or_empty(type_ctx, *env, |env| {
                type_clash::render_error_message(|ppf| {
                    type_clash::print_pattern_type_clash(ppf, type_ctx, env, trace)
                })
            });
            let report =
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message);
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::PolymorphicLabel { loc, lid }) => {
            UserDiagnostic::new(
                format_polymorphic_label_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::LabelMismatch {
            loc,
            lid,
            trace,
            env,
        }) => {
            let lid = format_longident_for_report(arena, lid);
            let message = with_typed_env_or_empty(type_ctx, *env, |env| {
                type_clash::render_error_message(|ppf| {
                    type_clash::print_label_mismatch(ppf, type_ctx, env, &lid, trace)
                })
            });
            let report =
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message);
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::NotSubtype {
            loc,
            trace,
            trace2,
            context,
            env,
        }) => {
            let message = with_typed_env_or_empty(type_ctx, *env, |env| {
                type_clash::render_error_message(|ppf| {
                    type_clash::print_not_subtype(ppf, type_ctx, env, trace, trace2, context.as_ref())
                })
            });
            let report =
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message);
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::LessGeneral {
            loc,
            kind,
            trace,
            env,
        }) => {
            let message = with_typed_env_or_empty(type_ctx, *env, |env| {
                type_clash::render_error_message(|ppf| {
                    type_clash::print_less_general(ppf, type_ctx, env, kind, trace)
                })
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnqualifiedGadtPattern { loc, tpath, name }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "The GADT constructor {} of type {}\nmust be written with its module prefix in this pattern.",
                        name,
                        format_type_path_for_report(tpath)
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnexpectedExistential { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This pattern introduces an existential type from a GADT constructor, which is not allowed here. Match on it inside a switch instead.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NotAVariantType { loc, lid }) => {
            UserDiagnostic::new(
                format_not_a_variant_type_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::TypeParamsNotSupported { loc, lid }) => {
            UserDiagnostic::new(
                format_type_params_not_supported_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ApplyNonFunction { loc, typ }) => {
            UserDiagnostic::new(
                format_apply_non_function_report(type_ctx, arena, source, filename, *loc, *typ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::MisplacedLabelSyntax { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Label syntax is not supported in this position",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::JsxUnboxedProps { loc, typ }) => {
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_jsx_unboxed_props(ppf, type_ctx, *typ)
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::TaggedTemplateNonTag { loc, typ }) => {
            UserDiagnostic::new(
                format_tagged_template_non_tag_report(
                    type_ctx, arena, source, filename, *loc, *typ,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::AbstractWrongLabel { loc, label, ty }) => {
            UserDiagnostic::new(
                format_abstract_wrong_label_report(
                    type_ctx, source, filename, loc, label, *ty,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ApplyWrongLabel { loc, label, ty }) => {
            UserDiagnostic::new(
                format_apply_wrong_label_report(
                    type_ctx,
                    arena,
                    source,
                    filename,
                    *loc,
                    label,
                    *ty,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IncoherentLabelOrder { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report_with_unindented_break(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This labeled function is applied to arguments",
                    "in an order different from other calls.\nThis is only allowed when the real type is known.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::WrongName {
            loc,
            kind,
            ty,
            expected,
            path,
            name,
            alternatives,
            jsx_component_info,
            env,
        }) => UserDiagnostic::new(
            format_wrong_name_report(
                type_ctx,
                env.and_then(|env| type_ctx.get_typed_env(env)),
                ReportSite::new(arena, source, filename, *loc),
                WrongName {
                    kind,
                    ty: *ty,
                    expected,
                    path,
                    name,
                },
                alternatives,
                jsx_component_info.as_deref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::NameTypeMismatch {
            loc,
            kind,
            lid,
            expected,
            alternatives,
        }) => UserDiagnostic::new(
            format_name_type_mismatch_report(
                type_ctx,
                ReportSite::new(arena, source, filename, *loc),
                kind,
                lid,
                expected,
                alternatives,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UndefinedMethod {
            loc: Some(loc),
            ty,
            method,
            alternatives,
        }) => UserDiagnostic::new(
            format_undefined_method_report(
                type_ctx,
                ReportSite::new(arena, source, filename, *loc),
                *ty,
                method,
                alternatives.as_deref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ObjectFieldNotMutable { loc, ty, name }) => {
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_object_field_not_mutable(ppf, type_ctx, *ty, name)
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundValue {
            loc,
            name,
            qualifier,
            alternatives,
            module_suggestion,
        }) => {
            let report = format_unbound_value_report(
                ReportSite::new(arena, source, filename, *loc),
                name,
                qualifier.as_deref(),
                alternatives,
                module_suggestion.as_deref(),
            );
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundModule {
            loc,
            name,
            alternatives,
        }) => UserDiagnostic::new(
            format_unbound_module_report(arena, source, filename, *loc, name, alternatives),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UnboundModtype {
            loc,
            lid,
            alternatives,
        }) => UserDiagnostic::new(
            format_unbound_modtype_report(arena, source, filename, *loc, lid, alternatives),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::AccessFunctorAsStructure { loc, lid }) => {
            UserDiagnostic::new(
                format_access_functor_as_structure_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::CannotScrapeAlias { loc, lid, path }) => {
            UserDiagnostic::new(
                format_cannot_scrape_alias_report(arena, source, filename, *loc, lid, path),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IllegalReferenceToRecursiveModule { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Illegal recursive module reference",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundConstructor {
            loc,
            lid,
            alternatives,
        }) => {
            UserDiagnostic::new(
                format_unbound_constructor_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    lid,
                    alternatives,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundTypeConstructor {
            loc,
            lid,
            alternatives,
        }) => {
            UserDiagnostic::new(
                format_unbound_type_constructor_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    lid,
                    alternatives,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundTypeConstructorIncomplete {
            loc,
            path,
        }) => UserDiagnostic::new(
            format_unbound_type_constructor_incomplete_report(
                arena, source, filename, *loc, path,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UnboundTypeVariable { loc, name }) => {
            UserDiagnostic::new(
                format_unbound_type_variable_report(arena, source, filename, *loc, name),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidVariableName { loc, name }) => {
            UserDiagnostic::new(
                format_invalid_variable_name_report(arena, source, filename, *loc, name),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::CannotQuantify { loc, name, ty }) => {
            UserDiagnostic::new(
                format_cannot_quantify_report(
                    type_ctx, arena, source, filename, *loc, name, *ty,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::MultipleConstraintsOnType { loc, lid }) => {
            UserDiagnostic::new(
                format_multiple_constraints_on_type_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::SignatureExpected { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This module type is not a signature",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::PresentHasConjunction { loc, label }) => {
            UserDiagnostic::new(
                format_present_has_conjunction_report(arena, source, filename, *loc, label),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::PresentHasNoType { loc, label }) => {
            UserDiagnostic::new(
                format_present_has_no_type_report(arena, source, filename, *loc, label),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ConstructorMismatch {
            loc,
            actual,
            expected,
        }) => UserDiagnostic::new(
            format_constructor_mismatch_report(
                type_ctx, arena, source, filename, *loc, *actual, *expected,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::NotAVariant { loc, ty }) => UserDiagnostic::new(
            format_not_a_variant_report(type_ctx, arena, source, filename, *loc, *ty),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::MethodMismatch {
            loc,
            label,
            actual,
            expected,
        }) => UserDiagnostic::new(
            format_method_mismatch_report(
                type_ctx,
                ReportSite::new(arena, source, filename, *loc),
                label,
                *actual,
                *expected,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::TypeMismatch { loc, trace }) => {
            UserDiagnostic::new(
                format_type_mismatch_report(type_ctx, arena, source, filename, *loc, trace),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::AliasTypeMismatch { loc, trace }) => {
            UserDiagnostic::new(
                format_alias_type_mismatch_report(
                    type_ctx, arena, source, filename, *loc, trace,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::TypeArityMismatch {
            loc,
            lid,
            expected,
            provided,
        }) => UserDiagnostic::new(
            format_type_arity_mismatch_report(
                arena, source, filename, *loc, lid, *expected, *provided,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::LabelMultiplyDefined {
            loc,
            label,
            jsx_component_info,
        }) => UserDiagnostic::new(
            format_label_multiply_defined_report(
                arena,
                source,
                filename,
                *loc,
                label,
                jsx_component_info.as_ref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::LabelsMissing {
            loc,
            labels,
            jsx_component_info,
        }) => UserDiagnostic::new(
            format_labels_missing_report(
                arena,
                source,
                filename,
                *loc,
                labels,
                jsx_component_info.as_ref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::RecordRest { loc, error }) => {
            UserDiagnostic::new(
                format_compiler_error_report_with_unindented_continuation(
                    arena,
                    source,
                    filename,
                    *loc,
                    &error.message(arena),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::PrivateType { loc, ty }) => {
            // typecore.ml:5425-5426.
            let ty = format_type_expr(type_ctx, *ty);
            UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &type_clash::render_error_message(|ppf| {
                    ppf.str("Cannot create values of the private type ");
                    crate::types::printtyp::pp_doc(ppf, &ty);
                }),
            ),
            2,
        )
        .into()
        }
        TypeModError::CoreError(TypeCoreError::LabelNotMutable { loc, lid }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "The record field {} is not mutable",
                        format_longident_for_report(arena, lid)
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundRecordField {
            loc,
            field_name,
            from_type,
            alternatives,
        }) => UserDiagnostic::new(
            format_unbound_record_field_report(
                type_ctx,
                ReportSite::new(arena, source, filename, *loc),
                field_name,
                *from_type,
                alternatives,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::FieldNotOptional { loc, name, typ }) => {
            UserDiagnostic::new(
                format_field_not_optional_report(
                    type_ctx, arena, source, filename, *loc, name, *typ,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::RecordSyntaxOnDictType { loc, key }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "Record syntax can't be used on a dict. Use dict{{...}} instead, e.g. dict{{\"{key}\": ...}}."
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::DictKeyMultiplyDefined { loc, key }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!("The key \"{key}\" is matched several times in this dict pattern"),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::FieldAccessOnDictType { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Direct field access on a dict is not supported. Use Dict.get instead.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NotAnObjectType { loc, ty }) => {
            // typetexp.ml:1014-1016: `@[The type %a@ is not an object type@]`.
            let ty = format_type_expr(type_ctx, *ty);
            UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &type_clash::render_error_message(|ppf| {
                    ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
                    ppf.str("The type ");
                    crate::types::printtyp::pp_doc(ppf, &ty);
                    ppf.space();
                    ppf.str("is not an object type");
                    ppf.close_box();
                }),
            ),
            2,
        )
        .into()
        }
        TypeModError::CoreError(TypeCoreError::OpenedObject { loc, path }) => {
            let report = match path {
                Some(path) => format_compiler_error_report_with_unindented_break(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Illegal open object type",
                    &path.name(),
                ),
                None => format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Illegal open object type",
                ),
            };
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::SignatureMismatch { loc, error } => UserDiagnostic::new(
            format_compiler_error_report_raw_message(
                arena,
                source,
                filename,
                *loc,
                &crate::types::includemod::format_error(type_ctx, filename, error),
            ),
            2,
        )
        .into(),
        TypeModError::UnboundModtype {
            loc,
            lid,
            alternatives,
        } => UserDiagnostic::new(
            format_unbound_modtype_report(arena, source, filename, *loc, lid, alternatives),
            2,
        )
        .into(),
        TypeModError::TypeDeclTypeClash { loc, trace } => {
            // typedecl.ml:2176-2180.
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_report_unification_error(
                    ppf,
                    type_ctx,
                    trace,
                    "This type constructor expands to type",
                    "but is used here with type",
                )
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::InconsistentConstraint { loc, trace } => UserDiagnostic::new(
            format_inconsistent_constraint_report(type_ctx, arena, source, filename, *loc, trace),
            2,
        )
        .into(),
        TypeModError::NullArityExternal { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "External identifiers must be functions",
            ),
            2,
        )
        .into(),
        TypeModError::FatalError { message } => UserDiagnostic::new(message.clone(), 2).into(),
        TypeModError::ConstraintFailed {
            loc,
            actual,
            expected,
        } => UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &format_two_type_message(type_ctx, *actual, *expected, |ppf, actual, expected| {
                    // typedecl.ml:2216-2221:
                    // `@[%s@ @[<hv>Type@ %a@ should be an instance of@ %a@]@]`.
                    use crate::parser::formatter::BoxKind;
                    ppf.open_box(BoxKind::Box, 0);
                    ppf.str("Constraints are not satisfied in this type.");
                    ppf.space();
                    ppf.open_box(BoxKind::HV, 0);
                    ppf.str("Type");
                    ppf.space();
                    crate::types::printtyp::pp_doc(ppf, actual);
                    ppf.space();
                    ppf.str("should be an instance of");
                    ppf.space();
                    crate::types::printtyp::pp_doc(ppf, expected);
                    ppf.close_box();
                    ppf.close_box();
                }),
            ),
            2,
        )
        .into(),
        TypeModError::DefinitionMismatch { loc, ty, errs } => UserDiagnostic::new(
            format_definition_mismatch_report(
                type_ctx, arena, source, filename, *loc, *ty, errs,
            ),
            2,
        )
        .into(),
        // typedecl.ml `Unavailable_type_constructor p`: `"The definition of
        // type %a@ is unavailable"`.
        TypeModError::UnavailableTypeConstructor { loc, path } => UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &type_clash::render_error_message(|ppf| {
                    ppf.str(&format!("The definition of type {}", path.name()));
                    ppf.space();
                    ppf.str("is unavailable");
                }),
            ),
            2,
        )
        .into(),
        TypeModError::BadFixedType { loc, reason } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("This fixed type {reason}"),
            ),
            2,
        )
        .into(),
        TypeModError::BadVariance {
            loc,
            param_index,
            actual,
            expected,
        } => UserDiagnostic::new(
            format_bad_variance_report(
                arena,
                source,
                filename,
                *loc,
                *param_index,
                *actual,
                *expected,
            ),
            2,
        )
        .into(),
        TypeModError::VaryingAnonymous { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "In this GADT definition, the variance of some parameter cannot be checked",
            ),
            2,
        )
        .into(),
        TypeModError::JsNameClash {
            loc,
            kind,
            other_kind,
            js_name,
            other_loc,
        } => UserDiagnostic::new(
            format_compiler_error_report_from_location(
                source,
                filename,
                loc,
                &render_js_name_clash_message(
                    kind,
                    other_kind,
                    js_name,
                    &code_frame::format_location(
                        &crate::types::includemod::location_filename(
                            type_ctx, filename, other_loc,
                        ),
                        &other_loc.loc_start,
                        &other_loc.loc_end,
                    ),
                ),
            ),
            2,
        )
        .into(),
        TypeModError::InvalidUntaggedVariantDefinition { loc, reason } => UserDiagnostic::new(
            format_compiler_error_report_from_location(
                source,
                filename,
                loc,
                &format!("This untagged variant definition is invalid: {reason}"),
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadCouldNotFindType { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This type could not be found. It's only possible to spread variants that are known as the spread happens. This means for example that you can't spread variants in recursive definitions.",
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadInvalidType { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This type is not a valid type to spread. It's only possible to spread other variants.",
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadHasTypeParams { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Type parameters are not supported in variant type spreads.",
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadDuplicateConstructor {
            loc,
            variant_name,
            constructor_name,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "Variant {variant_name} has a constructor named {constructor_name}, but a constructor named {constructor_name} already exists in the variant it's spread into.\nYou cannot spread variants with overlapping constructors.",
                ),
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadUnboxedMismatch {
            loc,
            source_unboxed,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "This variant is {}, but the variant where this is spread is not. Both variants unboxed configuration must match.",
                    if *source_unboxed {
                        "unboxed"
                    } else {
                        "not unboxed"
                    },
                ),
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadTagMismatch { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "The @tag attribute does not match for this variant and the variant where this is spread. Both variants must have the same @tag attribute configuration, or no @tag attribute at all.",
            ),
            2,
        )
        .into(),
        TypeModError::RepeatedParameter { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "A type parameter occurs several times",
            ),
            2,
        )
        .into(),
        TypeModError::DuplicateConstructor { loc, name } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("Two constructors are named {name}"),
            ),
            2,
        )
        .into(),
        TypeModError::DuplicateLabel {
            loc,
            label,
            record_name,
        } => UserDiagnostic::new(
            format_duplicate_type_label_report(arena, source, filename, *loc, label, record_name),
            2,
        )
        .into(),
        TypeModError::RepeatedName {
            loc,
            kind,
            name,
            repeated_loc,
        } => UserDiagnostic::new(
            format_repeated_name_report(
                arena,
                source,
                filename,
                *loc,
                kind,
                name,
                *repeated_loc,
            ),
            2,
        )
        .into(),
        TypeModError::ObjectSpreadWithRecordField { loc, field_name } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "You cannot mix a record field with an object type spread.\nRemove the record field or change it to an object field (e.g. \"{field_name}\": ...)."
                ),
            ),
            2,
        )
        .into(),
        TypeModError::RecursiveAbbrev { loc, name } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("The type abbreviation {name} is cyclic"),
            ),
            2,
        )
        .into(),
        TypeModError::CycleInDef { loc, name, ty } => UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &{
                    // typedecl.ml:2205-2208:
                    // `@[<v>The definition of %s contains a cycle:@ %a@]`.
                    let ty = format_type_expr(type_ctx, *ty);
                    type_clash::render_error_message(|ppf| {
                        ppf.open_vbox(0);
                        ppf.str(&format!("The definition of {name} contains a cycle:"));
                        ppf.space();
                        crate::types::printtyp::pp_doc(ppf, &ty);
                        ppf.close_box();
                    })
                },
            ),
            2,
        )
        .into(),
        TypeModError::ParametersDiffer {
            loc,
            path,
            actual,
            expected,
        } => UserDiagnostic::new(
            format_compiler_error_report_formatted(
                arena,
                source,
                filename,
                *loc,
                &format_two_type_message(type_ctx, *actual, *expected, |ppf, actual, expected| {
                    // typedecl.ml:2222-2226:
                    // `@[<hv>In the definition of %s, type@ %a@ should be@ %a@]`.
                    ppf.open_hvbox(0);
                    ppf.str(&format!("In the definition of {}, type", path.name()));
                    ppf.space();
                    crate::types::printtyp::pp_doc(ppf, actual);
                    ppf.space();
                    ppf.str("should be");
                    ppf.space();
                    crate::types::printtyp::pp_doc(ppf, expected);
                    ppf.close_box();
                }),
            ),
            2,
        )
        .into(),
        TypeModError::InvalidAttribute { loc, message } => UserDiagnostic::new(
            format_compiler_error_report(arena, source, filename, *loc, message),
            2,
        )
        .into(),
        TypeModError::BadUnboxedAttribute { loc, message } => {
            let report = if message == "extensible variant types cannot be unboxed" {
                "This type cannot be unboxed because\nextensible variant types cannot be unboxed."
                    .to_string()
            } else {
                format!("This type cannot be unboxed because {message}.")
            };
            UserDiagnostic::new(
                format_compiler_error_report(arena, source, filename, *loc, &report),
                2,
            )
            .into()
        }
        TypeModError::BadImmediateAttribute { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Types marked with the immediate attribute must be\nnon-pointer types like int or bool",
            ),
            2,
        )
        .into(),
        TypeModError::CannotExtendPrivateType { loc, path } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("Cannot extend private type definition {}", path.name()),
            ),
            2,
        )
        .into(),
        TypeModError::NotExtensibleType { loc, path } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("Type definition {} is not extensible", path.name()),
            ),
            2,
        )
        .into(),
        TypeModError::ExtensionMismatch {
            loc,
            path,
            mismatch,
        } => {
            let mismatch_message = match mismatch {
                TypeExtensionMismatch::Arity => "They have different arities.",
                TypeExtensionMismatch::Variance => "Their variances do not agree.",
            };
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "This extension does not match the definition of type {}\n{}",
                        path.name(),
                        mismatch_message
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::RebindWrongType {
            loc,
            lid,
            trace,
            env,
        } => {
            let lid = format_longident_for_report(arena, lid);
            let message = with_typed_env_or_empty(type_ctx, Some(*env), |env| {
                type_clash::render_error_message(|ppf| {
                    type_clash::print_rebind_wrong_type(ppf, type_ctx, env, &lid, trace)
                })
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::RebindPrivate { loc, lid } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "The constructor {} is private",
                    format_longident_for_report(arena, lid)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::UnboundTypeVar {
            loc,
            name,
            detail: None,
            var: None,
        } => UserDiagnostic::new(
            format_unbound_type_variable_report(arena, source, filename, *loc, name),
            2,
        )
        .into(),
        TypeModError::UnboundTypeVar {
            loc,
            name,
            detail,
            var,
        } => UserDiagnostic::new(
            format_unbound_type_declaration_variable_report(
                type_ctx,
                ReportSite::new(arena, source, filename, *loc),
                name,
                detail.as_ref(),
                *var,
            ),
            2,
        )
        .into(),
        TypeModError::UnboundTypeVarInExtension { loc, var, args } => {
            // typedecl.ml:2202-2205: `tys_of_constr_args ext.ext_args`, then
            // `explain_unbound` over the first argument containing `var`.
            let tys: Vec<TypeExprRef> = match args {
                crate::types::ConstructorArguments::CstrTuple(tys) => tys.clone(),
                crate::types::ConstructorArguments::CstrRecord(labels) => {
                    labels.iter().map(|l| l.ld_type).collect()
                }
            };
            let first = "A type variable is unbound in this extension constructor";
            let report = match tys
                .iter()
                .find(|ti| crate::types::ctype::deep_occur(type_ctx, *var, **ti))
            {
                Some(ti) => {
                    let explanation = type_clash::render_error_message_at_column0(|ppf| {
                        type_clash::print_explain_unbound_type(ppf, type_ctx, *var, *ti)
                    });
                    format_compiler_error_report_with_unindented_break(
                        arena,
                        source,
                        filename,
                        *loc,
                        &format!("{first}."),
                        explanation.trim_end_matches('\n'),
                    )
                }
                None => format_compiler_error_report(arena, source, filename, *loc, first),
            };
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::UnboundTypeVarExt { loc, name } => UserDiagnostic::new(
            format_unbound_type_variable_report(arena, source, filename, *loc, name),
            2,
        )
        .into(),
        TypeModError::InvalidStringEscape { loc } => {
            invalid_string_escape_report(type_ctx, filename, loc)
        }
        TypeModError::AstUntaggedVariantError { loc, error } => {
            let message = error.message_text();
            UserDiagnostic::new(
                format_compiler_error_report_from_location(source, filename, loc, &message),
                2,
            )
            .into()
        }
        TypeModError::NonrecursiveGadt { loc } => {
            // typedecl.ml:2334-2337: "@[GADTs require recursive type
            // syntax.@ Define your type using `type rec` instead of
            // `type`.@]".
            let message = type_clash::render_error_message(|ppf| {
                ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
                ppf.str("GADTs require recursive type syntax.");
                ppf.space();
                ppf.str("Define your type using `type rec` instead of `type`.");
                ppf.close_box();
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::NonGeneralizable { loc, typ } => UserDiagnostic::new(
            format_non_generalizable_report(source, filename, loc, type_ctx, *typ),
            2,
        )
        .into(),
        TypeModError::NonGeneralizableModule { loc, mty } => UserDiagnostic::new(
            format_non_generalizable_module_report(source, filename, loc, type_ctx, mty),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::InlinedRecordEscape { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This use of an inlined record is not allowed: its anonymous type would escape its constructor scope.\nPossible solutions: \n- Destructure the fields you're interested in from the inline record\n- Change the underlying type to use a defined record as payload instead of an inline record. That will let you use the payload without destructuring it first",
                ),
                2,
            )
            .into()
        }
        _ => anyhow!("Type checking failed: {err:?}"),
    }
}

fn persistent_env_error_to_anyhow(error: PersistentEnvError, filename: &str) -> anyhow::Error {
    let message = match error {
        PersistentEnvError::InterfaceRead { message } => {
            let mut output = String::new();
            push_compiler_report_intro(&mut output, "We've found a bug for you!");
            push_compiler_report_location(&mut output, filename);
            output.push_str("  ");
            output.push_str(&message);
            output.push_str("\n\n");
            return UserDiagnostic::new(output, 2).into();
        }
        PersistentEnvError::IllegalRenaming {
            expected, actual, ..
        } => format!(
            "You referred to the module {expected}, but we've found one called {actual} instead.\nIs the name's casing right?"
        ),
        // OCaml reports the stored persistent-structure filenames directly
        // through `Location.print_filename` (compiler/ml/env.ml:2110-2119).
        PersistentEnvError::InconsistentImport {
            name,
            source1,
            source2,
        } => format!(
            "\x1b[1;33mIt's possible that your build is stale.\x1b[0m\nTry to clean the artifacts and build again?\n\n\x1b[1;33mHere's the original error message\x1b[0m\nThe files {source1}\nand {source2}\nmake inconsistent assumptions over interface {name}"
        ),
    };
    UserDiagnostic::new(format_compiler_error_report_for_file(filename, &message), 2).into()
}

fn module_path_resolution_error_to_anyhow(
    error: ModulePathResolutionError,
    filename: &str,
) -> anyhow::Error {
    let message = match error {
        ModulePathResolutionError::CmjNotFound { module_name } => format!(
            "{module_name} not found, it means either the module does not exist or it is a namespace"
        ),
        ModulePathResolutionError::JsNotFound { js_file } => {
            format!("{js_file} not found, needed in script mode ")
        }
        ModulePathResolutionError::MissingMlDependency { module_name } => {
            format!("Missing dependency {module_name} in search path")
        }
        ModulePathResolutionError::DependencyScriptModuleDependentNot { module_name } => {
            format!("{module_name} is compiled in script mode while its dependent is not")
        }
    };
    UserDiagnostic::new(format_compiler_error_report_for_file(filename, &message), 2).into()
}

fn check_module_path_resolution_errors(
    program: &DepsProgram,
    resolver: &ModulePathResolver,
    filename: &str,
) -> Result<()> {
    for module in &program.modules {
        if let Some(error) = resolver.module_path_resolution_error(module) {
            return Err(module_path_resolution_error_to_anyhow(error, filename));
        }
    }
    Ok(())
}

fn push_compiler_report_intro(output: &mut String, intro: &str) {
    // OCaml compiler/ml/location.ml:88-95 colors the diagnostic intro with
    // the `error`, `warning`, or `info` tag after bsc's color mode has been
    // installed by compiler/ml/location.ml:45-47.
    output.push_str("\n  ");
    output.push_str(&code_frame::colorize_intro(intro, true));
    output.push('\n');
}

fn push_compiler_report_location(output: &mut String, location: &str) {
    // OCaml compiler/ml/location.ml:65-85 prints filenames through the
    // `filename` tag and line/column ranges through the `dim` tag.
    output.push_str("  ");
    output.push_str(&code_frame::colorize_location(location));
    output.push_str("\n\n");
}

fn format_compiler_error_report_for_file(filename: &str, message: &str) -> String {
    let mut output = String::new();
    push_compiler_report_intro(&mut output, "We've found a bug for you!");
    push_compiler_report_location(&mut output, filename);
    let message = code_frame::apply_message_styles(message);
    push_indented_lines(&mut output, &message);
    output.push('\n');
    output
}

fn format_duplicate_type_label_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
    record_name: &Option<String>,
) -> String {
    let message = if let Some(record_name) = record_name {
        format!(
            "The field {INFO}{label}{RESET} is defined several times in the record {INFO}{record_name}{RESET}. Fields can only be added once to a record."
        )
    } else {
        format!(
            "The field {INFO}{label}{RESET} is defined several times in this record. Fields can only be added once to a record."
        )
    };
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_repeated_name_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    kind: &str,
    name: &str,
    repeated_loc: LocIdx,
) -> String {
    let repeated = code_frame::format_location(
        filename,
        arena.loc_start(repeated_loc),
        arena.loc_end(repeated_loc),
    );
    // OCaml compiler/ml/typemod.ml:1851-1855:
    // "@[Multiple definition of the %s name %s @ at @{<loc>%a@}@ @ Names must be
    //  unique in a given structure or signature.@]"
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.set_margin(76);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.print(format_args!(
            "Multiple definition of the {kind} name {name} "
        ));
        ppf.space();
        ppf.str("at ");
        if code_frame::should_enable_color() {
            // `@{<loc>...@}` around `Location.print_loc`, which prints
            // `@{<filename>%s@}:@{<dim>%s@}` (compiler/ml/location.ml:75-93);
            // semantic tag markers take no width (compiler/ext/misc.ml:327-350).
            let (file, range) = repeated.split_once(':').unwrap_or((repeated.as_str(), ""));
            ppf.string_as(0, "\x1b[1m");
            ppf.string_as(0, "\x1b[36m");
            ppf.str(file);
            ppf.string_as(0, "\x1b[0m");
            if !range.is_empty() {
                ppf.str(":");
                ppf.string_as(0, "\x1b[2m");
                ppf.str(range);
                ppf.string_as(0, "\x1b[0m");
            }
            ppf.string_as(0, "\x1b[0m");
        } else {
            ppf.str(&repeated);
        }
        ppf.space();
        ppf.space();
        ppf.str("Names must be unique in a given structure or signature.");
        ppf.close_box();
        ppf.flush();
    }
    let message = String::from_utf8(buf).unwrap_or_default();
    format_compiler_error_report(arena, source, filename, loc, &message)
}

/// typemod.ml `Js_name_clash`: "@[This %s has the same JavaScript name %s@ as
/// the %s at @{<loc>%a@}.@ Rename one of them.@]".
fn render_js_name_clash_message(
    kind: &str,
    other_kind: &str,
    js_name: &str,
    other_location: &str,
) -> String {
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.set_margin(76);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.print(format_args!(
            "This {kind} has the same JavaScript name {js_name}"
        ));
        ppf.space();
        ppf.print(format_args!("as the {other_kind} at "));
        if code_frame::should_enable_color() {
            // `@{<loc>...@}` around `Location.print_loc`, which prints
            // `@{<filename>%s@}:@{<dim>%s@}` (compiler/ml/location.ml:75-93);
            // semantic tag markers take no width (compiler/ext/misc.ml:327-350).
            let (file, range) = other_location
                .split_once(':')
                .unwrap_or((other_location, ""));
            ppf.string_as(0, "\x1b[1m");
            ppf.string_as(0, "\x1b[36m");
            ppf.str(file);
            ppf.string_as(0, "\x1b[0m");
            if !range.is_empty() {
                ppf.str(":");
                ppf.string_as(0, "\x1b[2m");
                ppf.str(range);
                ppf.string_as(0, "\x1b[0m");
            }
            ppf.string_as(0, "\x1b[0m");
        } else {
            ppf.str(other_location);
        }
        ppf.str(".");
        ppf.space();
        ppf.str("Rename one of them.");
        ppf.close_box();
        ppf.flush();
    }
    String::from_utf8(buf).unwrap_or_default()
}

/// `non_generalizable_msg` (typemod.ml:1805-1812) around the fallback
/// message of `Non_generalizable` / `Non_generalizable_module`
/// (typemod.ml:1856-1874), inside `@[<v>...@]`.
fn render_non_generalizable_message(intro: &str, rendered_type: &str) -> String {
    use crate::types::printtyp::{TAG_ERROR, TAG_INFO, TAG_RESET};
    type_clash::render_error_message(|ppf| {
        ppf.open_vbox(0);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str(intro);
        ppf.cut();
        ppf.string_as(0, TAG_ERROR);
        // `type_scheme` or `modtype` (typemod.ml:1906-1924).
        crate::types::printtyp::pp_doc(ppf, rendered_type);
        ppf.string_as(0, TAG_RESET);
        ppf.close_box();
        ppf.cut();
        ppf.cut();
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str("This happens when the type system senses there's a mutation/side-effect,");
        ppf.space();
        ppf.str("in combination with a polymorphic value.");
        ppf.cut();
        ppf.string_as(0, TAG_INFO);
        ppf.str("Using or annotating that value usually solves it.");
        ppf.string_as(0, TAG_RESET);
        ppf.close_box();
        ppf.close_box();
    })
}

fn format_compiler_error_report_formatted_from_location(
    source: &str,
    filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let mut output = String::new();
    push_compiler_error_report_header_from_location(&mut output, source, filename, loc);
    output.push_str(&code_frame::apply_message_styles(message));
    output.push_str("\n\n");
    output
}

fn format_non_generalizable_report(
    source: &str,
    filename: &str,
    loc: &Location,
    type_ctx: &TypeContext,
    typ: TypeExprRef,
) -> String {
    let rendered_type = format_non_generalizable_type_expr(type_ctx, typ);
    let message = render_non_generalizable_message(
        "This expression's type contains type variables that cannot be generalized:",
        &rendered_type,
    );
    format_compiler_error_report_formatted_from_location(source, filename, loc, &message)
}

fn format_non_generalizable_module_report(
    source: &str,
    filename: &str,
    loc: &Location,
    type_ctx: &TypeContext,
    mty: &crate::types::decl::ModuleType,
) -> String {
    let rendered_type = crate::types::includemod::format_module_type_show_weak(type_ctx, mty);
    let message = render_non_generalizable_message(
        "The type of this module contains type variables that cannot be generalized:",
        &rendered_type,
    );
    format_compiler_error_report_formatted_from_location(source, filename, loc, &message)
}

fn format_interface_not_compiled_report(
    source: &str,
    filename: &str,
    file_name_idx: StrIdx,
    interface_name: &str,
) -> String {
    let loc = Location::in_file(file_name_idx);
    let message = format!("Could not compile the interface\n{interface_name}.");
    format_compiler_error_report_from_location(source, filename, &loc, &message)
}

fn interface_source_name(source_file: &str) -> String {
    let mut intf = std::path::PathBuf::from(source_file);
    intf.set_extension("resi");
    intf.to_string_lossy().into_owned()
}

/// GenTypeMain.ml:93-107's walk (Annotation.ml:179-227) over a parsed
/// signature: whether `@genType.ignoreInterface` is seen before the first
/// annotated item.
fn parsed_signature_read_input(
    arena: &ParseArena,
    signature: &[crate::parser::ast::SignatureItem],
    ignore_interface: &std::cell::Cell<bool>,
) -> crate::gentype::annotation::Read<bool> {
    let check = |attributes: &Attributes| {
        crate::gentype::main::read_input_check_annotation(ignore_interface, arena, attributes)
    };
    fn module_type(
        arena: &ParseArena,
        idx: crate::parse_arena::ModTypeIdx,
        ignore_interface: &std::cell::Cell<bool>,
    ) -> crate::gentype::annotation::Read<bool> {
        match &arena.get_mod_type(idx).pmty_desc {
            crate::parser::ast::ModuleTypeDesc::Pmty_signature(signature) => {
                parsed_signature_read_input(arena, signature, ignore_interface)
            }
            _ => Ok(false),
        }
    }
    for item in signature {
        let annotated = match &item.psig_desc {
            SignatureItemDesc::Psig_type(declarations) => {
                let mut annotated = false;
                for declaration in &declarations.1 {
                    if check(&declaration.ptype_attributes)? {
                        annotated = true;
                        break;
                    }
                }
                annotated
            }
            SignatureItemDesc::Psig_value(value) => check(&value.pval_attributes)?,
            SignatureItemDesc::Psig_module(declaration) => {
                check(&declaration.pmd_attributes)?
                    || module_type(arena, declaration.pmd_type, ignore_interface)?
            }
            SignatureItemDesc::Psig_attribute(attribute) => {
                check(&Attributes::from_vec(vec![attribute.as_ref().clone()]))?
            }
            SignatureItemDesc::Psig_modtype(declaration) => {
                check(&declaration.pmtd_attributes)?
                    || match declaration.pmtd_type {
                        None => false,
                        Some(idx) => module_type(arena, idx, ignore_interface)?,
                    }
            }
            _ => false,
        };
        if annotated {
            return Ok(true);
        }
    }
    Ok(false)
}

/// What GenType reads in a module's interface (GenTypeMain.ml:91-107) for a
/// compile that has only its source: OCaml reads the `.cmti`, which this
/// compile path does not have typed, so the parsed `.resi` stands in for
/// the walk and the interface's output is not this compile's.
fn interface_source_gentype_read(source_file: &str) -> crate::gentype::main::InterfaceRead {
    // The walk renders no notes.
    let not_selected = crate::gentype::main::InterfaceRead::Read {
        ignore_interface: false,
        needs_locations: false,
        output: None,
    };
    let intf_name = interface_source_name(source_file);
    let Ok(bytes) = std::fs::read(&intf_name) else {
        return not_selected;
    };
    let source = crate::source_text::latin1_bytes_to_string(bytes);
    let mut parser = Parser::new(&intf_name, &source);
    let signature = module::parse_signature(&mut parser);
    if parser.has_errors() {
        return not_selected;
    }
    let ignore_interface = std::cell::Cell::new(false);
    match parsed_signature_read_input(parser.arena(), &signature, &ignore_interface) {
        Ok(_) => crate::gentype::main::InterfaceRead::Read {
            ignore_interface: ignore_interface.get(),
            needs_locations: false,
            output: None,
        },
        Err(crate::gentype::annotation::InvalidEscape::Parsed(loc)) => {
            crate::gentype::main::InterfaceRead::Raised(format_compiler_error_report(
                parser.arena(),
                &source,
                &intf_name,
                loc,
                "Invalid string escape sequence",
            ))
        }
        Err(crate::gentype::annotation::InvalidEscape::Decl(_)) => {
            unreachable!("a parsed signature's payloads have parse locations")
        }
    }
}

fn source_has_interface(options: &CompilerOptions, source_file: &str) -> bool {
    options.assume_compiled_interface || std::path::Path::new(&format!("{source_file}i")).exists()
}

fn compiled_interface_file_exists(options: &CompilerOptions, source_file: &str) -> bool {
    let module_name = module_name_from_source_filename(source_file);
    let filename = format!("{module_name}.cmi");
    let uncapitalized = filename
        .chars()
        .next()
        .map(|ch| ch.to_lowercase().collect::<String>() + &filename[ch.len_utf8()..])
        .unwrap_or_else(|| filename.clone());

    build_load_path(options)
        .iter()
        .any(|dir| dir.join(&uncapitalized).exists() || dir.join(&filename).exists())
}

fn push_compiler_error_report_header_from_location(
    output: &mut String,
    source: &str,
    filename: &str,
    loc: &Location,
) {
    push_compiler_error_report_header_from_external_location(output, Some(source), filename, loc);
}

fn push_compiler_error_report_header(
    output: &mut String,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
) {
    push_compiler_report_intro(output, "We've found a bug for you!");
    let start_pos = arena.loc_start(loc);
    let end_pos = arena.loc_end(loc);
    if !code_frame::has_printable_range(start_pos, end_pos) {
        // `Location.show_filename` (location.ml:38): the location's own file
        // name unless it is the `_none_` placeholder.
        let pos_fname = arena.get_string(start_pos.file_name);
        let shown = if pos_fname.is_empty() || pos_fname == "_none_" {
            filename
        } else {
            pos_fname
        };
        push_compiler_report_location(output, shown);
    } else {
        let location = code_frame::format_location(filename, start_pos, end_pos);
        push_compiler_report_location(output, &location);
        output.push_str(&code_frame::print(source, start_pos, end_pos));
        output.push('\n');
    }
}

fn format_compiler_error_report_from_location(
    source: &str,
    filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header_from_location(&mut output, source, filename, loc);

    let message = code_frame::apply_message_styles(message);
    push_indented_lines(&mut output, &message);
    output.push('\n');
    output
}

fn push_compiler_error_report_header_from_external_location(
    output: &mut String,
    source: Option<&str>,
    filename: &str,
    loc: &Location,
) {
    push_compiler_report_intro(output, "We've found a bug for you!");
    if !code_frame::has_printable_range(&loc.loc_start, &loc.loc_end) {
        push_compiler_report_location(output, filename);
    } else {
        let location = code_frame::format_location(filename, &loc.loc_start, &loc.loc_end);
        push_compiler_report_location(output, &location);
        if let Some(source) = source {
            output.push_str(&code_frame::print(source, &loc.loc_start, &loc.loc_end));
            output.push('\n');
        }
    }
}

fn format_compiler_error_report_from_external_location(
    type_ctx: &TypeContext,
    current_filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let loc_filename = type_ctx
        .resolve_cmi_longident_component(loc.loc_start.file_name)
        .filter(|name| !name.is_empty() && name != "_none_")
        .unwrap_or_else(|| current_filename.to_string());
    let loc_source = std::fs::read_to_string(&loc_filename).ok();
    let mut output = String::new();

    push_compiler_error_report_header_from_external_location(
        &mut output,
        loc_source.as_deref(),
        &loc_filename,
        loc,
    );

    push_indented_lines(&mut output, message);
    output.push('\n');
    output
}

fn format_compiler_error_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);

    let message = code_frame::apply_message_styles(message);
    push_indented_lines(&mut output, &message);
    output.push('\n');
    output
}

/// The error OCaml raises when writing a binary AST reaches an `[%error]`
/// extension: `Location.Error (Builtin_attributes.error_of_extension ext)`
/// from `Depend.handle_extension` (depend.ml:92-96).
pub fn error_extension_to_anyhow(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    extension: &crate::parser::ast::Extension,
) -> anyhow::Error {
    match crate::types::typecore::builtin_extension_error(arena, extension) {
        TypeCoreError::ExtensionError(error) => UserDiagnostic::new(
            format_builtin_extension_error_report(arena, source, filename, &error),
            2,
        )
        .into(),
        // OCaml's `Location.Already_displayed_error` sentinel: exit with the
        // error status without printing a report.
        TypeCoreError::ExtensionAlreadyDisplayed => UserDiagnostic::new(String::new(), 2).into(),
        other => unreachable!("builtin_extension_error returned {other:?}"),
    }
}

fn format_builtin_extension_error_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    error: &BuiltinExtensionError,
) -> String {
    let mut output =
        format_compiler_error_report(arena, source, filename, error.loc, &error.message);
    // OCaml `Location.default_error_reporter` prints each sub-error after a
    // break (`@,@[%a@]`), which shares the blank line ending the parent
    // report.
    for sub in &error.sub {
        let sub = format_builtin_extension_error_report(arena, source, filename, sub);
        output.push_str(sub.strip_prefix('\n').unwrap_or(&sub));
    }
    output
}

fn format_compiler_error_report_with_unindented_continuation(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);
    output.push_str("  ");
    output.push_str(message);
    if !message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_compiler_error_report_with_unindented_break(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    first_line: &str,
    second_line: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);
    output.push_str("  ");
    output.push_str(first_line);
    output.push('\n');
    output.push_str(second_line);
    output.push_str("\n\n");
    output
}

fn format_cannot_apply_module_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    mty: &crate::types::decl::ModuleType,
    origin: Option<&crate::types::Path>,
) -> String {
    // typemod.ml:1816 "@[This module is not a functor; it has type@ %a@]".
    let rendered_module_type = match origin {
        Some(origin) => {
            crate::types::includemod::format_persistent_module_type(type_ctx, mty, origin)
        }
        None => format_typemod_module_type(type_ctx, mty),
    };
    let message = type_clash::render_error_message(|ppf| {
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str("This module is not a functor; it has type");
        ppf.space();
        crate::types::printtyp::pp_doc(ppf, &rendered_module_type);
        ppf.close_box();
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_missing_module_message(
    path: &crate::types::path::Path,
    expanded: &crate::types::path::Path,
) -> String {
    let head = expanded.head().name().to_string();
    if path.same(expanded) {
        format!(
            "Internal path {} is dangling.\nThe compiled interface for module {head} was not found.",
            path.name()
        )
    } else {
        format!(
            "Internal path {} expands to {} which is dangling.\nThe compiled interface for module {head} was not found.",
            path.name(),
            expanded.name()
        )
    }
}

fn format_cannot_eliminate_dependency_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    mty: &crate::types::decl::ModuleType,
) -> String {
    let rendered_module_type =
        crate::types::includemod::format_module_type_full_paths(type_ctx, mty);
    // typemod.ml:1819-1823: "@[This functor has type@ %a@ The parameter
    // cannot be eliminated in the result type.@  Bind the argument to a
    // module identifier.@]", the module type printed by `pp_doc`
    // (res_outcome_printer.ml:426-440).
    let message = type_clash::render_error_message(|ppf| {
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str("This functor has type");
        ppf.space();
        crate::types::printtyp::pp_doc(ppf, &rendered_module_type);
        ppf.space();
        ppf.str("The parameter cannot be eliminated in the result type.");
        ppf.space();
        ppf.str(" Bind the argument to a module identifier.");
        ppf.close_box();
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_structure_expected_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    mty: &crate::types::decl::ModuleType,
) -> String {
    // typemod.ml:1826 "@[This module is not a structure; it has type@ %a".
    let rendered_module_type = format_typemod_module_type(type_ctx, mty);
    let message = type_clash::render_error_message(|ppf| {
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str("This module is not a structure; it has type");
        ppf.space();
        crate::types::printtyp::pp_doc(ppf, &rendered_module_type);
        ppf.close_box();
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

/// A message printing two types in one naming session, as
/// `Printtyp.reset_and_mark_loops ty; Printtyp.mark_loops ty'` does before
/// the report prints both (typedecl.ml:2217-2218, 2223-2224).
fn format_two_type_message(
    type_ctx: &TypeContext,
    first: TypeExprRef,
    second: TypeExprRef,
    f: impl FnOnce(&mut crate::parser::formatter::Formatter<&mut Vec<u8>>, &str, &str),
) -> String {
    let mut printer = TypeExprPrinter::new(type_ctx);
    printer.reset();
    printer.mark_loops(first);
    printer.mark_loops(second);
    let first = printer.print(first);
    let second = printer.print(second);
    type_clash::render_error_message(|ppf| f(ppf, &first, &second))
}

fn format_typemod_module_type(
    type_ctx: &TypeContext,
    mty: &crate::types::decl::ModuleType,
) -> String {
    // `Printtyp.modtype` prints values with `tree_of_type_scheme`, which names
    // non-generalized variables `'_weakN` (printtyp.ml).
    crate::types::includemod::format_module_type_show_weak(type_ctx, mty)
}

fn format_with_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    error: &crate::types::includemod::IncludeModError,
) -> String {
    let lid = format_longident_for_report(arena, lid);
    let message = crate::types::includemod::format_report(
        type_ctx,
        filename,
        error,
        crate::types::includemod::ReportHeading::WithMismatch { lid: &lid },
    );
    format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
}

/// Where an error report points: the source text and file it is framed
/// against, and the location inside it. Report formatters take it as one
/// argument alongside their error-specific fields.
#[derive(Clone, Copy)]
struct ReportSite<'a> {
    arena: &'a ParseArena,
    source: &'a str,
    filename: &'a str,
    loc: LocIdx,
}

impl<'a> ReportSite<'a> {
    fn new(arena: &'a ParseArena, source: &'a str, filename: &'a str, loc: LocIdx) -> Self {
        Self {
            arena,
            source,
            filename,
            loc,
        }
    }
}

fn format_with_makes_applicative_functor_ill_typed_report(
    type_ctx: &TypeContext,
    site: ReportSite<'_>,
    lid: &Longident,
    path: &crate::types::Path,
    error: &crate::types::includemod::IncludeModError,
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    let lid = format_longident_for_report(arena, lid);
    let message = crate::types::includemod::format_report(
        type_ctx,
        filename,
        error,
        crate::types::includemod::ReportHeading::WithMakesApplicativeFunctorIllTyped {
            lid: &lid,
            path: &path.name(),
        },
    );
    format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
}

fn format_not_a_variant_type_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    format_compiler_error_report_with_unindented_break(
        arena,
        source,
        filename,
        loc,
        &format!("The type {}", format_longident_for_report(arena, lid)),
        "is not a variant type",
    )
}

fn format_type_params_not_supported_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    format_compiler_error_report_with_unindented_break(
        arena,
        source,
        filename,
        loc,
        &format!("The type {}", format_longident_for_report(arena, lid)),
        "has type parameters, but type parameters are not supported here.",
    )
}

fn format_unbound_type_constructor_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    alternatives: &[String],
) -> String {
    let name = format_longident_for_report(arena, lid);
    let spellcheck_name = arena.get_string(lid.last_idx());
    if let Some(hint) = super_spellcheck_hint(spellcheck_name, alternatives) {
        return format_compiler_error_report(
            arena,
            source,
            filename,
            loc,
            &format!(
                "This type constructor, `{name}`, can't be found.\n\n\n{INFO}Hint: Did you mean {hint}?{RESET}"
            ),
        );
    }

    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!(
            "This type constructor, `{name}`, can't be found.\nIf you wanted to write a recursive type, don't forget the `rec` in `type rec`"
        ),
    )
}

fn format_unbound_type_constructor_incomplete_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    path: &crate::types::Path,
) -> String {
    let name = format_type_path_for_report(path);
    format_compiler_error_report_with_unindented_break(
        arena,
        source,
        filename,
        loc,
        &format!("The type constructor {name}"),
        "is not yet completely defined",
    )
}

fn format_unbound_type_variable_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
) -> String {
    let mut report = format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("Unbound type parameter {name}"),
    );
    report.push('\n');
    report
}

fn format_unbound_type_declaration_variable_report(
    type_ctx: &TypeContext,
    site: ReportSite<'_>,
    name: &str,
    detail: Option<&UnboundTypeVarDetail>,
    var: Option<TypeExprRef>,
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    // typedecl.ml:2182-2201: the period starts `explain_unbound_gen`'s
    // explanation (".@.@[In ...").
    let mut message = String::from("  A type variable is unbound in this type declaration");
    if let Some(detail) = detail {
        if let UnboundTypeVarDetail::Constructor {
            name: case_name,
            args,
        } = detail
        {
            // typedecl.ml:2185-2193: `typ ti` is a fresh tuple of the
            // argument types; the case prints `Printtyp.constructor_arguments`.
            let tys = match args {
                crate::types::ConstructorArguments::CstrTuple(tys) => tys.clone(),
                crate::types::ConstructorArguments::CstrRecord(labels) => {
                    labels.iter().map(|l| l.ld_type).collect()
                }
            };
            let typ_ti = type_ctx.new_generic_type(TypeDesc::Ttuple(type_ctx.new_type_list(&tys)));
            let mut printer = TypeExprPrinter::new(type_ctx);
            printer.reset();
            printer.mark_loops(typ_ti);
            if let Some(var) = var {
                let ty0 = type_ctx.new_generic_type(TypeDesc::Tobject { fields: var });
                printer.mark_loops(ty0);
            }
            let args_text = printer.printtyp.constructor_arguments(args);
            let var_text = match var {
                Some(var) => printer.print(var),
                None => name.to_string(),
            };
            message.push_str(".\n");
            message.push_str(&format_explain_unbound_gen(
                "case",
                &format!("{case_name} of "),
                &args_text,
                &var_text,
            ));
            return format_compiler_error_report_raw_message(
                arena, source, filename, loc, &message,
            );
        }
        let (kwd, label, ty) = match detail {
            UnboundTypeVarDetail::Constructor { .. } => unreachable!(),
            UnboundTypeVarDetail::Type { ty } => ("type", String::new(), *ty),
            UnboundTypeVarDetail::Case {
                name: case_name,
                ty,
                polymorphic,
            } => (
                "case",
                if *polymorphic {
                    format!("`{case_name} of ")
                } else {
                    format!("{case_name} of ")
                },
                *ty,
            ),
            UnboundTypeVarDetail::Field {
                name: field_name,
                ty,
            } => ("field", format!("{field_name}: "), *ty),
            UnboundTypeVarDetail::Method {
                name: method_name,
                ty,
            } => ("field", format!("{method_name}: "), *ty),
        };
        // `Typedecl.explain_unbound_gen` (typedecl.ml:2080-2090):
        // `reset_and_mark_loops_list [typ ti; ty0]` with
        // `ty0 = newgenty (Tobject (tv, ref None))` to force aliasing, then
        // print `typ ti` and `tv` in that naming session.
        let mut printer = TypeExprPrinter::new(type_ctx);
        printer.reset();
        printer.mark_loops(ty);
        if let Some(var) = var {
            let ty0 = type_ctx.new_generic_type(TypeDesc::Tobject { fields: var });
            printer.mark_loops(ty0);
        }
        let ty_text = printer.format(ty);
        let var_text = match var {
            Some(var) => printer.print(var),
            None => name.to_string(),
        };
        message.push_str(".\n");
        message.push_str(&format_explain_unbound_gen(
            kwd, &label, &ty_text, &var_text,
        ));
    }
    format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
}

/// `explain_unbound_gen` (typedecl.ml:2080-2090) after the `.@.` flush:
/// `@[<hov2>In %s@ %a@;<1 -2>the variable %a is unbound@]` from column 0,
/// the item printed by `explain_unbound`'s `%s%a` (typedecl.ml:2149-2151):
/// its label, then its type.
fn format_explain_unbound_gen(kwd: &str, label: &str, item_type: &str, var: &str) -> String {
    type_clash::render_error_message_at_column0(|ppf| {
        ppf.open_hovbox(2);
        ppf.str(&format!("In {kwd}"));
        ppf.space();
        ppf.string_as(label.len(), label);
        crate::types::printtyp::pp_doc(ppf, item_type);
        ppf.break_(1, -2);
        ppf.str("the variable ");
        crate::types::printtyp::pp_doc(ppf, var);
        ppf.str(" is unbound");
        ppf.close_box();
    })
}

fn format_unbound_modtype_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    alternatives: &[String],
) -> String {
    let name = format_longident_for_report(arena, lid);
    if let Some(hint) = spellcheck_hint(&name, alternatives) {
        let mut raw_message = String::new();
        raw_message.push_str("  Unbound module type ");
        raw_message.push_str(&name);
        raw_message.push('\n');
        raw_message.push_str("Hint: Did you mean ");
        raw_message.push_str(&hint);
        raw_message.push('?');
        format_compiler_error_report_raw_message(arena, source, filename, loc, &raw_message)
    } else {
        format_compiler_error_report(
            arena,
            source,
            filename,
            loc,
            &format!("Unbound module type {name}"),
        )
    }
}

fn format_invalid_variable_name_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
) -> String {
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!(
            "The type variable name {name} is not allowed; type variable names cannot start with an underscore."
        ),
    )
}

fn format_cannot_quantify_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
    ty: TypeExprRef,
) -> String {
    let reason = if crate::types::btype::is_tvar(type_ctx, ty) {
        "it escapes its scope"
    } else if crate::types::btype::is_tunivar(type_ctx, ty) {
        "it is already bound to another variable"
    } else {
        "it is not a variable"
    };
    let message = format_cannot_quantify_message(name, reason);
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_cannot_quantify_message(name: &str, reason: &str) -> String {
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.set_margin(76);
        ppf.open_hovbox(0);
        ppf.print(format_args!(
            "The universal type variable '{name} cannot be generalized:"
        ));
        ppf.space();
        ppf.print(format_args!("{reason}."));
        ppf.close_box();
        ppf.flush();
    }
    String::from_utf8(buf).unwrap_or_default()
}

fn format_multiple_constraints_on_type_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!(
            "Multiple constraints for type {}",
            format_longident_for_report(arena, lid)
        ),
    )
}

fn format_present_has_conjunction_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
) -> String {
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The present constructor {label} has a conjunctive type"),
    )
}

fn format_present_has_no_type_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
) -> String {
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The present constructor {label} has no type"),
    )
}

fn format_constructor_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_constructor_mismatch(ppf, type_ctx, actual, expected)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_not_a_variant_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    ty: TypeExprRef,
) -> String {
    let message =
        type_clash::render_error_message(|ppf| type_clash::print_not_a_variant(ppf, type_ctx, ty));
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_method_mismatch_report(
    type_ctx: &TypeContext,
    site: ReportSite<'_>,
    label: &str,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_method_mismatch(ppf, type_ctx, label, actual, expected)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_type_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    // Typetexp `Type_mismatch` (typetexp.ml:790-794).
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_report_unification_error(
            ppf,
            type_ctx,
            trace,
            "This type",
            "should be an instance of type",
        )
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_alias_type_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    // Typetexp `Alias_type_mismatch` (typetexp.ml:795-799).
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_report_unification_error(
            ppf,
            type_ctx,
            trace,
            "This alias is bound to type",
            "but is used as an instance of type",
        )
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_type_arity_mismatch_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    expected: usize,
    provided: usize,
) -> String {
    let name = format_longident_for_report(arena, lid);
    let plural = |count: usize| if count == 1 { "" } else { "s" };
    // typetexp.ml:776-789: both messages are laid out in a Format box.
    let message = format_boxed_message(|ppf| {
        if expected == 0 {
            ppf.print(format_args!(
                "The type `{name}` is not generic so expects no arguments,"
            ));
            ppf.space();
            ppf.print(format_args!(
                "but is here given {provided} argument{}.",
                plural(provided)
            ));
            ppf.space();
            ppf.str("Have you tried removing the angular brackets `<` and `>` and the");
            ppf.space();
            ppf.print(format_args!(
                "arguments within them and just writing `{name}` instead? "
            ));
        } else {
            ppf.print(format_args!("The type constructor `{name}`"));
            ppf.space();
            ppf.print(format_args!(
                "expects {expected} type argument{},",
                plural(expected)
            ));
            ppf.space();
            ppf.print(format_args!("but is given {provided}"));
        }
    });
    format_compiler_error_report(arena, source, filename, loc, &message)
}

/// Lay out a report message printed as `@[...@]` by OCaml: a `Pp_box` in the
/// report body, whose two-column indent leaves a 76-column margin.
fn format_boxed_message(
    f: impl FnOnce(&mut crate::parser::formatter::Formatter<&mut Vec<u8>>),
) -> String {
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.set_margin(76);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        f(&mut ppf);
        ppf.close_box();
        ppf.flush();
    }
    String::from_utf8(buf).unwrap_or_default()
}

fn format_inconsistent_constraint_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    if !trace.is_empty() {
        // typedecl.ml:2171-2175: "The type constraints are not consistent.@."
        // then `Printtyp.report_unification_error` from column 0.
        let unification = type_clash::render_error_message_at_column0(|ppf| {
            type_clash::print_report_unification_error(
                ppf,
                type_ctx,
                trace,
                "Type",
                "is not compatible with type",
            )
        });
        format_compiler_error_report_with_unindented_break(
            arena,
            source,
            filename,
            loc,
            "The type constraints are not consistent.",
            unification.trim_end_matches('\n'),
        )
    } else {
        format_compiler_error_report(
            arena,
            source,
            filename,
            loc,
            "The type constraints are not consistent.",
        )
    }
}

fn format_definition_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    ty: TypeExprRef,
    errs: &[crate::types::includecore::TypeMismatch],
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_definition_mismatch(ppf, type_ctx, ty, errs)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn variance_suffix(n: usize) -> &'static str {
    let is_teen = (n % 100) / 10 == 1;
    match n % 10 {
        1 if !is_teen => "st",
        2 if !is_teen => "nd",
        3 if !is_teen => "rd",
        _ => "th",
    }
}

fn format_variance((co, cn, inj): (bool, bool, bool)) -> String {
    let mut output = String::new();
    if inj {
        output.push_str("injective ");
    }
    match (co, cn) {
        (true, true) => output.push_str("invariant"),
        (true, false) => output.push_str("covariant"),
        (false, true) => output.push_str("contravariant"),
        (false, false) if inj => {}
        (false, false) => output.push_str("unrestricted"),
    }
    output
}

fn format_bad_variance_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    param_index: i32,
    actual: (bool, bool, bool),
    expected: (bool, bool, bool),
) -> String {
    let message = match param_index {
        -1 => format!(
            "In this definition, a type variable has a variance that\nis not reflected by its occurrence in type parameters.\nIt was expected to be {}, but it is {}.",
            format_variance(expected),
            format_variance(actual),
        ),
        -2 => "In this definition, a type variable cannot be deduced\nfrom the type parameters."
            .to_string(),
        -3 => format!(
            "In this definition, a type variable has a variance that\ncannot be deduced from the type parameters.\nIt was expected to be {}, but it is {}.",
            format_variance(expected),
            format_variance(actual),
        ),
        _ => {
            let param_index = param_index as usize;
            format!(
                "In this definition, expected parameter variances are not satisfied.\nThe {}{} type parameter was expected to be {},\nbut it is {}.",
                param_index,
                variance_suffix(param_index),
                format_variance(expected),
                format_variance(actual),
            )
        }
    };
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_compiler_warning_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warning: &TypeCoreWarning,
) -> String {
    let start_pos = arena.loc_start(warning.loc);
    let end_pos = arena.loc_end(warning.loc);
    let mut output = String::new();
    code_frame::mark_color_setup();

    output.push_str("\n  ");
    output.push_str(&code_frame::colorize_intro(
        &format!("Warning number {}", warning.warning.number()),
        warning.is_error,
    ));
    if warning.is_error {
        output.push_str(" (configured as error) ");
    }
    output.push('\n');
    output.push_str("  ");
    if !code_frame::has_printable_range(start_pos, end_pos) {
        output.push_str(&code_frame::colorize_location(filename));
        output.push_str("\n\n");
    } else {
        let location = code_frame::format_location(filename, start_pos, end_pos);
        output.push_str(&code_frame::colorize_location(&location));
        output.push_str("\n\n");
        // OCaml `Location.print ~message_kind`: `Code_frame.print ~is_warning`
        // is false for a warning configured as an error (location.ml:143-155).
        output.push_str(&if warning.is_error {
            code_frame::print(source, start_pos, end_pos)
        } else {
            code_frame::print_warning(source, start_pos, end_pos)
        });
        output.push('\n');
    }

    let indent_after_blank = !matches!(
        warning.warning,
        crate::diagnostics::Warning::UnusedVariable { .. }
            | crate::diagnostics::Warning::UnusedVariableStrict { .. }
    );
    let mut after_blank = false;
    let message = warning.warning.message();
    // An empty message still prints its indented message line.
    if message.is_empty() {
        output.push_str("  \n");
    }
    for (idx, line) in message.lines().enumerate() {
        let indent_line = match warning.warning {
            crate::diagnostics::Warning::NonClosedRecordPattern { .. } => idx == 0,
            crate::diagnostics::Warning::AttributePayload { .. } => idx == 0,
            crate::diagnostics::Warning::BsUnusedAttribute { .. } => idx == 0,
            crate::diagnostics::Warning::AllClausesGuarded => idx == 0,
            crate::diagnostics::Warning::AmbiguousPattern { .. } => idx == 0,
            crate::diagnostics::Warning::AmbiguousName { .. } => idx == 0,
            crate::diagnostics::Warning::FragileMatch { .. } => idx == 0,
            // `Builtin_attributes.cat` and warnings.ml:263-278 carry the
            // indentation of every later line in the message itself.
            crate::diagnostics::Warning::Deprecated { .. } => idx == 0,
            crate::diagnostics::Warning::FragileLiteralPattern => idx == 0,
            crate::diagnostics::Warning::UnreachableCase => idx == 0,
            // warnings.ml:412-438 carries its own indentation after the
            // first line; the printed return type keeps Format's layout.
            crate::diagnostics::Warning::BsToplevelExpressionUnit { .. } => idx == 0,
            crate::diagnostics::Warning::BsRecordRestOptionalOverlap { .. } => idx == 0,
            crate::diagnostics::Warning::UnusedConstructor { .. }
            | crate::diagnostics::Warning::UnusedExtension { .. } => idx == 0,
            crate::diagnostics::Warning::PartialMatch { .. } => {
                idx < 2 || line.starts_with("Hint:")
            }
            _ => indent_after_blank || !after_blank,
        };
        if !line.is_empty() && indent_line {
            output.push_str("  ");
            output.push_str(line);
        } else if !line.is_empty() {
            output.push_str(line);
        }
        if line.is_empty() {
            after_blank = true;
        }
        output.push('\n');
    }
    if message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
    output
}

/// [`format_type_warnings`], reading the source only when there is a
/// warning to report.
fn format_type_warnings_lazy<'s>(
    arena: &ParseArena,
    source: &dyn Fn() -> &'s str,
    filename: &str,
    warnings: &[TypeCoreWarning],
) -> String {
    if warnings.is_empty() {
        return String::new();
    }
    format_type_warnings(arena, source(), filename, warnings)
}

/// Type warnings rendered as one string for attempt-local buffering.
fn format_type_warnings(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warnings: &[TypeCoreWarning],
) -> String {
    let mut output = String::new();
    for warning in warnings {
        let report = format_compiler_warning_report(arena, source, filename, warning);
        output.push_str(&crate::source_text::decode_internal_utf8_runs(&report));
    }
    output
}

/// The source text an in-process compile reports diagnostics against. Like
/// OCaml's code frames (location.ml), it is read back from the source file.
fn read_in_process_source(filename: &str) -> String {
    std::fs::read(filename)
        .map(crate::source_text::latin1_bytes_to_string)
        .unwrap_or_default()
}

/// An error report preceded by the warnings printed before it.
/// An error raised once a unit is typed: the warnings reported so far, then
/// its report (the in-process compiles read the source only to report).
fn in_process_typed_unit_error<'s>(
    err: TypeModError,
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &dyn Fn() -> &'s str,
    filename: &str,
    warnings: &[TypeCoreWarning],
) -> anyhow::Error {
    if !arena.stores_locations() {
        return LocationRetry::Diagnostic.into();
    }
    let prefix = format_type_warnings_lazy(arena, source, filename, warnings);
    let suppress_info_style =
        !warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
    prefix_diagnostic(
        &prefix,
        type_mod_error_to_anyhow(err, type_ctx, arena, source(), filename, suppress_info_style),
    )
}

/// "Invalid string escape sequence" (ast_payload.ml:39-51) at a declaration
/// attribute's location, which may be in another unit's source.
fn invalid_string_escape_report(
    type_ctx: &TypeContext,
    filename: &str,
    loc: &Location,
) -> anyhow::Error {
    UserDiagnostic::new(
        format_compiler_error_report_from_external_location(
            type_ctx,
            filename,
            loc,
            "Invalid string escape sequence",
        ),
        2,
    )
    .into()
}

/// The error a unit-level payload reader raises (ast_payload.ml:39-51).
fn payload_type_error(error: crate::ast_payload::PayloadError) -> TypeModError {
    TypeModError::CoreError(crate::types::typemod::invalid_string_escape(error))
}

fn prefix_diagnostic(prefix: &str, err: anyhow::Error) -> anyhow::Error {
    if prefix.is_empty() {
        return err;
    }
    match err.downcast::<UserDiagnostic>() {
        Ok(diagnostic) => UserDiagnostic::new(
            format!("{prefix}{}", diagnostic.output()),
            diagnostic.exit_code(),
        )
        .into(),
        Err(err) => anyhow!("{prefix}{err}"),
    }
}

fn type_warnings_have_errors(warnings: &[TypeCoreWarning]) -> bool {
    warnings.iter().any(|warning| warning.is_error)
}

fn format_compiler_error_report_raw_message(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);
    let message = code_frame::apply_message_styles(message);
    output.push_str(&message);
    if !message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
    output
}

/// The name a `TypeCoreError::WrongName` reports and the type it was looked
/// up in.
struct WrongName<'a> {
    /// What was named: `record` (a field), `constructor`, ...
    kind: &'a str,
    /// The type the name was expected to belong to.
    ty: TypeExprRef,
    /// The phrase introducing `ty` ("This record pattern is expected to have", ...).
    expected: &'a str,
    /// The path of `ty`'s type constructor.
    path: &'a crate::types::Path,
    /// The name that does not belong to `ty`.
    name: &'a str,
}

fn format_wrong_name_report(
    type_ctx: &TypeContext,
    env: Option<std::rc::Rc<crate::types::env::Env>>,
    site: ReportSite<'_>,
    wrong: WrongName<'_>,
    alternatives: &[String],
    jsx_component_info: Option<&crate::types::typecore::JsxPropErrorInfo>,
) -> String {
    let WrongName {
        kind,
        ty,
        expected,
        path,
        name,
    } = wrong;
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    if let Some(jsx_component_info) = jsx_component_info {
        let mut message = String::new();
        if name == "children" {
            message.push_str("This JSX component does not accept child elements. It has no ");
            message.push_str(ERROR);
            message.push_str("children");
            message.push_str(RESET);
            message.push_str(" prop ");
        } else {
            message.push_str("The prop ");
            message.push_str(ERROR);
            message.push_str(name);
            message.push_str(RESET);
            message.push_str(" does not belong to the JSX component ");
        }
        if let Some(component_name) = &jsx_component_info.component_name {
            message.push_str(INFO);
            message.push('<');
            message.push_str(component_name);
            message.push_str(" />");
            message.push_str(RESET);
            message.push(' ');
        }
        message.push_str("\n\n\n");
        if let Some(hint) = spellcheck_hint(name, alternatives) {
            let mut raw_message = format_message_with_compiler_indentation(&message);
            raw_message.push_str("Hint: Did you mean ");
            raw_message.push_str(&hint);
            raw_message.push_str("?\n");
            return format_compiler_error_report_raw_message(
                arena,
                source,
                filename,
                loc,
                &raw_message,
            );
        }
        return format_compiler_error_report(arena, source, filename, loc, &message);
    }

    if path.is_constructor_typath() {
        let hint = spellcheck_hint(name, alternatives);
        let message = type_clash::render_error_message(|ppf| {
            type_clash::print_wrong_name_inline_record_field(
                ppf,
                type_ctx,
                name,
                path,
                hint.as_deref(),
            )
        });
        return format_compiler_error_report_formatted(arena, source, filename, loc, &message);
    }

    let label = if kind == "record" { "field" } else { kind };
    let type_text = format_type_expr(type_ctx, ty);
    // `Printtyp.path` under `wrap_printing_env env` (typecore.ml:5253-5254).
    let mut printer = crate::types::printtyp::Printtyp::new(type_ctx);
    if let Some(env) = env {
        printer.set_printing_env(&env);
    }
    // typecore.ml:4963-4971:
    //   @[<v>@[<2>The %s @{<error>%s@} does not belong to type @{<info>%a@}@]@,@,
    //   @[<2>%s type@ @{<info>%a@}@]@]
    // The type prints through `pp_doc` (res_outcome_printer.ml:426-440).
    let path_text = printer.string_of_path(path);
    let message = {
        let mut buf = Vec::new();
        {
            use crate::parser::formatter::{BoxKind, Formatter};
            // The report body sits in a box two columns in.
            let mut ppf = Formatter::new(&mut buf);
            ppf.set_margin(78);
            ppf.str("  ");
            ppf.open_box(BoxKind::V, 0);
            ppf.open_box(BoxKind::Box, 2);
            ppf.print(format_args!("The {label} "));
            ppf.string_as(0, ERROR);
            ppf.str(name);
            ppf.string_as(0, RESET);
            ppf.str(" does not belong to type ");
            ppf.string_as(0, INFO);
            ppf.str(&path_text);
            ppf.string_as(0, RESET);
            ppf.close_box();
            ppf.cut();
            ppf.cut();
            ppf.open_box(BoxKind::Box, 2);
            ppf.print(format_args!("{expected} type"));
            ppf.space();
            ppf.string_as(0, INFO);
            crate::types::printtyp::pp_doc(&mut ppf, &type_text);
            ppf.string_as(0, RESET);
            ppf.close_box();
            ppf.close_box();
            ppf.flush();
        }
        String::from_utf8(buf).unwrap_or_default()
    };
    let mut raw_message = message;
    raw_message.push('\n');
    if let Some(hint) = spellcheck_hint(name, alternatives) {
        raw_message.push_str("Hint: Did you mean ");
        raw_message.push_str(&hint);
        raw_message.push_str("?\n");
    }
    format_compiler_error_report_raw_message(arena, source, filename, loc, &raw_message)
}

fn format_name_type_mismatch_report(
    type_ctx: &TypeContext,
    site: ReportSite<'_>,
    kind: &str,
    lid: &Longident,
    expected: &(crate::types::Path, crate::types::Path),
    alternatives: &[(crate::types::Path, crate::types::Path)],
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    let lid = format_longident_for_report(arena, lid);
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_name_type_mismatch(
            ppf,
            type_ctx,
            None,
            kind,
            &lid,
            expected,
            alternatives,
        )
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_undefined_method_report(
    type_ctx: &TypeContext,
    site: ReportSite<'_>,
    ty: TypeExprRef,
    method: &str,
    alternatives: Option<&[String]>,
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    let hint = alternatives.map(|alts| spellcheck_hint(method, alts));
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_undefined_method(
            ppf,
            type_ctx,
            ty,
            method,
            hint.as_ref().map(|h| h.as_deref()),
        )
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_type_path_for_report(path: &crate::types::Path) -> String {
    let name = path.name();
    name.strip_prefix("Stdlib.")
        .or_else(|| name.strip_prefix("Stdlib_"))
        .unwrap_or(&name)
        .to_string()
}

fn format_unbound_value_report(
    site: ReportSite<'_>,
    name: &str,
    qualifier: Option<&str>,
    alternatives: &[String],
    module_suggestion: Option<&str>,
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    let mut message = String::new();
    if let Some(qualifier) = qualifier {
        message.push_str("The value ");
        message.push_str(name);
        message.push_str(" can't be found in ");
        message.push_str(qualifier);
    } else {
        message.push_str("The value ");
        message.push_str(name);
        message.push_str(" can't be found");
    }

    let spellcheck = super_spellcheck_hint(name, alternatives);
    if let Some(module_suggestion) = module_suggestion {
        let mut raw_message = String::new();
        raw_message.push_str("  ");
        raw_message.push_str(&message);
        raw_message.push('\n');

        if let Some(hint) = spellcheck {
            raw_message.push_str("  \n  ");
            raw_message.push_str(INFO);
            raw_message.push_str("Hint: Did you mean ");
            raw_message.push_str(&hint);
            raw_message.push('?');
            raw_message.push_str(RESET);
            raw_message.push_str("\n\n  Or did you mean");
        } else {
            raw_message.push_str("\n  Maybe you meant");
        }
        raw_message.push_str(" to use the module ");
        raw_message.push_str(INFO);
        raw_message.push_str(module_suggestion);
        raw_message.push_str(RESET);
        raw_message.push_str("?\n");

        return format_compiler_error_report_raw_message(
            arena,
            source,
            filename,
            loc,
            &raw_message,
        );
    }

    if let Some(hint) = spellcheck {
        message.push_str("\n\n");
        message.push_str(INFO);
        message.push_str("Hint: Did you mean ");
        message.push_str(&hint);
        message.push('?');
        message.push_str(RESET);
    }

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_unbound_module_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
    alternatives: &[String],
) -> String {
    let mut message = if name == "Str" {
        format!(
            "{INFO}The module or file Str can't be found.{RESET}\nAre you trying to use the standard library's Str?\nIf you're compiling to JavaScript, use {INFO}RegExp{RESET} instead.\nOtherwise, add str.cma to your ocamlc/ocamlopt command."
        )
    } else {
        format!(
            "{INFO}The module or file {name} can't be found.{RESET}\n- If it's a third-party dependency:\n  - Did you add it to the \"dependencies\" or \"dev-dependencies\" in rescript.json?\n- Did you include the file's directory to the \"sources\" in rescript.json?"
        )
    };
    // typetexp.ml:742-750 `spellcheck`: an `Ldot (r, s)` is checked by its
    // last component `s` against the modules of `r`.
    let last_component = name.rsplit('.').next().unwrap_or(name);
    if name != "Str"
        && let Some(hint) = super_spellcheck_hint(last_component, alternatives)
    {
        message.push_str("\n\n\n");
        message.push_str(INFO);
        message.push_str("Hint: Did you mean ");
        message.push_str(&hint);
        message.push('?');
        message.push_str(RESET);
    } else if name != "Str" {
        message.push_str("\n\n");
    }
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_access_functor_as_structure_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    let name = format_longident_for_report(arena, lid);
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The module {name} is a functor, not a structure"),
    )
}

fn format_cannot_scrape_alias_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    path: &crate::types::Path,
) -> String {
    let name = format_longident_for_report(arena, lid);
    let alias = format_type_path_for_report(path);
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The module {name} is an alias for module {alias}, which is missing"),
    )
}

fn format_unbound_constructor_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    alternatives: &[String],
) -> String {
    let name = format_longident_for_report(arena, lid);
    // typetexp.ml:742-750: spellcheck the last component of the longident.
    let hint = spellcheck_hint(name.rsplit('.').next().unwrap_or(&name), alternatives);
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_unbound_constructor(ppf, &name, hint.as_deref())
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

/// Append each line of `message` indented by two spaces, as the compiler's
/// report body prints it.
fn push_indented_lines(output: &mut String, message: &str) {
    for line in message.lines() {
        output.push_str("  ");
        output.push_str(line);
        output.push('\n');
    }
}

fn format_message_with_compiler_indentation(message: &str) -> String {
    let mut output = String::new();
    push_indented_lines(&mut output, message);
    output
}

/// OCaml `Misc.spellcheck` + `Misc.did_you_mean` (compiler/ext/misc.ml:240-272):
/// every alternative at the best edit distance within the cutoff, most recent
/// tie first, rendered as "a, b or c".
/// `Typetexp.super_spellcheck` + `Typetexp.did_you_mean`
/// (compiler/ml/typetexp.ml:717-740): unlike `Misc.did_you_mean`, the head of
/// the `Misc.spellcheck` result is printed last and the rest in reverse.
fn super_spellcheck_hint(name: &str, alternatives: &[String]) -> Option<String> {
    let choices = spellcheck_choices(name, alternatives);
    let (last, rev_rest) = choices.split_first()?;
    Some(if rev_rest.is_empty() {
        (*last).to_string()
    } else {
        let rest: Vec<&str> = rev_rest.iter().rev().copied().collect();
        format!("{} or {}", rest.join(", "), last)
    })
}

/// `Misc.spellcheck` + `Misc.did_you_mean` (compiler/ext/misc.ml:240-272).
fn spellcheck_hint(name: &str, alternatives: &[String]) -> Option<String> {
    let best = spellcheck_choices(name, alternatives);
    let (last, rest) = best.split_last()?;
    Some(if rest.is_empty() {
        (*last).to_string()
    } else {
        format!("{} or {}", rest.join(", "), last)
    })
}

/// `Misc.spellcheck` (compiler/ext/misc.ml:240-257): the closest candidates,
/// in the order of OCaml's prepend-on-tie fold.
fn spellcheck_choices<'a>(name: &str, alternatives: &'a [String]) -> Vec<&'a str> {
    let cutoff = match name.len() {
        1 | 2 => 0,
        3 | 4 => 1,
        5 | 6 => 2,
        _ => 3,
    };
    // Ties are collected in order and reversed once at the end, which yields
    // OCaml's prepend-on-tie order.
    let mut best: Vec<&str> = Vec::new();
    let mut best_dist = usize::MAX;
    let mut scratch = Vec::new();
    for candidate in alternatives {
        let Some(dist) = ocaml_edit_distance(name, candidate, cutoff, &mut scratch) else {
            continue;
        };
        if dist < best_dist {
            best.clear();
            best.push(candidate.as_str());
            best_dist = dist;
        } else if dist == best_dist {
            best.push(candidate.as_str());
        }
    }
    best.reverse();
    best
}

/// OCaml `Misc.edit_distance` (compiler/ext/misc.ml:195-238): Levenshtein
/// distance with adjacent transpositions, bounded by `cutoff`. `scratch` is a
/// reusable buffer for the `(la + 1) * (lb + 1)` distance matrix.
fn ocaml_edit_distance(a: &str, b: &str, cutoff: usize, scratch: &mut Vec<usize>) -> Option<usize> {
    let a = a.as_bytes();
    let b = b.as_bytes();
    let (la, lb) = (a.len(), b.len());
    let cutoff = cutoff.min(la.max(lb));
    if la.abs_diff(lb) > cutoff {
        return None;
    }
    let width = lb + 1;
    scratch.clear();
    scratch.resize((la + 1) * width, cutoff + 1);
    let m = &mut scratch[..];
    let at = |i: usize, j: usize| i * width + j;
    m[0] = 0;
    for i in 1..=la {
        m[at(i, 0)] = i;
    }
    for j in 1..=lb {
        m[at(0, j)] = j;
    }
    for i in 1..=la {
        let lo = 1.max(i.saturating_sub(cutoff + 1));
        let hi = lb.min(i + cutoff + 1);
        for j in lo..=hi {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            let mut best =
                (1 + m[at(i - 1, j)].min(m[at(i, j - 1)])).min(m[at(i - 1, j - 1)] + cost);
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                best = best.min(m[at(i - 2, j - 2)] + cost);
            }
            m[at(i, j)] = best;
        }
    }
    let result = m[at(la, lb)];
    (result <= cutoff).then_some(result)
}

fn format_label_multiply_defined_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
    jsx_component_info: Option<&crate::types::typecore::JsxPropErrorInfo>,
) -> String {
    if let Some(jsx_component_info) = jsx_component_info {
        let mut message = String::new();
        message.push_str("The prop ");
        message.push_str(INFO);
        message.push_str(label);
        message.push_str(RESET);
        message.push_str(" has already been passed to the component ");
        if let Some(component_name) = &jsx_component_info.component_name {
            message.push_str(INFO);
            message.push('<');
            message.push_str(component_name);
            message.push_str(" />");
            message.push_str(RESET);
            message.push(' ');
        }

        let mut raw_message = format_message_with_compiler_indentation(&message);
        raw_message.push_str("You can't pass the same prop more than once.\n");
        return format_compiler_error_report_raw_message(
            arena,
            source,
            filename,
            loc,
            &raw_message,
        );
    }

    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The record field label {label} is defined several times"),
    )
}

fn format_labels_missing_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    labels: &[String],
    jsx_component_info: Option<&crate::types::typecore::JsxPropErrorInfo>,
) -> String {
    let component_name = jsx_component_info.map(|info| info.component_name.as_deref());
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_labels_missing(ppf, labels, component_name)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

/// `Typecore.report_error`'s `Expr_type_clash` (typecore.ml:4879-4894).
#[allow(clippy::too_many_arguments)]
fn format_expr_type_clash_report_ocaml(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    context: &Option<TypeClashContext>,
    env: &crate::types::Env,
) -> String {
    if let Some((arity_a, arity_b)) = type_clash::expr_type_clash_arity_mismatch(type_ctx, trace) {
        return format_function_arity_mismatch_report(
            arena,
            source,
            filename,
            loc,
            arity_a as i32,
            arity_b as i32,
        );
    }
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_expr_type_clash(ppf, type_ctx, env, arena, source, loc, trace, context)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

/// A report whose message was laid out by Format like `Location.errorf`:
/// `default_error_reporter` prints it followed by `@,` and the final `@.`
/// (location.ml:237-251, 272-279), i.e. always two newlines.
fn format_compiler_error_report_formatted(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();
    push_compiler_error_report_header(&mut output, arena, source, filename, loc);
    output.push_str(&code_frame::apply_message_styles(message));
    output.push_str("\n\n");
    output
}

fn format_orpat_vars_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    id: &Ident,
    valid_idents: &[Ident],
) -> String {
    let message = format!(
        "Variable {} must occur on both sides of this | pattern",
        id.name()
    );
    let alternatives: Vec<String> = valid_idents
        .iter()
        .map(|valid| valid.name().to_string())
        .collect();

    if let Some(hint) = spellcheck_hint(id.name(), &alternatives) {
        let mut raw_message = format_message_with_compiler_indentation(&message);
        raw_message.push_str("Hint: Did you mean ");
        raw_message.push_str(&hint);
        raw_message.push('?');
        return format_compiler_error_report_raw_message(
            arena,
            source,
            filename,
            loc,
            &raw_message,
        );
    }

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_polymorphic_label_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    let message = format!(
        "The record field {} is polymorphic. You cannot instantiate it in a pattern.",
        format_longident_for_report(arena, lid)
    );
    format_compiler_error_report(arena, source, filename, loc, &message)
}

// Format's default margin is 78. The Location reporter adds two columns
// before the message; each <hov 2> heading box adds two more on a break.
fn format_function_arity_mismatch_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    actual_arity: i32,
    expected_arity: i32,
) -> String {
    let mut message = String::new();
    message.push_str("This function is expected to have ");
    message.push_str(INFO);
    message.push_str(&expected_arity.to_string());
    message.push_str(RESET);
    message.push(' ');
    message.push_str(if expected_arity == 1 {
        "argument"
    } else {
        "arguments"
    });
    message.push_str(", but");
    if actual_arity < expected_arity {
        message.push_str(" only");
    }
    message.push_str(" has ");
    message.push_str(ERROR);
    message.push_str(&actual_arity.to_string());
    message.push_str(RESET);

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_apply_non_function_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    typ: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_apply_non_function(ppf, type_ctx, typ)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_tagged_template_non_tag_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    typ: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_tagged_template_non_tag(ppf, type_ctx, typ)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_abstract_wrong_label_report(
    type_ctx: &TypeContext,
    source: &str,
    filename: &str,
    loc: &Location,
    label: &TypeArgLabel,
    ty: TypeExprRef,
) -> String {
    let label_mark = match label {
        TypeArgLabel::Nolabel => "but its first argument is not labelled".to_string(),
        TypeArgLabel::Labelled(label) => {
            format!("but its first argument is labelled ~{}", label.txt)
        }
        TypeArgLabel::Optional(label) => {
            format!("but its first argument is labelled ?{}", label.txt)
        }
    };
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_abstract_wrong_label(ppf, type_ctx, &label_mark, ty)
    });
    let mut output = String::new();
    push_compiler_error_report_header_from_location(&mut output, source, filename, loc);
    output.push_str(&code_frame::apply_message_styles(&message));
    output.push_str("\n\n");
    output
}

fn format_apply_wrong_label_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &ParserArgLabel,
    ty: TypeExprRef,
) -> String {
    let label = match label {
        ParserArgLabel::Nolabel => None,
        ParserArgLabel::Labelled(loc) => Some(format!("~{}", arena.get_string(loc.txt))),
        ParserArgLabel::Optional(loc) => Some(format!("?{}", arena.get_string(loc.txt))),
    };
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_apply_wrong_label(ppf, type_ctx, label.as_deref(), ty)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_field_not_optional_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
    typ: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_field_not_optional(ppf, type_ctx, name, typ)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_unbound_record_field_report(
    type_ctx: &TypeContext,
    site: ReportSite<'_>,
    field_name: &str,
    from_type: Option<TypeExprRef>,
    alternatives: &[String],
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    let hint = spellcheck_hint(
        field_name.rsplit('.').next().unwrap_or(field_name),
        alternatives,
    );
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_unbound_label(ppf, type_ctx, field_name, from_type, hint.as_deref())
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_uncurried_arity_mismatch_report(
    type_ctx: &TypeContext,
    site: ReportSite<'_>,
    function_type: TypeExprRef,
    expected_arity: usize,
    provided_arity: usize,
    provided_args: &[crate::parser::ast::ArgLabel],
    arity_suggestion: Option<&str>,
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    let args_from_type = collect_function_arg_labels(type_ctx, function_type);
    let args_from_type_unlabelled = args_from_type
        .iter()
        .filter(|arg| matches!(arg, TypeArgLabel::Nolabel))
        .count();
    let provided_unlabelled = provided_args
        .iter()
        .filter(|arg| matches!(arg, crate::parser::ast::ArgLabel::Nolabel))
        .count();
    let mismatch_in_unlabelled_args = args_from_type_unlabelled != provided_unlabelled;

    let required_args = args_from_type
        .iter()
        .filter_map(|arg| match arg {
            TypeArgLabel::Labelled(label) => Some(label.txt.clone()),
            TypeArgLabel::Nolabel | TypeArgLabel::Optional(_) => None,
        })
        .collect::<Vec<_>>();
    let passed_named_args = provided_args
        .iter()
        .filter_map(|arg| parser_arg_label_name(arg, arena).map(str::to_string))
        .collect::<Vec<_>>();
    let missing_required_args = required_args
        .iter()
        .filter(|arg| !passed_named_args.contains(arg))
        .cloned()
        .collect::<Vec<_>>();

    let named_args_of_fn_type = args_from_type
        .iter()
        .filter_map(|arg| match arg {
            TypeArgLabel::Labelled(label) | TypeArgLabel::Optional(label) => {
                Some(label.txt.clone())
            }
            TypeArgLabel::Nolabel => None,
        })
        .collect::<Vec<_>>();
    let superfluous_args = passed_named_args
        .iter()
        .filter(|arg| !named_args_of_fn_type.contains(arg))
        .cloned()
        .collect::<Vec<_>>();

    let is_fallback = missing_required_args.is_empty()
        && superfluous_args.is_empty()
        && !mismatch_in_unlabelled_args;

    // typecore.ml:5150-5220 lays the message out in one `@[<v>...@]` box.
    use crate::types::printtyp::{TAG_ERROR, TAG_INFO, TAG_RESET};
    let type_text = format_type_expr(type_ctx, function_type);
    let plural = |n: usize| if n == 1 { "" } else { "s" };
    let message = type_clash::render_error_message(|ppf| {
        let tagged =
            |ppf: &mut crate::parser::formatter::Formatter<&mut Vec<u8>>, tag: &str, text: &str| {
                ppf.string_as(0, tag);
                ppf.str(text);
                ppf.string_as(0, TAG_RESET);
            };
        ppf.open_vbox(0);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 2);
        ppf.str("This function call is incorrect.");
        ppf.close_box();
        ppf.cut();
        ppf.str("The function has type:");
        ppf.space();
        crate::types::printtyp::pp_doc(ppf, &type_text);
        if !is_fallback {
            ppf.cut();
        }
        if !missing_required_args.is_empty() {
            ppf.cut();
            ppf.str(&format!(
                "- Missing arguments that must be provided: {}",
                missing_required_args
                    .iter()
                    .map(|arg| format!("~{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
            ppf.cut();
            ppf.str("- Hint: Did you want to partially apply the function? You can do that by putting `...` just before the closing parens of the function call. Example: ");
            tagged(ppf, TAG_INFO, "yourFn(~arg1=someVar, ...)");
        }
        if !superfluous_args.is_empty() {
            ppf.cut();
            ppf.str(&format!(
                "- Called with arguments it does not take: {}",
                superfluous_args.join(", ")
            ));
        }
        if mismatch_in_unlabelled_args {
            ppf.cut();
            ppf.str("- The function takes ");
            tagged(
                ppf,
                TAG_INFO,
                &unlabelled_arg_count_message(
                    args_from_type_unlabelled,
                    provided_unlabelled,
                    CountPosition::Left,
                ),
            );
            ppf.str(&format!(
                " unlabelled argument{}, but is called with ",
                plural(args_from_type_unlabelled)
            ));
            tagged(
                ppf,
                TAG_ERROR,
                &unlabelled_arg_count_message(
                    provided_unlabelled,
                    args_from_type_unlabelled,
                    CountPosition::Right,
                ),
            );
        }
        if is_fallback {
            ppf.cut();
            ppf.cut();
            ppf.str("It is called with ");
            tagged(ppf, TAG_ERROR, &provided_arity.to_string());
            ppf.str(&format!(
                " argument{} but{} requires ",
                plural(provided_arity),
                if provided_arity > expected_arity {
                    " just"
                } else {
                    ""
                }
            ));
            tagged(ppf, TAG_INFO, &expected_arity.to_string());
            ppf.str(".");
        }
        if let Some(suggestion) = arity_suggestion {
            ppf.cut();
            ppf.cut();
            ppf.str("Hint: Try ");
            tagged(ppf, TAG_INFO, suggestion);
            ppf.str(" instead (takes ");
            tagged(ppf, TAG_INFO, &provided_arity.to_string());
            ppf.str(&format!(" argument{}).", plural(provided_arity)));
        }
        ppf.close_box();
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_constructor_arity_mismatch_report(
    site: ReportSite<'_>,
    name: &Longident,
    is_inline_record: bool,
    expected: usize,
    provided: usize,
) -> String {
    let ReportSite {
        arena,
        source,
        filename,
        loc,
    } = site;
    let name = format_longident_for_report(arena, name);
    let message = if is_inline_record && expected == 1 {
        let suffix = if provided == 0 {
            ", but it's not being passed any arguments"
        } else {
            ""
        };
        format!(
            "This variant constructor {INFO}{name}{RESET} expects an inline record as payload{suffix}."
        )
    } else {
        let argument = if expected == 1 {
            "argument"
        } else {
            "arguments"
        };
        let only = if provided < expected { " only" } else { "" };
        format!(
            "This variant constructor {INFO}{name}{RESET} expects {expected} {argument}, but it's{only} being passed {provided}."
        )
    };

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_longident_for_report(arena: &ParseArena, lid: &Longident) -> String {
    match lid {
        Longident::Lident(name) => arena.get_string(*name).to_string(),
        Longident::Ldot(prefix, name) => {
            format!(
                "{}.{}",
                format_longident_for_report(arena, prefix),
                arena.get_string(*name)
            )
        }
        Longident::Lapply(func, arg) => {
            format!(
                "{}({})",
                format_longident_for_report(arena, func),
                format_longident_for_report(arena, arg)
            )
        }
    }
}

#[derive(Clone, Copy)]
enum CountPosition {
    Left,
    Right,
}

fn unlabelled_arg_count_message(
    count: usize,
    other_count: usize,
    position: CountPosition,
) -> String {
    match (count, position) {
        (0, CountPosition::Left) => "no".to_string(),
        (0, CountPosition::Right) => "none".to_string(),
        _ if count > other_count => count.to_string(),
        _ => format!("just {count}"),
    }
}

fn parser_arg_label_name<'a>(
    label: &crate::parser::ast::ArgLabel,
    arena: &'a ParseArena,
) -> Option<&'a str> {
    match label {
        crate::parser::ast::ArgLabel::Nolabel => None,
        crate::parser::ast::ArgLabel::Labelled(loc)
        | crate::parser::ast::ArgLabel::Optional(loc) => Some(arena.get_string(loc.txt)),
    }
}

fn collect_function_arg_labels(
    type_ctx: &TypeContext,
    function_type: TypeExprRef,
) -> Vec<TypeArgLabel> {
    let mut labels = Vec::new();
    let mut current = function_type;
    let mut seen = AHashSet::new();

    loop {
        if !seen.insert(current) {
            break;
        }

        match &*type_ctx.get_desc(current) {
            TypeDesc::Tarrow { args, ret } => {
                labels.extend(
                    type_ctx
                        .type_args(args)
                        .iter()
                        .map(|arg| arg.label().to_arg_label()),
                );
                current = *ret;
            }
            _ => break,
        }
    }

    labels
}

fn format_type_expr(type_ctx: &TypeContext, ty: TypeExprRef) -> String {
    TypeExprPrinter::new(type_ctx).format(ty)
}

fn format_package_type_expr_for_error(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    ty: TypeExprRef,
) -> String {
    let repr = type_ctx.repr(ty);
    let desc = *type_ctx.get_desc(repr);
    let TypeDesc::Tpackage { path, lids, args } = desc else {
        return format_type_expr(type_ctx, ty);
    };
    let lids = type_ctx.package_lids(lids);
    if lids.is_empty() {
        return format_type_expr(type_ctx, ty);
    }

    let constraints = lids
        .iter()
        .zip(type_ctx.type_list(args).iter())
        .map(|(lid, arg)| {
            format!(
                "type {} = {}",
                format_longident_for_report(arena, lid),
                format_type_expr(type_ctx, arg)
            )
        })
        .collect::<Vec<_>>();
    format!("module({} with {})", path.name(), constraints.join(" and "))
}

fn format_non_generalizable_type_expr(type_ctx: &TypeContext, ty: TypeExprRef) -> String {
    TypeExprPrinter::new_with_weak_names(type_ctx).format(ty)
}

/// A `Printtyp` naming session (compiler/ml/printtyp.ml): type variables
/// keep their names across every type printed with the same printer.
struct TypeExprPrinter<'a> {
    type_ctx: &'a TypeContext,
    printtyp: crate::types::printtyp::Printtyp<'a>,
    weak_names: bool,
    /// Types whose loops were marked since the last `reset`. OCaml's callers
    /// mark each printed type once (`reset_and_mark_loops`,
    /// `prepare_expansion`); marking an open object or row a second time
    /// would alias it.
    marked: Vec<TypeExprRef>,
}

impl<'a> TypeExprPrinter<'a> {
    fn new(type_ctx: &'a TypeContext) -> Self {
        Self {
            type_ctx,
            printtyp: crate::types::printtyp::Printtyp::new(type_ctx),
            weak_names: false,
            marked: Vec::new(),
        }
    }

    fn new_with_weak_names(type_ctx: &'a TypeContext) -> Self {
        Self {
            weak_names: true,
            ..Self::new(type_ctx)
        }
    }

    /// `Printtyp.reset`.
    fn reset(&mut self) {
        self.printtyp.reset();
        self.marked.clear();
    }

    /// `Printtyp.mark_loops`.
    fn mark_loops(&mut self, ty: TypeExprRef) {
        self.marked.push(self.type_ctx.repr(ty));
        self.printtyp.mark_loops(ty);
    }

    /// `Printtyp.mark_loops` unless the session already marked `ty`.
    fn mark_loops_once(&mut self, ty: TypeExprRef) {
        if !self.marked.contains(&self.type_ctx.repr(ty)) {
            self.mark_loops(ty);
        }
    }

    /// `Printtyp.type_expr` without marking.
    fn print(&mut self, ty: TypeExprRef) -> String {
        self.printtyp.type_expr(ty)
    }

    /// Print `ty` (marking its loops first if the session has not):
    /// `type_expr`, or `type_sch` for a weak-name printer.
    fn format(&mut self, ty: TypeExprRef) -> String {
        self.mark_loops_once(ty);
        if self.weak_names {
            self.printtyp.type_sch(ty)
        } else {
            self.printtyp.type_expr(ty)
        }
    }
}

#[cfg(test)]
#[derive(Clone, Debug, Default)]
struct PreJsDiscriminatorTrace {
    type_context_stamp: i32,
    raw_converter_stamp: i32,
    raw_max_stamp: i32,
    raw_lambda: String,
    lowered_lambda: String,
    js_program: String,
}

/// Compile ReScript source to JavaScript.
pub fn compile_source_to_js(source: &str, filename: &str) -> Result<String> {
    compile_source_to_js_with_options(source, filename, &CompilerOptions::default())
}

/// Compile ReScript source to JavaScript with options.
pub fn compile_source_to_js_with_options(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<String> {
    compile_source_to_js_with_options_inner(
        source,
        filename,
        options,
        #[cfg(test)]
        None,
    )
}

/// Borrow the inputs of a possible fallback. O(1), no heap allocation.
fn general_syntax_provider<'a>(
    source: &'a str, filename: &'a str, options: &'a CompilerOptions,
) -> impl Fn() -> Result<GeneralSyntax<Structure>> + 'a {
    move || general_implementation_syntax(source, filename, options)
}

/// The general syntax of an implementation whose plan could not be used
/// ([`DerivedFallback`]): the frontend run again on its
/// source with [`DerivedPath::Fallback`]. Its reports were printed with the
/// first tree and are not printed again. Cost: one parse and frontend run
/// of the unit and one copy of the options, only for a unit that falls back.
fn general_implementation_syntax(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<GeneralSyntax<Structure>> {
    let mut options = options.clone();
    options.derived_path = DerivedPath::Fallback;
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    let frontend =
        run_implementation_frontend(&mut parser, structure, source, filename, &options, &mut String::new())?;
    parser.arena_mut().reserve_typecheck_synthetic_capacity();
    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    Ok(GeneralSyntax { arena: parser.into_arena(), tree: frontend.structure, warning_locations: None })
}

#[cfg(test)]
fn compile_source_to_js_with_trace(
    source: &str,
    filename: &str,
    trace: &mut PreJsDiscriminatorTrace,
) -> Result<String> {
    compile_source_to_js_with_options_inner(
        source,
        filename,
        &CompilerOptions::default(),
        Some(trace),
    )
}

/// Output of [`run_implementation_frontend`]: the rewritten structure plus the
/// file-level settings later phases read from the source structure.
pub struct ImplementationFrontend {
    /// The structure after the external and builtin PPXs.
    pub structure: Structure,
    /// A frontend warning was configured as an error.
    pub warnings_fatal: bool,
    /// The file's leading `@@warning` attributes, applied again when type
    /// checking starts.
    pub frontend_warning_specs: Vec<ppx::WarningAttributeSpec>,
    /// The file's `@@config` flag overrides.
    pub file_config: FileConfigOverrides,
    /// The file's `@@directive` payloads, printed atop the JavaScript.
    pub file_directives: Vec<String>,
    /// `let?` is enabled, by the command line or `@@config`.
    pub experimental_let_unwrap: bool,
}

/// Everything OCaml runs between parsing and type checking an implementation:
/// parser warnings and
/// `Ppx_entry.rewrite_implementation` (compiler/frontend/ppx_entry.ml:45-60),
/// together with the frontend checks Rust performs around them. This is also
/// what `bsc -bs-ast` does before writing the AST
/// (compiler/core/js_implementation.ml:172-186). Warning reports are appended
/// to `out` in emission order; the caller prints or captures them.
pub fn run_implementation_frontend(
    parser: &mut Parser<'_>,
    structure: Structure,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    out: &mut String,
) -> Result<ImplementationFrontend> {
    let census_start = crate::derived_census::start(options.derived_census.is_some());
    if let Some(path) = &options.derived_census {
        parser.arena_mut().derived_census = Some(Box::new(crate::derived_census::Census::new(path, filename)));
    }
    let parser_warnings_have_errors =
        format_parser_warnings(parser, source, filename, options, out);
    if parser.has_errors() {
        return Err(parser_error_to_anyhow(parser, source, filename));
    }
    parser.arena_mut().set_builtin_spice(options.builtin_spice());
    parser
        .arena_mut()
        .set_derived_plans(options.derived_path.plans_off());
    let frontend_warnings =
        ppx::collect_leading_builtin_warning_attributes(&structure, parser.arena())
            .map_err(|err| ppx_error_to_anyhow(err, parser.arena(), source, filename))?;
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_attribute_specs(&structure, parser.arena())
            .map_err(|err| ppx_error_to_anyhow(err, parser.arena(), source, filename))?;
    let mut ppx_warnings_have_errors = parser_warnings_have_errors
        | format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &warning_config_for_options(options),
            &frontend_warnings,
            out,
        );
    let config_processing = validate_file_config_from_structure(
        &structure,
        parser.arena(),
        &warning_config_for_options_and_leading_attrs(options, &frontend_warning_specs),
    );
    for (warning, config) in &config_processing.warnings {
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            out,
        );
    }
    if let Some(err) = config_processing.error {
        return Err(config_payload_error_to_anyhow(
            err,
            parser.arena(),
            source,
            filename,
        ));
    }
    let file_config = config_processing.overrides;
    let file_warning_config = warning_config_for_options_file_config_and_leading_attrs(
        options,
        &file_config,
        &frontend_warning_specs,
    );
    let file_directives = extract_file_directives_from_structure(&structure, parser.arena())
        .map_err(|err| directive_payload_error_to_anyhow(err, parser.arena(), source, filename))?;
    let experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
    // Source fallback path: only run JSX rewrite when the file enables `-bs-jsx`.
    let jsx_version = options.jsx_version.or(file_config.jsx_version);
    let structure = if let Some(jsx_version) = jsx_version {
        let (structure, jsx_warnings) = jsx_ppx::transform_structure_collecting_warnings(
            structure,
            jsx_version,
            jsx_module_name(options, Some(&file_config)),
            parser.arena_mut(),
        );
        let jsx_warnings = jsx_preprocessor_warnings_to_ppx(parser.arena_mut(), jsx_warnings);
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &file_warning_config,
            &jsx_warnings,
            out,
        );
        structure.map_err(|e| jsx_ppx_error_to_anyhow(e, parser.arena(), source, filename))?
    } else {
        structure
    };

    let structure = if file_config.no_builtin_ppx(options) {
        structure
    } else {
        // OCaml `Ast_config.process_str` marks the leading `@@config` before
        // the builtin mapper runs (compiler/frontend/ppx_entry.ml:48-50).
        ppx::mark_config_attributes_structure(&structure, parser.arena());
        // Rewrite expressions: desugar pipe (->), setter (#=), property access (##),
        // await, tagged templates, encode externals, and apply spice mapper rewrites.
        // spice is handled here, so avoid running a second top-level spice expansion pass.
        // The mapper's warnings precede its error.
        let (rewritten, ppx_warnings) = ppx::rewrite_structure_with_warnings(
            &structure,
            parser.arena_mut(),
            experimental_let_unwrap,
        );
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &file_warning_config,
            &ppx_warnings,
            out,
        );
        rewritten.map_err(|e| ppx_error_to_anyhow(e, parser.arena(), source, filename))?
    };
    let mut census = parser.arena_mut().derived_census.take();
    // OCaml `Bs_ast_invariant.emit_external_warnings_on_structure` runs over
    // the rewritten structure (compiler/frontend/ppx_entry.ml:60-63).
    let (unused_attribute_warnings, invariant_error) =
        ppx::collect_unused_attribute_warnings_structure(&structure, parser.arena(), census.as_deref_mut(), !file_config.no_builtin_ppx(options));
    ppx_warnings_have_errors |= format_ppx_warnings_with_config(
        parser.arena(),
        source,
        filename,
        &file_warning_config,
        &unused_attribute_warnings,
        out,
    );
    if let Some(e) = invariant_error {
        return Err(ppx_error_to_anyhow(e, parser.arena(), source, filename));
    }
    parser.arena_mut().derived_census = census;
    // js_implementation.ml:125-129: `after_parsing_impl` runs the second
    // `Ast_config.process_str` after the builtin ppx.
    for (warning, config) in &config_processing.late_warnings {
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            out,
        );
    }
    // js_implementation.ml:130 `if !Js_config.no_export then no_export ast`,
    // applied once to the top-level structure after the frontend.
    let structure =
        crate::binary_ast::writer::apply_no_export_config(parser.arena_mut(), structure);
    if let Some(start) = census_start {
        let elapsed = crate::derived_census::nanos(start.elapsed());
        if let Some(mut census) = parser.arena_mut().derived_census.take() {
            census.account_frontend(elapsed);
            parser.arena_mut().derived_census = Some(census);
        }
    }
    Ok(ImplementationFrontend {
        structure,
        warnings_fatal: ppx_warnings_have_errors,
        frontend_warning_specs,
        file_config,
        file_directives,
        experimental_let_unwrap,
    })
}

fn compile_source_to_js_with_options_inner(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    #[cfg(test)] mut discriminator_trace: Option<&mut PreJsDiscriminatorTrace>,
) -> Result<String> {
    // Parse
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    let mut frontend_output = String::new();
    let frontend = run_implementation_frontend(
        &mut parser,
        structure,
        source,
        filename,
        options,
        &mut frontend_output,
    );
    if !options.frontend_already_reported {
        write_stderr(&frontend_output);
    }
    let unit_options = options;
    let ImplementationFrontend {
        structure,
        warnings_fatal: ppx_warnings_have_errors,
        frontend_warning_specs,
        file_config,
        file_directives,
        experimental_let_unwrap,
    } = frontend?;
    // The rest of the compile sees the `@@config` flags applied after the
    // command line (rescript_compiler_driver.ml:539-557).
    let effective_options = file_config.apply(options);
    let options = &*effective_options;
    let ppx_warnings_have_errors = if options.frontend_already_reported {
        report_stored_ast_config_warnings(
            first_config_attribute_of_structure(&structure, parser.arena()),
            true,
            parser.arena(),
            source,
            filename,
            options,
        )
    } else {
        ppx_warnings_have_errors
    };
    parser.arena_mut().reserve_typecheck_synthetic_capacity();

    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    let current_unit_name = options.current_unit_name();
    let fallback = || general_implementation_syntax(source, filename, unit_options);
    let (type_ctx, result) = type_structure_two_modes(
        CheckUnit { filename, options, registry: None,
            module_name: current_unit_name.as_deref(), file_config: &file_config,
            frontend_warning_specs: &frontend_warning_specs, derived_plans: true,
            mode: crate::types::context::CheckMode::from_env() },
        UnitSyntax::new(parser.arena(), &structure, options),
        (parser.arena().plans().item_count() > 0).then_some(&fallback as &dyn Fn() -> Result<GeneralSyntax<Structure>>),
        |tctx, env, syntax| {
            tctx.experimental_let_unwrap = experimental_let_unwrap;
            type_structure(tctx, env, syntax.arena, syntax.tree)
        },
        |type_ctx, mut tctx, typed, syntax, attempt_output| {
    let UnitSyntax { arena, .. } = syntax;
    let ((typed_structure, final_env), env) = match typed {
        Ok(result) => result,
        Err(e) => {
            // OCaml compiler/ext/misc.ml:337-392: `Color.color_enabled`
            // starts as `true` and takes the configured `-color` value at
            // the first `Location.setup_colors` (location.ml:45-47), which
            // printing a warning triggers. Messages formatted afterwards
            // only carry style escapes when colors are enabled.
            tctx.drain_open_slot_uses();
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            attempt_output.warnings(arena, source, filename, &tctx.warnings);
            if let Some(error) = tctx
                .persistent_env
                .as_ref()
                .and_then(|persistent_env| persistent_env.last_error())
            {
                return Err(persistent_env_error_to_anyhow(error, filename));
            }
            return Err(type_mod_error_to_anyhow(
                e,
                type_ctx,
                arena,
                source,
                filename,
                suppress_info_style,
            ));
        }
    };
    if let Some(error) = tctx
        .persistent_env
        .as_ref()
        .and_then(|persistent_env| persistent_env.last_error())
    {
        return Err(persistent_env_error_to_anyhow(error, filename));
    }
    tctx.drain_open_slot_uses();
    attempt_output.warnings(arena, source, filename, &tctx.warnings);
    // js_implementation.ml:158-163: `Warnings.check_fatal` runs only after
    // `Typemod.type_implementation_more`, whose delayed checks
    // (typemod.ml:1769-1776) still report their warnings.
    let early_warnings_have_errors =
        ppx_warnings_have_errors || type_warnings_have_errors(&tctx.warnings);
    let delayed_type_warning_start = tctx.warnings.len();

    let source_file_for_interface = options.source_filename.as_deref().unwrap_or(filename);
    let has_resi = source_file_for_interface.ends_with(".res")
        && source_has_interface(options, source_file_for_interface);
    if options.assume_compiled_interface
        && source_file_for_interface.ends_with(".res")
        && !compiled_interface_file_exists(options, source_file_for_interface)
    {
        let intf_name = interface_source_name(source_file_for_interface);
        return Err(UserDiagnostic::new(
            format_interface_not_compiled_report(source, filename, parser.filename(), &intf_name),
            2,
        )
        .into());
    }

    // Apply interface constraints: moregen linking for non-generic Tvars.
    // OCaml's Includemod.compunit -> moregeneral -> moregen links weak (non-generic)
    // type variables from value-restricted expressions to the corresponding types
    // from the .resi interface. This happens BEFORE sexp serialization.
    apply_moregen_constraints(&mut tctx, type_ctx, &typed_structure, options, has_resi);
    if has_resi {
        check_compunit_inclusion_for_errors(
            &mut tctx,
            &env,
            &typed_structure,
            source_file_for_interface,
            &|| source.to_string(),
            filename,
            current_unit_name.as_deref(),
        )?;
    }

    // OCaml compiler/ml/typemod.ml:1755-1758 reads the compiled interface
    // through Env.read_signature; persistent Env errors raised there abort
    // implementation typing before warnings are reported as success.
    if let Some(error) = tctx
        .persistent_env
        .as_ref()
        .and_then(|persistent_env| persistent_env.last_error())
    {
        return Err(persistent_env_error_to_anyhow(error, filename));
    }

    // OCaml's no-interface path runs inferred-signature inclusion before
    // checking non-generalizable schemes and normalizing the signature
    // (compiler/ml/typemod.ml:1766-1771). It yields the export coercion and
    // marks the unit's items as used.
    let (inferred_simple_signature, inferred_implementation_coercion) = if !has_resi {
        let simple_signature =
            crate::types::includemod::simplify_signature(&typed_structure.str_type);
        // typemod.ml `type_implementation_more`: `check_js_names ~toplevel:true
        // simple_sg` before the inferred-signature inclusion.
        if let Err(e) = crate::types::typemod::check_js_names(type_ctx, true, &simple_signature) {
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            return Err(type_mod_error_to_anyhow(
                e,
                type_ctx,
                arena,
                source,
                filename,
                suppress_info_style,
            ));
        }
        let implementation_coercion = coerce_to_inferred_signature(
            type_ctx,
            &env,
            source_file_for_interface,
            &typed_structure.str_type,
            &simple_signature,
        );
        // A payload reader's error escapes the inclusion (includecore.ml:45).
        let implementation_coercion =
            match crate::types::includemod::escaped(type_ctx, implementation_coercion) {
                Ok(coercion) => coercion,
                Err(e) => {
                    attempt_output.warnings(arena, source, filename, &tctx.warnings);
                    return Err(type_mod_error_to_anyhow(
                        e.into(),
                        type_ctx,
                        arena,
                        source,
                        filename,
                        !tctx.warnings.is_empty()
                            && !crate::parser::code_frame::should_enable_color(),
                    ));
                }
            }
            .map_err(|e| anyhow!("Inferred signature inclusion failed: {e:?}"))?;
        if let Err(e) =
            crate::types::typemod::check_nongen_schemes(type_ctx, &final_env, &simple_signature)
        {
            // The warnings printed so far have set up colors (misc.ml:337-392).
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            return Err(type_mod_error_to_anyhow(
                e,
                type_ctx,
                arena,
                source,
                filename,
                suppress_info_style,
            ));
        }
        normalize_signature(type_ctx, &final_env, &simple_signature);
        (Some(simple_signature), Some(implementation_coercion))
    } else {
        (None, None)
    };

    // OCaml compiler/ml/typemod.ml:1769-1776 forces delayed checks before
    // compiler/core/js_implementation.ml:148-156 prints `-dtyped-sexp`; Rust
    // typedtree-only runs must therefore flush value-usage checks before the dump.
    tctx.flush_value_usage_checks();
    let delayed_warnings = &tctx.warnings[delayed_type_warning_start..];
    attempt_output.warnings(arena, source, filename, delayed_warnings);
    // `Warnings.check_fatal` only runs at lam_compile_main.ml:420 (or right
    // after typing for typedtree/cmi-only runs, js_implementation.ml:158-159),
    // so a fatal typing warning still lets Translmod report its warnings.
    let typing_warnings_fatal =
        early_warnings_have_errors || type_warnings_have_errors(delayed_warnings);
    let post_type_warning_start = tctx.warnings.len();

    // Print typed tree if requested
    if options.dump_typed_sexp {
        let stderr = &mut attempt_output.stderr;
        let _ = print_typed_structure(
            arena,
            type_ctx,
            &tctx.typed,
            &typed_structure,
            stderr,
        );
    }
    if options.dump_typed_sexp_locs {
        let stderr = &mut attempt_output.stderr;
        let _ = print_typed_structure_with_locs(
            arena,
            type_ctx,
            &tctx.typed,
            &typed_structure,
            stderr,
        );
    }

    // `Env.save_signature` renames the bound identifiers of a copy of the
    // inferred signature (env.ml:1886-1892), taking stamps; no file is written.
    if let Some(simple_signature) = inferred_simple_signature.as_deref()
        && !has_resi
    {
        saved_signature_copy(type_ctx, simple_signature);
    }

    // `process_with_gentype` runs after the JS is emitted
    // (js_implementation.ml:164), which a fatal warning prevents.
    let pending_gentype = if options.gentype_config.is_some() && !typing_warnings_fatal {
        let module_name = current_unit_name
            .clone()
            .unwrap_or_else(|| module_name_from_source_filename(source_file_for_interface));
        if !has_resi && let Some(simple_signature) = inferred_simple_signature.as_deref() {
            // OCaml saves the inferred signature before GenType consumes CMT
            // data in compiler/ml/typemod.ml:1779-1788 and
            // compiler/gentype/GenTypeMain.ml:136-175. The direct Rust CLI
            // path does not write/read a CMT, so expose the same pre-finalized
            // raw signature to GenType's alias scraping path.
            let current_raw_sig =
                std::sync::Arc::new(crate::types::typecore::copy_lookup_signature_for_subst(
                    simple_signature,
                    type_ctx,
                ));
            type_ctx.register_gentype_raw_module_sig(&module_name, current_raw_sig.clone());
            type_ctx.register_raw_module_sig(&module_name, current_raw_sig);
        }
        process_gentype_typed_artifact_if_enabled(
            options,
            has_resi.then(|| interface_source_gentype_read(source_file_for_interface)),
            GentypeUnit {
                annots: crate::gentype::main::TypedArtifactAnnots::Implementation(&typed_structure),
                arena,
                ta: &tctx.typed,
                type_ctx,
                source: &|| source.to_string(),
                filename: source_file_for_interface,
                module_name: &module_name,
            },
        )
    } else { None };

    let lambda_start_stamp = synchronize_lambda_start_stamp(type_ctx);

    let unit_name = options.current_unit_name().unwrap_or_default();
    let implementation_coercion = inferred_implementation_coercion.unwrap_or_else(|| {
        compute_raw_implementation_coercion(
            &mut tctx,
            type_ctx,
            &env,
            &typed_structure,
            options,
            has_resi,
        )
    });
    let raw_arena = crate::raw_lambda::RawArena::for_typed_exprs(tctx.typed.expr_count());
    let mut raw_converter =
        crate::raw_lambda::convert::RawLambdaConverter::with_start_stamp_and_unit_name(
            arena,
            &tctx.typed,
            type_ctx,
            &env,
            lambda_start_stamp,
            unit_name,
            &raw_arena,
        );
    raw_converter.set_preserve_expanded_sparse_records(
        options.dump_lambda || options.dump_lambda_sexp || options.dump_lambda_sexp_locs,
    );
    raw_converter.set_no_assert_false(options.no_assert_false);
    raw_converter.set_noassert(options.noassert);
    raw_converter.set_warning_config(tctx.warning_config.clone());
    if let Some(persistent_env) = tctx.persistent_env.clone() {
        raw_converter.set_persistent_env(persistent_env);
    }
    let raw_lambda =
        raw_converter.convert_structure_with_coercion(&typed_structure, &implementation_coercion);
    let interface_signature = if has_resi {
        implementation_interface_signature(
            &mut tctx.persistent_env,
            type_ctx,
            source_file_for_interface,
            current_unit_name.as_deref(),
        )
    } else {
        None
    };
    let flat_make_paths = flat_make_paths_of_signature(
        &mut tctx.persistent_env,
        type_ctx,
        &final_env,
        if has_resi {
            interface_signature.as_deref().map(Vec::as_slice)
        } else {
            inferred_simple_signature.as_deref()
        },
    );
    raw_converter.set_flat_make_paths(&raw_lambda, flat_make_paths);
    let raw_warnings = raw_converter.take_warnings();
    let flat_make_paths = raw_converter.take_flat_make_paths();
    let lam_locs = raw_converter.take_lam_locs();
    if let Some(diagnostic) = raw_converter.take_diagnostic() {
        // A Translmod error escapes before `Warnings.check_fatal`.
        attempt_output.warnings(arena, source, filename, &raw_warnings);
        return Err(UserDiagnostic::new(
            format_compiler_error_report_from_location(
                source,
                filename,
                &diagnostic.loc,
                &diagnostic.message,
            ),
            2,
        )
        .into());
    }
    let late_type_warnings = &tctx.warnings[post_type_warning_start..];
    attempt_output.warnings(arena, source, filename, late_type_warnings);
    attempt_output.warnings(arena, source, filename, &raw_warnings);
    // lam_compile_main.ml:420 `Warnings.check_fatal ()` runs after the
    // lambda and JS passes (checked below, after `lam_compile`).
    let warnings_fatal = typing_warnings_fatal
        || type_warnings_have_errors(late_type_warnings)
        || type_warnings_have_errors(&raw_warnings);
    let possible_required_modules = raw_converter.take_possible_required_modules();
    #[cfg(test)]
    if let Some(trace) = discriminator_trace.as_deref_mut() {
        trace.type_context_stamp = type_ctx.current_stamp();
        trace.raw_converter_stamp = raw_converter.current_stamp();
        trace.raw_max_stamp =
            crate::raw_lambda::lower::max_ident_stamp_for_test(&raw_arena.get(), raw_lambda);
        trace.raw_lambda =
            crate::raw_lambda::print::RawLambdaPrinter::new(&raw_arena.get(), raw_lambda)
                .to_string();
    }

    // This attempt can still fail during lowering: release its checker borrows
    // normally rather than leaking the discarded graph on the CLI fast path.
    drop(raw_converter);
    let (mut lowered_arena, lowered_root, export_idents) =
        crate::raw_lambda::lower::lower_to_translmod_lambda(raw_arena.into_inner(), raw_lambda);
    // js_implementation.ml:165 prints `-drawlambda` on Translmod's result.
    if options.dump_lambda {
        use std::io::Write;
        let mut buf = Vec::new();
        crate::lambda::printlambda::print_lambda(&lowered_arena.export(lowered_root), &mut buf);
        buf.push(b'\n');
        let stderr = &mut attempt_output.stderr;
        let _ = stderr.write_all(&buf);

        if std::env::var_os("RUST_RAWLAMBDA_ONLY").is_some() {
            attempt_output.publish(type_ctx)?;
            std::process::exit(0);
        }
    }
    // lam_compile_main.ml:288-290: the first pass of Lam_compile_main.compile.
    let lowered_root = crate::lambda::lam_pass_collapse_var_aliases::collapse(
        &mut lowered_arena,
        lowered_root,
        &export_idents,
    );

    if options.backend != crate::bir::shadow::BackendMode::Legacy {
        crate::bir::shadow::check_lambda(&lowered_arena, lowered_root, filename)?;
        crate::bir::shadow::check_norm(&lowered_arena, raw_lambda, filename)?;
    }

    #[cfg(test)]
    if let Some(trace) = discriminator_trace.as_deref_mut() {
        trace.lowered_lambda = format!("{:#?}", lowered_arena.export(lowered_root));
    }

    if options.dump_lambda_sexp || options.dump_lambda_sexp_locs {
        let lowered_lambda = lowered_arena.export(lowered_root);
        if options.dump_lambda_sexp {
            let stderr = &mut attempt_output.stderr;
            let _ = crate::lambda::sexp_lambda::print_lambda(&lowered_lambda, stderr);

        }
        if options.dump_lambda_sexp_locs {
            let stderr = &mut attempt_output.stderr;
            let _ =
                crate::lambda::sexp_lambda::print_lambda_with_locs(&lowered_lambda, stderr);

        }
    }

    // Lambda -> JS IR
    let mut module_path_resolver = ModulePathResolver::from_compile_options(
        options.source_filename.as_deref(),
        options.output_path.as_deref(),
        options.output_module_format,
        options.package_name.as_deref(),
        options.runtime_path.as_deref(),
        tctx.persistent_env.clone(),
        options.make_runtime,
    );
    module_path_resolver.set_package_specs(&options.js_package_specs);
    for module in &possible_required_modules {
        if matches!(module.kind, Kind::Ml) && !module.dynamic_import {
            if let Some(path) =
                module_path_resolver.resolve_local_module_fallback_path(module.id.name())
            {
                module_path_resolver.set_module_path_override(module.id.name(), path);
            }
        }
    }
    let mut compiler = LambdaCompiler::with_module_path_resolver_and_options(
        Some(module_path_resolver),
        options.jsx_preserve,
        options.check_div_by_zero,
        options.cross_module_inline,
    );
    compiler.set_source_map_enabled(
        options.source_map != crate::js_ir::source_map::SourceMapMode::None,
    );
    compiler.set_flat_make_paths(flat_make_paths);
    compiler.set_lam_locs(lam_locs);
    if options.backend == crate::bir::shadow::BackendMode::Check {
        compiler.set_shadow_unit(filename);
    }
    let mut all_possible_required_modules =
        crate::lambda::lam_compile::collect_possible_required_modules_in_arena(
            &lowered_arena,
            lowered_root,
        );
    all_possible_required_modules.extend(possible_required_modules.iter().cloned());
    let program = compile_with_lower_check(
        &mut compiler, lowered_arena, lowered_root,
        all_possible_required_modules, options, options.jsx_preserve, filename,
    )?;
    #[cfg(test)]
    if let Some(trace) = discriminator_trace.as_deref_mut() {
        trace.js_program = format!("{program:#?}");
    }
    if let Some(error) = compiler.take_shadow_error() {
        return Err(error);
    }
    if let Some(diagnostic) = compiler.take_diagnostic() {
        // A location-free compilation has no range to report: recompile
        // with locations instead of printing a zero range.
        let Some(diagnostic_loc) = diagnostic.loc else {
            return Err(LocationRetry::Diagnostic.into());
        };
        return Err(UserDiagnostic::new(
            format_compiler_error_report_from_location(
                source,
                filename,
                &diagnostic_loc,
                &diagnostic.message,
            ),
            2,
        )
        .into());
    }
    // lam_compile_main.ml:420 `Warnings.check_fatal ()`.
    if warnings_fatal {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }
    let module_path_resolver = compiler
        .take_module_path_resolver()
        .expect("lambda compiler retained module path resolver");
    check_module_path_resolution_errors(&program, &module_path_resolver, filename)?;

    if options.backend != crate::bir::shadow::BackendMode::Legacy {
        crate::bir::shadow::check_js(
            &program, &module_path_resolver, &file_directives, options.debug,
            options.jsx_preserve, !options.no_version_header, filename,
        )?;
    }

    // JS IR -> JS source. File-based compilation writes the companion map
    // here because its public return value remains the generated JS string;
    // in-process compilation carries the map on `JsOutput` instead.
    let (js, source_map) = render_js_program(
        &program,
        &module_path_resolver,
        JsFileSettings {
            file_directives: &file_directives,
            debug: options.debug,
            jsx_preserve: options.jsx_preserve,
        },
        options,
        options.output_path.as_deref(),
        std::sync::Arc::new(compiler.take_lam_locs()),
    );
    attempt_output.publish(type_ctx)?;
    print!("{}", apply_gentype_outcome(pending_gentype, "", source_file_for_interface)?);
    if let Some(output_path) = options.output_path.as_deref() {
        let map_path = PathBuf::from(format!("{}.map", output_path.display()));
        if let Some(source_map) = source_map {
            if let Some(parent) = map_path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(map_path, source_map)?;
        } else {
            let _ = std::fs::remove_file(map_path);
        }
    }

    // The CLI compiler is a short-lived process. Skipping teardown for the
    // large typechecking arenas keeps snapshot runs inside the harness timeout
    // once output has already been produced.
    if SKIP_CLI_CLEANUP.load(Ordering::Relaxed) {
        std::mem::forget(compiler);
        std::mem::forget(program);
        std::mem::forget(implementation_coercion);
        std::mem::forget(typed_structure);
        std::mem::forget(final_env);
        std::mem::forget(env);
        std::mem::forget(tctx);
    }

    Ok(js)
        },
    );
    if result.is_ok() && SKIP_CLI_CLEANUP.load(Ordering::Relaxed) {
        std::mem::forget(type_ctx);
        std::mem::forget(structure);
        std::mem::forget(parser);
    }
    result
}

/// Build a structural module coercion by matching interface items to implementation
/// positions by name, without type-checking. Used as a fallback when `compunit`
/// fails due to type representation differences (e.g., OCaml CMI stamps vs Rust stamps).
///
/// This matches OCaml's `Tcoerce_structure` behavior: for each runtime component
/// in the interface signature, find its runtime position in the implementation
/// signature and emit a `(pos, Tcoerce_none)` entry. Items in the implementation
/// that don't appear in the interface are excluded from the export block.
fn build_name_based_coercion(
    impl_sig: &crate::types::decl::Signature,
    intf_sig: &crate::types::decl::Signature,
) -> crate::types::typedtree::ModuleCoercion {
    use crate::types::decl::{AliasPresence, ModuleType, SignatureItem, ValueKind};
    use crate::types::includemod::is_runtime_component;
    use crate::types::typedtree::{EnvRef, ModuleCoercion, PrimitiveCoercion};

    fn module_type_coercion(impl_mty: &ModuleType, intf_mty: &ModuleType) -> ModuleCoercion {
        match (impl_mty, intf_mty) {
            (
                ModuleType::MtyAlias(pres_impl, impl_path),
                ModuleType::MtyAlias(pres_sig, intf_path),
            ) => {
                // OCaml `try_modtypes` first compares normalized alias paths,
                // then only emits `Tcoerce_alias` for absent implementation
                // aliases matched against present interface aliases
                // (compiler/ml/includemod.ml:209-228). Same absent aliases are
                // runtime-empty on both sides, so the fallback must keep them
                // identity instead of materializing the target module.
                if impl_path.same(intf_path)
                    && matches!(pres_impl, AliasPresence::MtaAbsent)
                    && matches!(pres_sig, AliasPresence::MtaPresent)
                {
                    ModuleCoercion::Tcoerce_alias(
                        EnvRef(0),
                        **impl_path,
                        Box::new(ModuleCoercion::Tcoerce_none),
                    )
                } else {
                    ModuleCoercion::Tcoerce_none
                }
            }
            (ModuleType::MtyAlias(AliasPresence::MtaAbsent, impl_path), _) => {
                // OCaml wraps an absent implementation alias when the
                // interface expects an expanded module type
                // (compiler/ml/includemod.ml:230-241). This name-based
                // fallback cannot safely expand the target after the real
                // inclusion check failed, so preserve the existing alias
                // coercion at the same boundary.
                ModuleCoercion::Tcoerce_alias(
                    EnvRef(0),
                    **impl_path,
                    Box::new(ModuleCoercion::Tcoerce_none),
                )
            }
            (ModuleType::MtySignature(impl_sig), ModuleType::MtySignature(intf_sig)) => {
                // OCaml recurses into submodule signatures when building
                // structural coercions (compiler/ml/includemod.ml:253-292,
                // 329-342), so an interface can hide fields inside an exported
                // module without leaking the implementation block shape.
                build_name_based_coercion(impl_sig, intf_sig)
            }
            (
                ModuleType::MtyFunctor {
                    result: impl_result,
                    ..
                },
                ModuleType::MtyFunctor {
                    result: intf_result,
                    ..
                },
            ) => {
                let result = module_type_coercion(impl_result, intf_result);
                if matches!(result, ModuleCoercion::Tcoerce_none) {
                    ModuleCoercion::Tcoerce_none
                } else {
                    // OCaml represents functor inclusion as a result coercion
                    // over the applied body (compiler/ml/includemod.ml:144-166;
                    // compiler/ml/translmod.ml:160-168). This fallback is used
                    // only after the real inclusion check failed, so keep the
                    // argument side identity and preserve the observable result
                    // export shape.
                    ModuleCoercion::Tcoerce_functor(
                        Box::new(ModuleCoercion::Tcoerce_none),
                        Box::new(result),
                    )
                }
            }
            _ => ModuleCoercion::Tcoerce_none,
        }
    }

    // Build name → runtime_position map from the implementation signature.
    // OCaml indexes every implementation component with the current runtime
    // position, then advances only for runtime components. That lets primitive
    // implementations satisfy regular interface values via Tcoerce_primitive.
    // See compiler/ml/includemod.ml:313-342 and 381-390.
    let mut impl_name_to_component: ahash::AHashMap<&str, (usize, &SignatureItem)> =
        ahash::AHashMap::new();
    let mut runtime_pos = 0usize;
    for item in impl_sig {
        match item {
            SignatureItem::SigValue(id, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigTypext(id, _, _) => {
                impl_name_to_component.insert(id.name(), (runtime_pos, item));
            }
            _ => {}
        }
        if is_runtime_component(item) {
            runtime_pos += 1;
        }
    }
    let len_impl = runtime_pos;

    // Build coercions and runtime_fields from the interface signature.
    // For each runtime component in the interface, look up its position in the impl.
    let mut coercions: Vec<(usize, ModuleCoercion)> = Vec::new();
    let mut runtime_fields: Vec<String> = Vec::new();

    for item in intf_sig {
        if !is_runtime_component(item) {
            continue;
        }
        let name = match item {
            SignatureItem::SigValue(id, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigTypext(id, _, _) => id.name(),
            _ => continue,
        };
        if let Some(&(pos, impl_item)) = impl_name_to_component.get(name) {
            let coercion = match (item, impl_item) {
                (
                    SignatureItem::SigValue(_, sig_desc),
                    SignatureItem::SigValue(impl_id, impl_desc),
                ) if !matches!(sig_desc.val_kind, ValueKind::ValPrim(_)) => {
                    match &impl_desc.val_kind {
                        ValueKind::ValPrim(prim) => {
                            // Mirrors compiler/ml/includecore.ml:52-63:
                            // Val_prim implementation + regular interface
                            // value is exported by a primitive coercion.
                            ModuleCoercion::Tcoerce_primitive(PrimitiveCoercion {
                                pc_desc: (**prim).clone(),
                                pc_type: sig_desc.val_type,
                                pc_loc: impl_desc.val_loc,
                                pc_id: *impl_id,
                            })
                        }
                        ValueKind::ValReg => ModuleCoercion::Tcoerce_none,
                    }
                }
                (
                    SignatureItem::SigModule(_, sig_md, _),
                    SignatureItem::SigModule(_, impl_md, _),
                ) => module_type_coercion(&impl_md.md_type, &sig_md.md_type),
                _ => ModuleCoercion::Tcoerce_none,
            };
            coercions.push((pos, coercion));
            runtime_fields.push(name.to_string());
        }
    }

    let len_sig = coercions.len();

    // Check if this is already an identity coercion (same items in same order)
    let is_identity = len_impl == len_sig
        && coercions
            .iter()
            .enumerate()
            .all(|(expected_pos, (actual_pos, coercion))| {
                *actual_pos == expected_pos && matches!(coercion, ModuleCoercion::Tcoerce_none)
            });

    if is_identity {
        ModuleCoercion::Tcoerce_none
    } else {
        ModuleCoercion::Tcoerce_structure(coercions, Vec::new(), runtime_fields)
    }
}

fn report_compunit_inclusion_warnings(
    tctx: &mut TypeCheckContext<'_>,
    warnings: Vec<crate::diagnostics::Warning>,
) {
    let loc = tctx.arena.none_loc();
    for warning in warnings {
        tctx.report_warning(loc, warning);
    }
}

fn direct_compunit_error_location(
    error: &crate::types::includemod::IncludeModError,
) -> Option<crate::types::DeclLoc> {
    use crate::types::includemod::IncludeModError;

    match error {
        IncludeModError::ValueTypeMismatch { actual, .. } => Some(actual.val_loc),
        IncludeModError::TypeDeclarationMismatch { actual, .. } => Some(actual.type_loc),
        IncludeModError::MissingField { loc, .. } => Some(*loc),
        IncludeModError::SignatureMismatch(errors) if errors.len() == 1 => {
            direct_compunit_error_location(&errors[0])
        }
        _ => None,
    }
}

fn format_compiler_error_report_raw_message_from_location(
    source: &str,
    filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header_from_location(&mut output, source, filename, loc);
    output.push_str(message);
    if !message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_compunit_mismatch_report(
    type_ctx: &TypeContext,
    source: &str,
    filename: &str,
    impl_name: &str,
    intf_name: &str,
    error: &crate::types::includemod::IncludeModError,
) -> String {
    let file_loc = Location::in_file(StrIdx::default());
    let loc =
        &direct_compunit_error_location(error).map_or(file_loc, |loc| type_ctx.resolve_loc(loc));
    let message = crate::types::includemod::format_report(
        type_ctx,
        filename,
        error,
        crate::types::includemod::ReportHeading::Interface {
            impl_name,
            intf_name,
        },
    );
    // The report is located where the error is (location.ml prints
    // `loc.loc_start.pos_fname`), e.g. at a value only the interface declares.
    let loc_file = crate::types::includemod::location_filename(type_ctx, filename, loc);
    if loc_file != filename
        && let Ok(bytes) = std::fs::read(&loc_file)
    {
        let loc_source = crate::source_text::latin1_bytes_to_string(bytes);
        return format_compiler_error_report_raw_message_from_location(
            &loc_source,
            &loc_file,
            loc,
            &message,
        );
    }
    format_compiler_error_report_raw_message_from_location(source, filename, loc, &message)
}

/// The result of checking an implementation against its interface: OCaml's
/// one `Includemod.compunit` call gives both the coercion Translmod uses and
/// the inclusion warnings (typemod.ml:1742-1758).
struct CompunitInclusion {
    coercion: crate::types::typedtree::ModuleCoercion,
    warnings: Vec<crate::diagnostics::Warning>,
}

#[allow(clippy::too_many_arguments)]
/// The coercion of an implementation without an interface to its inferred
/// signature `simple_signature` (compiler/ml/typemod.ml:1766-1768).
fn coerce_to_inferred_signature(
    type_ctx: &TypeContext,
    env: &Env,
    source_file: &str,
    signature: &crate::types::decl::Signature,
    simple_signature: &crate::types::decl::Signature,
) -> crate::types::includemod::IncludeModResult<crate::types::typedtree::ModuleCoercion> {
    if let Some(coercion) = crate::types::includemod::inferred_signature_coercion(
        type_ctx,
        env,
        signature,
        simple_signature,
    ) {
        return Ok(coercion);
    }
    crate::types::includemod::compunit(
        type_ctx,
        env,
        source_file,
        signature,
        "(inferred signature)",
        simple_signature,
    )
}

/// Check an implementation that has a `.resi` against its compiled interface.
fn check_compunit_inclusion_for_errors(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    typed_structure: &crate::types::typedtree::Structure,
    source_file: &str,
    source: &dyn Fn() -> String,
    filename: &str,
    unit_name: Option<&str>,
) -> Result<Option<CompunitInclusion>> {
    if !source_file.ends_with(".res") {
        return Ok(None);
    }
    let type_ctx = tctx.type_ctx;

    // The interface is the unit being compiled: `A-Ns` in a namespaced
    // package, as OCaml's `modulename` (typemod.ml:1742-1753).
    let module_name = interface_unit_name(unit_name, source_file);
    if module_name.is_empty() {
        return Ok(None);
    }

    let Some(pers) = &mut tctx.persistent_env else {
        return Ok(None);
    };
    load_interface_unit(pers, source_file, &module_name, type_ctx);
    // In-process, the interface was saved without a `.cmi`; its raw `ps_sig`
    // travels with the registered portable structure.
    let raw_in_process_sig = if pers.is_in_process_mode() {
        type_ctx.get_gentype_raw_module_sig(&module_name)
    } else {
        None
    };
    let in_process = pers.is_in_process_mode();
    let Some(target_sig) =
        raw_in_process_sig.or_else(|| pers.read_raw_sig_shared(&module_name, type_ctx))
    else {
        // typemod.ml:1744-1751 raises `Interface_not_compiled` here. An
        // in-process build registers every compiled interface, so a missing
        // one must not silently skip the implementation-interface check.
        if in_process {
            return Err(anyhow!(
                "Could not find the compiled interface of {module_name} for {source_file}"
            ));
        }
        return Ok(None);
    };
    // Env.read_signature forces ps_sig, whose Subst.signature identity copy
    // renames every bound interface identifier before compunit inclusion
    // (compiler/ml/env.ml:1867-1869, compiler/ml/subst.ml:322-354).
    rename_saved_signature_idents(type_ctx, target_sig.as_ref());

    let mut inclusion_warnings = Vec::new();
    let inclusion = crate::types::includemod::compunit_with_warnings(
        type_ctx,
        env,
        source_file,
        &typed_structure.str_type,
        // typemod.ml: the interface is named by its source file.
        &interface_source_name(source_file),
        target_sig.as_ref(),
        &mut inclusion_warnings,
    );
    // A payload reader's error escapes the inclusion (includecore.ml:45).
    let inclusion = match crate::types::includemod::escaped(type_ctx, inclusion) {
        Ok(inclusion) => inclusion,
        Err(TypeCoreError::InvalidStringEscapeAt { loc }) => {
            return Err(invalid_string_escape_report(type_ctx, filename, &loc));
        }
        Err(_) => unreachable!("`escaped` only raises an invalid escape"),
    };
    match inclusion {
        Ok(coercion) => Ok(Some(CompunitInclusion {
            coercion,
            warnings: inclusion_warnings,
        })),
        Err(error) => Err(UserDiagnostic::new(
            format_compunit_mismatch_report(
                type_ctx,
                &source(),
                filename,
                source_file,
                &interface_source_name(source_file),
                &error,
            ),
            2,
        )
        .into()),
    }
}

/// The signature `Typemod.type_implementation_more` returns with an
/// interface (`dclsig`, read from the interface unit), for
/// `Translmod.transl_implementation`.
fn implementation_interface_signature(
    persistent_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    type_ctx: &TypeContext,
    source_file: &str,
    unit_name: Option<&str>,
) -> Option<std::sync::Arc<crate::types::decl::Signature>> {
    if !source_file.ends_with(".res") {
        return None;
    }
    let module_name = interface_unit_name(unit_name, source_file);
    if module_name.is_empty() {
        return None;
    }
    let pers = persistent_env.as_mut()?;
    let raw_in_process_sig = if pers.is_in_process_mode() {
        type_ctx.get_gentype_raw_module_sig(&module_name)
    } else {
        None
    };
    raw_in_process_sig.or_else(|| pers.read_raw_sig_shared(&module_name, type_ctx))
}

/// `Translmod.flat_make_paths final_env signature`, run after the structure
/// is translated (translmod.ml `transl_implementation`).
fn flat_make_paths_of_signature(
    persistent_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    type_ctx: &TypeContext,
    final_env: &Env,
    signature: Option<&[crate::types::decl::SignatureItem]>,
) -> Vec<crate::lambda::FlatMakePath> {
    match signature {
        Some(signature) => crate::types::typemod::flat_make_paths(
            type_ctx,
            final_env,
            persistent_env,
            signature,
        ),
        None => Vec::new(),
    }
}

/// The unit name an implementation's interface is registered under: the
/// compile's unit name when known (namespaced, `A-Ns`), else the file's.
fn interface_unit_name(unit_name: Option<&str>, source_file: &str) -> String {
    unit_name
        .filter(|name| !name.is_empty())
        .map(str::to_string)
        .unwrap_or_else(|| module_name_from_source_filename(source_file))
}

fn compute_raw_implementation_coercion(
    tctx: &mut TypeCheckContext<'_>,
    type_ctx: &TypeContext,
    env: &Env,
    typed_structure: &crate::types::typedtree::Structure,
    options: &CompilerOptions,
    has_resi: bool,
) -> crate::types::typedtree::ModuleCoercion {
    let Some(source_file) = &options.source_filename else {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    };
    if !source_file.ends_with(".res") {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    }

    let impl_sig = &typed_structure.str_type;
    if !has_resi {
        // The no-interface coercion is computed at the Typemod boundary before
        // signature normalization and passed through to Lambda translation.
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    }

    let module_name = interface_unit_name(options.current_unit_name().as_deref(), source_file);
    if module_name.is_empty() {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    }
    let Some(pers) = &mut tctx.persistent_env else {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    };
    load_interface_unit(pers, source_file, &module_name, type_ctx);
    let target_sig = match pers.read_raw_sig_shared(&module_name, type_ctx) {
        Some(sig) => sig,
        None => return crate::types::typedtree::ModuleCoercion::Tcoerce_none,
    };

    let mut inclusion_warnings = Vec::new();
    let inclusion_result = crate::types::includemod::compunit_with_warnings(
        type_ctx,
        env,
        source_file,
        impl_sig,
        "(inferred signature)",
        target_sig.as_ref(),
        &mut inclusion_warnings,
    );
    report_compunit_inclusion_warnings(tctx, inclusion_warnings);

    // If compunit fails, fall back to a name-based structural coercion that at
    // least filters the export block to the interface's exported items, so
    // functors and other implementation-only items stay out of the module
    // export block.
    inclusion_result.unwrap_or_else(|_| build_name_based_coercion(impl_sig, &target_sig))
}

/// Make the unit's own interface loadable: add the source directory to the
/// load path and load its persistent structure.
fn load_interface_unit(
    pers: &mut PersistentEnv,
    source_file: &str,
    module_name: &str,
    type_ctx: &TypeContext,
) {
    let source_dir = std::path::Path::new(source_file)
        .parent()
        .map(|d| d.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."));
    if !pers.load_path_contains(&source_dir) {
        pers.add_load_path(source_dir);
    }
    let _ = pers.find_pers_struct(module_name, type_ctx);
}

/// Output of [`run_interface_frontend`].
pub struct InterfaceFrontend {
    /// The signature after the external and builtin PPXs.
    pub signature: Signature,
    /// A frontend warning was configured as an error.
    pub warnings_fatal: bool,
    /// The file's leading `@@warning` attributes, applied again when type
    /// checking starts.
    pub frontend_warning_specs: Vec<ppx::WarningAttributeSpec>,
    /// The file's `@@config` flag overrides.
    pub file_config: FileConfigOverrides,
    /// `let?` is enabled, by the command line or `@@config`.
    pub experimental_let_unwrap: bool,
}

/// The interface counterpart of [`run_implementation_frontend`]: parser
/// warnings and `Ppx_entry.rewrite_signature`
/// (compiler/frontend/ppx_entry.ml:27-43). Warning reports go to `out`.
pub fn run_interface_frontend(
    parser: &mut Parser<'_>,
    signature: Signature,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    out: &mut String,
) -> Result<InterfaceFrontend> {
    let census_start = crate::derived_census::start(options.derived_census.is_some());
    if let Some(path) = &options.derived_census {
        parser.arena_mut().derived_census = Some(Box::new(crate::derived_census::Census::new(path, filename)));
    }
    let parser_warnings_have_errors =
        format_parser_warnings(parser, source, filename, options, out);
    if parser.has_errors() {
        return Err(parser_error_to_anyhow(parser, source, filename));
    }
    parser.arena_mut().set_builtin_spice(options.builtin_spice());
    let frontend_warnings =
        ppx::collect_leading_builtin_warning_signature_attributes(&signature, parser.arena())
            .map_err(|err| ppx_error_to_anyhow(err, parser.arena(), source, filename))?;
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_signature_attribute_specs(&signature, parser.arena())
            .map_err(|err| ppx_error_to_anyhow(err, parser.arena(), source, filename))?;
    let mut ppx_warnings_have_errors = parser_warnings_have_errors
        | format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &warning_config_for_options(options),
            &frontend_warnings,
            out,
        );
    let config_processing = validate_file_config_from_signature(
        &signature,
        parser.arena(),
        &warning_config_for_options_and_leading_attrs(options, &frontend_warning_specs),
    );
    for (warning, config) in &config_processing.warnings {
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            out,
        );
    }
    if let Some(err) = config_processing.error {
        return Err(config_payload_error_to_anyhow(
            err,
            parser.arena(),
            source,
            filename,
        ));
    }
    let file_config = config_processing.overrides;
    let file_warning_config = warning_config_for_options_file_config_and_leading_attrs(
        options,
        &file_config,
        &frontend_warning_specs,
    );
    let experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
    let mut builtin_ppx_warnings = Vec::new();
    let signature = preprocess_signature_for_typecheck_with_source(
        signature,
        options,
        &file_config,
        parser.arena_mut(),
        source,
        filename,
        &mut builtin_ppx_warnings,
    );
    ppx_warnings_have_errors |= format_ppx_warnings_with_config(
        parser.arena(),
        source,
        filename,
        &file_warning_config,
        &builtin_ppx_warnings,
        out,
    );
    let signature = signature?;
    if !file_config.no_builtin_ppx(options) {
        // OCaml `Ast_config.process_sig` + `emit_external_warnings_on_signature`.
        ppx::mark_config_attributes_signature(&signature, parser.arena());
    }
    let mut census = parser.arena_mut().derived_census.take();
    let (unused_attribute_warnings, invariant_error) =
        ppx::collect_unused_attribute_warnings_signature(&signature, parser.arena(), census.as_deref_mut(), !file_config.no_builtin_ppx(options));
    ppx_warnings_have_errors |= format_ppx_warnings_with_config(
        parser.arena(),
        source,
        filename,
        &file_warning_config,
        &unused_attribute_warnings,
        out,
    );
    if let Some(e) = invariant_error {
        return Err(ppx_error_to_anyhow(e, parser.arena(), source, filename));
    }
    parser.arena_mut().derived_census = census;
    // js_implementation.ml:36-38: the second `Ast_config.process_sig`.
    for (warning, config) in &config_processing.late_warnings {
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            out,
        );
    }
    if let Some(start) = census_start {
        let elapsed = crate::derived_census::nanos(start.elapsed());
        if let Some(mut census) = parser.arena_mut().derived_census.take() {
            census.account_frontend(elapsed);
            parser.arena_mut().derived_census = Some(census);
        }
    }
    Ok(InterfaceFrontend {
        signature,
        warnings_fatal: ppx_warnings_have_errors,
        frontend_warning_specs,
        file_config,
        experimental_let_unwrap,
    })
}

/// Parse and type check an interface source, reporting its diagnostics.
pub fn typecheck_interface_source(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<()> {
    // Parse as signature
    let mut parser = Parser::new(filename, source);
    let signature = module::parse_signature(&mut parser);
    let mut frontend_output = String::new();
    let frontend = run_interface_frontend(
        &mut parser,
        signature,
        source,
        filename,
        options,
        &mut frontend_output,
    );
    if !options.frontend_already_reported {
        write_stderr(&frontend_output);
    }
    let InterfaceFrontend {
        signature,
        warnings_fatal: ppx_warnings_have_errors,
        frontend_warning_specs,
        file_config,
        experimental_let_unwrap,
    } = frontend?;
    let effective_options = file_config.apply(options);
    let options = &*effective_options;
    let ppx_warnings_have_errors = if options.frontend_already_reported {
        report_stored_ast_config_warnings(
            first_config_attribute_of_signature(&signature, parser.arena()),
            false,
            parser.arena(),
            source,
            filename,
            options,
        )
    } else {
        ppx_warnings_have_errors
    };
    parser.arena_mut().reserve_typecheck_synthetic_capacity();

    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    let current_unit_name = options.current_unit_name();
    type_structure_two_modes(
        CheckUnit { filename, options, registry: None,
            module_name: current_unit_name.as_deref(), file_config: &file_config,
            frontend_warning_specs: &frontend_warning_specs, derived_plans: true,
            mode: crate::types::context::CheckMode::from_env() },
        // An interface has no derived item that can fall back.
        UnitSyntax::new(parser.arena(), &signature, options),
        None,
        |tctx, env, syntax| {
            tctx.experimental_let_unwrap = experimental_let_unwrap;
            transl_signature(tctx, env, syntax.arena, syntax.tree)
        },
        |type_ctx, mut tctx, typed, _, attempt_output| {
    let (typed_signature, env) = match typed {
        Ok(typed) => typed,
        Err(e) => {
            // See the implementation path above (compiler/ext/misc.ml:337-392).
            tctx.drain_open_slot_uses();
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            attempt_output.warnings(parser.arena(), source, filename, &tctx.warnings);
            if let Some(error) = tctx
                .persistent_env
                .as_ref()
                .and_then(|persistent_env| persistent_env.last_error())
            {
                return Err(persistent_env_error_to_anyhow(error, filename));
            }
            return Err(type_mod_error_to_anyhow(
                e,
                type_ctx,
                parser.arena(),
                source,
                filename,
                suppress_info_style,
            ));
        }
    };
    if let Some(error) = tctx
        .persistent_env
        .as_ref()
        .and_then(|persistent_env| persistent_env.last_error())
    {
        return Err(persistent_env_error_to_anyhow(error, filename));
    }
    // js_implementation.ml:62: `ignore (Includemod.signatures initial_env sg
    // sg)`, which marks the declarations of the interface used.
    let sig_type = crate::types::typemod::decl_signature_from_typed_signature(
        &tctx.typed,
        &typed_signature,
        parser.arena(),
        type_ctx,
    );
    // js_implementation.ml `after_parsing_sig`: `Typemod.check_js_names
    // ~toplevel:true sg` before the self-inclusion.
    if let Err(e) = crate::types::typemod::check_js_names(type_ctx, true, &sig_type) {
        let suppress_info_style =
            !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
        attempt_output.warnings(parser.arena(), source, filename, &tctx.warnings);
        return Err(type_mod_error_to_anyhow(
            e,
            type_ctx,
            parser.arena(),
            source,
            filename,
            suppress_info_style,
        ));
    }
    // js_implementation.ml:56: `ignore (Includemod.signatures initial_env sg
    // sg)` drops the coercion; a payload reader's error escapes it.
    let self_inclusion = crate::types::includemod::compunit(
        type_ctx, &env, filename, &sig_type, filename, &sig_type,
    );
    if let Err(e) = crate::types::includemod::escaped(type_ctx, self_inclusion) {
        let suppress_info_style =
            !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
        attempt_output.warnings(parser.arena(), source, filename, &tctx.warnings);
        return Err(type_mod_error_to_anyhow(
            e.into(),
            type_ctx,
            parser.arena(),
            source,
            filename,
            suppress_info_style,
        ));
    }
    // js_implementation.ml:64 `Delayed_checks.force_delayed_checks ()`.
    tctx.flush_value_usage_checks();
    attempt_output.warnings(parser.arena(), source, filename, &tctx.warnings);
    if ppx_warnings_have_errors || type_warnings_have_errors(&tctx.warnings) {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }

    // Print typed tree if requested
    if options.dump_typed_sexp {
        let stderr = &mut attempt_output.stderr;
        let _ = print_typed_signature(
            parser.arena(),
            type_ctx,
            &tctx.typed,
            &typed_signature,
            stderr,
        );
    }
    if options.dump_typed_sexp_locs {
        let stderr = &mut attempt_output.stderr;
        let _ = print_typed_signature_with_locs(
            parser.arena(),
            type_ctx,
            &tctx.typed,
            &typed_signature,
            stderr,
        );
    }

    Ok(())
        },
    ).1
}

/// Type-check an interface file and dump typed sexp if requested.
pub fn typecheck_interface_file(path: &std::path::Path, options: &CompilerOptions) -> Result<()> {
    let bytes =
        std::fs::read(path).with_context(|| format!("Failed to read {}", path.display()))?;
    let source = crate::source_text::latin1_bytes_to_string(bytes);
    let filename = path.to_string_lossy();
    typecheck_interface_source(&source, &filename, options)
}

/// Compile a file to JavaScript.
pub fn compile_file_to_js(path: &std::path::Path) -> Result<String> {
    compile_file_to_js_with_options(path, &CompilerOptions::default())
}

/// Compile a file to JavaScript with options.
pub fn compile_file_to_js_with_options(
    path: &std::path::Path,
    options: &CompilerOptions,
) -> Result<String> {
    // Read file as raw bytes, converting each byte to a char (Latin-1 encoding).
    // This matches OCaml's byte-level string handling where each byte is a character.
    // In Latin-1 mode, char offset == original byte offset, which is critical for
    // correct position tracking in the scanner.
    let bytes =
        std::fs::read(path).with_context(|| format!("Failed to read {}", path.display()))?;
    let source = crate::source_text::latin1_bytes_to_string(bytes);
    let filename = path.to_string_lossy();
    compile_source_to_js_with_options(&source, &filename, options)
}

// =====================================================================/// Build the load path from compiler options.
///
/// Matches OCaml's `res_compmisc.ml:init_path()`:
/// - Expands `-I` directories
/// - Appends `{runtime_path}/lib/rescript` as the stdlib directory (unless no_stdlib)
fn build_load_path(options: &CompilerOptions) -> Vec<PathBuf> {
    build_load_path_with_display(options).0
}

/// Load path shared by modules with the same compiler options, built once
/// per worker thread. Normalizing every include path again for each
/// in-process module allocated thousands of paths per module.
fn shared_load_path_with_display(
    options: &CompilerOptions,
) -> (std::sync::Arc<Vec<PathBuf>>, std::sync::Arc<Vec<PathBuf>>) {
    type Key = (Option<PathBuf>, Vec<PathBuf>, Option<&'static FsPath>);
    type Entry = (
        Key,
        std::sync::Arc<Vec<PathBuf>>,
        std::sync::Arc<Vec<PathBuf>>,
    );
    thread_local! {
        static CACHE: std::cell::RefCell<Vec<Entry>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }
    let cwd = crate::process_cwd::current_dir().ok();
    CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if let Some((_, paths, display)) =
            cache.iter().find(|((runtime, includes, entry_cwd), _, _)| {
                runtime == &options.runtime_path
                    && includes == &options.include_paths
                    && entry_cwd == &cwd
            })
        {
            return (paths.clone(), display.clone());
        }
        let (paths, display) = build_load_path_with_display(options);
        let (paths, display) = (std::sync::Arc::new(paths), std::sync::Arc::new(display));
        if cache.len() >= 64 {
            cache.remove(0);
        }
        cache.push((
            (
                options.runtime_path.clone(),
                options.include_paths.clone(),
                cwd,
            ),
            paths.clone(),
            display.clone(),
        ));
        (paths, display)
    })
}

fn build_load_path_with_display(options: &CompilerOptions) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let stdlib_dir = options
        .runtime_path
        .as_ref()
        .map(|runtime_path| runtime_path.join("lib").join("rescript"));
    let cwd = crate::process_cwd::current_dir().ok();

    let mut paths = Vec::new();
    let mut display_paths = Vec::new();

    for path in &options.include_paths {
        paths.push(normalize_load_path_entry(path, stdlib_dir.as_deref(), cwd));
        display_paths.push(display_load_path_entry(path, stdlib_dir.as_deref(), cwd));
    }

    if let Some(stdlib_dir) = stdlib_dir {
        paths.push(normalize_load_path_entry(&stdlib_dir, None, cwd));
        display_paths.push(stdlib_dir);
    }

    (paths, display_paths)
}

fn display_load_path_entry(
    path: &FsPath,
    stdlib_dir: Option<&FsPath>,
    cwd: Option<&FsPath>,
) -> PathBuf {
    if let Some(raw) = path.to_str()
        && raw.starts_with('+')
    {
        return normalize_load_path_entry(path, stdlib_dir, cwd);
    }

    path.to_path_buf()
}

fn normalize_load_path_entry(
    path: &FsPath,
    stdlib_dir: Option<&FsPath>,
    cwd: Option<&FsPath>,
) -> PathBuf {
    if let Some(raw) = path.to_str() {
        if let Some(rest) = raw.strip_prefix('+') {
            if let Some(stdlib_dir) = stdlib_dir {
                return normalize_lexical_path(stdlib_dir.join(rest));
            }
        }
    }

    if path.is_absolute() {
        return normalize_lexical_path(path.to_path_buf());
    }

    match cwd {
        Some(cwd) => normalize_lexical_path(cwd.join(path)),
        None => normalize_lexical_path(path.to_path_buf()),
    }
}

fn normalize_lexical_path(path: PathBuf) -> PathBuf {
    let mut prefix: Option<OsString> = None;
    let mut has_root = false;
    let mut parts: Vec<OsString> = Vec::new();

    for component in path.components() {
        match component {
            Component::Prefix(value) => prefix = Some(value.as_os_str().to_os_string()),
            Component::RootDir => has_root = true,
            Component::CurDir => {}
            Component::ParentDir => match parts.last() {
                Some(last) if last != ".." => {
                    parts.pop();
                }
                _ if !has_root && prefix.is_none() => parts.push(OsString::from("..")),
                _ => {}
            },
            Component::Normal(part) => parts.push(part.to_os_string()),
        }
    }

    let mut normalized = PathBuf::new();
    if let Some(prefix) = prefix {
        normalized.push(prefix);
    }
    if has_root {
        normalized.push(std::path::MAIN_SEPARATOR.to_string());
    }
    for part in parts {
        normalized.push(part);
    }

    if normalized.as_os_str().is_empty() && !has_root {
        PathBuf::from(".")
    } else {
        normalized
    }
}

/// Build the initial environment of a compile: the predefined types, the
/// implicit Pervasives and Stdlib opens and the explicit `-open` modules.
///
/// This is OCaml's `Res_compmisc.initial_env` (compiler/core/res_compmisc.ml:48-66).
/// It reads modules through `tctx`'s persistent environment, which must be set.
///
/// When `nopervasives` is true (matching OCaml's `-nopervasives` flag), the
/// implicit Pervasives and Stdlib opens are skipped. This is used by
/// `@rescript/runtime` modules which bootstrap Pervasives themselves.
///
/// The `-open` modules are opened in argument order. When `compiling_module`
/// is `Some(name)`, an `-open` of that module is skipped to prevent circular
/// self-loading (OCaml filters `modulename` from `open_modules`). A module
/// that cannot be found stops the compile with an error located at "command
/// line", as in OCaml.
pub fn initial_type_env(
    tctx: &mut TypeCheckContext<'_>,
    open_modules: &[String],
    nopervasives: bool,
    compiling_module: Option<&str>,
) -> crate::types::typemod::TypeModResult<Env> {
    let ctx = tctx.type_ctx;
    let mut env = initial_env(ctx);
    if !nopervasives && let Some(pers_env) = tctx.persistent_env.as_mut() {
        for name in ["Pervasives", "Stdlib"] {
            if pers_env.open_module(
                name,
                crate::types::Path::pident(crate::ident::Ident::create_persistent(name)),
                &mut env,
                ctx,
                None,
            ) {
                env.mark_implicit_open_root(name);
                // OCaml `Res_compmisc.initial_env` opens implicit modules
                // through `type_open` (compiler/core/res_compmisc.ml:48-63). In
                // in-process and standalone builds alike, that reaches
                // Env.open_signature at compiler/ml/env.ml:1874-1877, which
                // adds opened components but not a root module binding. Keep
                // the raw signature registered for ps_comps-style descriptor
                // lookup without changing source module lookup shape.
                pers_env.register_opened_raw_sig(ctx, name);
            }
        }
    }
    for module_name in open_modules {
        if compiling_module == Some(module_name.as_str()) {
            continue;
        }
        crate::types::typemod::type_command_line_open(tctx, &mut env, module_name)?;
    }
    Ok(env)
}

use crate::types::env::Env;

/// Apply moregen-like interface constraints: link non-generic Tvars in the
/// implementation to corresponding types from the .resi interface.
///
/// This matches OCaml's Includemod.compunit -> moregeneral -> moregen mechanism.
/// OCaml runs this after type_structure but before sexp serialization. The key
/// insight is that value-restricted expressions (like `basicComponent("interop")`)
/// produce non-generic Tvars that `instance()` returns by identity. When moregen
/// links these shared Tvars to interface types, ALL references update.
fn apply_moregen_constraints(
    tctx: &mut TypeCheckContext<'_>,
    type_ctx: &TypeContext,
    typed_structure: &crate::types::typedtree::Structure,
    options: &CompilerOptions,
    has_resi: bool,
) {
    use crate::types::decl::SignatureItem;
    use crate::types::type_expr::TypeExprRef;

    let source_file = match &options.source_filename {
        Some(f) => f,
        None => return,
    };

    // Only apply when a .resi file exists
    if !source_file.ends_with(".res") {
        return;
    }
    if !has_resi {
        return;
    }

    let module_name = interface_unit_name(options.current_unit_name().as_deref(), source_file);
    if module_name.is_empty() {
        return;
    }

    // Load the RAW interface signature from CMI (without path substitution).
    // OCaml's ps_sig retains raw Pident paths; path substitution happens lazily
    // in components_of_module_maker, not on the sig used for moregen.
    // Using raw paths ensures moregen_link propagates Pident (local) paths
    // instead of Pdot (module-qualified) paths to the implementation.
    let iface_sig = {
        let pers = match &mut tctx.persistent_env {
            Some(p) => p,
            None => return,
        };
        // Ensure the module is loaded first (for side effects like registering types)
        load_interface_unit(pers, source_file, &module_name, type_ctx);
        // Then read raw sig without path substitution for moregen
        let result = pers.read_raw_sig_shared(&module_name, type_ctx);
        match result {
            Some(sig) => sig,
            None => return,
        }
    };

    // Rewrite CMI interface type paths to use implementation idents.
    // OCaml does this in Includemod.signatures → pair_components which builds
    // a Subst mapping id2→Pident(id1) for each paired Sig_type/Sig_module, then
    // applies it via Subst.type_expr during type comparisons.
    // We apply the same remapping up front: for each type in the interface sig,
    // find the corresponding implementation type by name and remap the CMI
    // stamp to the implementation's Pident path in all type_exprs.
    {
        let impl_sig = &typed_structure.str_type;
        let mut stamp_remap: ahash::AHashMap<i32, crate::types::Path> = ahash::AHashMap::new();
        // Match OCaml pair_components: remap Sig_type, Sig_module, Sig_modtype.
        // The first implementation item of each kind and name wins.
        #[derive(PartialEq, Eq, Hash)]
        enum PairKind {
            Type,
            Module,
            Modtype,
        }
        fn pair_key(item: &SignatureItem) -> Option<(PairKind, &crate::ident::Ident)> {
            match item {
                SignatureItem::SigType(id, _, _) => Some((PairKind::Type, id)),
                SignatureItem::SigModule(id, _, _) => Some((PairKind::Module, id)),
                SignatureItem::SigModtype(id, _) => Some((PairKind::Modtype, id)),
                _ => None,
            }
        }
        let mut impl_items: ahash::AHashMap<(PairKind, &str), &crate::ident::Ident> =
            ahash::AHashMap::new();
        for item in impl_sig.iter() {
            if let Some((kind, id)) = pair_key(item) {
                impl_items.entry((kind, id.name())).or_insert(id);
            }
        }
        for iface_item in iface_sig.iter() {
            let Some((kind, iface_id)) = pair_key(iface_item) else {
                continue;
            };
            if let Some(&impl_id) = impl_items.get(&(kind, iface_id.name())) {
                if iface_id.stamp() != 0
                    && impl_id.stamp() != 0
                    && iface_id.stamp() != impl_id.stamp()
                {
                    stamp_remap.insert(iface_id.stamp(), crate::types::Path::pident(*impl_id));
                }
            }
        }
        if !stamp_remap.is_empty() {
            // Apply stamp remapping to interface type_exprs
            crate::cmi::persistent_env::substitute_type_paths_in_sig_with_stamp_map(
                iface_sig.as_ref(),
                &stamp_remap,
                type_ctx,
            );
        }
    }

    // Build a map from value name -> interface type
    let mut iface_val_types: ahash::AHashMap<String, TypeExprRef> = ahash::AHashMap::new();
    for item in iface_sig.iter() {
        if let SignatureItem::SigValue(id, vd) = item {
            iface_val_types.insert(id.name().to_string(), vd.val_type);
        }
    }

    // Walk top-level implementation structure items and match with interface.
    // Also recurse into modules to find inner non-generic Tvars.
    moregen_link_structure(type_ctx, &tctx.typed, typed_structure, &iface_val_types);
}

fn moregen_link_structure(
    type_ctx: &TypeContext,
    ta: &crate::types::typedtree::TypedArena,
    structure: &crate::types::typedtree::Structure,
    iface_val_types: &ahash::AHashMap<String, crate::types::type_expr::TypeExprRef>,
) {
    for item in ta.structure_items(structure.str_items) {
        match &item.str_desc {
            crate::types::typedtree::StructureItemDesc::Tstr_value(_, bindings) => {
                for binding in ta.value_bindings(*bindings) {
                    let Some(name) = extract_pat_name(ta.pattern(binding.vb_pat)) else {
                        continue;
                    };
                    let Some(&iface_ty) = iface_val_types.get(&name) else {
                        continue;
                    };
                    let iface_inst = crate::types::ctype::instance(type_ctx, iface_ty);
                    moregen_link(
                        type_ctx,
                        ta.pattern(binding.vb_pat).pat_type,
                        iface_inst,
                        &mut ahash::AHashSet::new(),
                    );
                    let vb_expr = ta.expr(binding.vb_expr);
                    if let crate::types::typedtree::ExpressionDesc::Texp_ident(_, _, desc) =
                        &vb_expr.exp_desc
                    {
                        // OCaml Ctype.moregeneral instantiates generic variables on
                        // copies before comparison (compiler/ml/ctype.ml:3124-3139).
                        // Only non-generic variables are shared with the original
                        // typedtree and can be linked by inclusion.
                        let iface_inst = crate::types::ctype::instance(type_ctx, iface_ty);
                        moregen_link(
                            type_ctx,
                            desc.val_type,
                            iface_inst,
                            &mut ahash::AHashSet::new(),
                        );
                        moregen_link(
                            type_ctx,
                            ta.pattern(binding.vb_pat).pat_type,
                            desc.val_type,
                            &mut ahash::AHashSet::new(),
                        );
                        moregen_link(
                            type_ctx,
                            vb_expr.exp_type,
                            desc.val_type,
                            &mut ahash::AHashSet::new(),
                        );
                    }
                }
            }
            crate::types::typedtree::StructureItemDesc::Tstr_module(mb) => {
                moregen_link_mod_expr(type_ctx, ta, ta.module_expr(mb.mb_expr), iface_val_types);
            }
            // A derived binding is a `let` of a variable bound to a function.
            crate::types::typedtree::StructureItemDesc::Tstr_derived(idx) => {
                for bound in ta.derived.bound(*idx) {
                    let Some(&iface_ty) = iface_val_types.get(bound.ident.name()) else {
                        continue;
                    };
                    let iface_inst = crate::types::ctype::instance(type_ctx, iface_ty);
                    moregen_link(type_ctx, bound.ty, iface_inst, &mut ahash::AHashSet::new());
                }
            }
            crate::types::typedtree::StructureItemDesc::Tstr_eval(..)
            | crate::types::typedtree::StructureItemDesc::Tstr_primitive(_)
            | crate::types::typedtree::StructureItemDesc::Tstr_type(..)
            | crate::types::typedtree::StructureItemDesc::Tstr_typext(_)
            | crate::types::typedtree::StructureItemDesc::Tstr_exception(_)
            | crate::types::typedtree::StructureItemDesc::Tstr_recmodule(_)
            | crate::types::typedtree::StructureItemDesc::Tstr_modtype(_)
            | crate::types::typedtree::StructureItemDesc::Tstr_open(_)
            | crate::types::typedtree::StructureItemDesc::Tstr_include(_)
            | crate::types::typedtree::StructureItemDesc::Tstr_attribute(_) => {}
        }
    }
}

fn moregen_link_mod_expr(
    type_ctx: &TypeContext,
    ta: &crate::types::typedtree::TypedArena,
    mod_expr: &crate::types::typedtree::ModuleExpr,
    iface_val_types: &ahash::AHashMap<String, crate::types::type_expr::TypeExprRef>,
) {
    match &mod_expr.mod_desc {
        crate::types::typedtree::ModuleExprDesc::Tmod_structure(s) => {
            moregen_link_structure(type_ctx, ta, s, iface_val_types);
        }
        crate::types::typedtree::ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
            moregen_link_mod_expr(type_ctx, ta, ta.module_expr(*inner), iface_val_types);
        }
        _ => {}
    }
}

fn extract_pat_name(pat: &crate::types::typedtree::Pattern) -> Option<String> {
    match &pat.pat_desc {
        crate::types::typedtree::PatternDesc::Tpat_var(id, _) => Some(id.name().to_string()),
        crate::types::typedtree::PatternDesc::Tpat_alias(_, id, _) => Some(id.name().to_string()),
        _ => None,
    }
}

/// Check if two paths are compatible for moregen linking.
/// OCaml's moregen uses path equality because both impl and iface have
/// the same qualified paths (due to Subst.type_declaration). In Rust,
/// impl has local Pident while iface has qualified Pdot, so we compare
/// the leaf name instead.
fn moregen_paths_compatible(p1: &crate::types::Path, p2: &crate::types::Path) -> bool {
    if p1.same(p2) {
        return true;
    }
    let leaf1 = match p1.view() {
        PathView::Pident(id) => id.name(),
        PathView::Pdot(_, name, _) => name.as_str(),
        _ => return false,
    };
    let leaf2 = match p2.view() {
        PathView::Pident(id) => id.name(),
        PathView::Pdot(_, name, _) => name.as_str(),
        _ => return false,
    };
    leaf1 == leaf2
}

/// Walk two types structurally and link non-generic Tvars in the impl
/// to the corresponding interface types. Matches OCaml's moregen.
fn moregen_link(
    ctx: &TypeContext,
    impl_ty: crate::types::type_expr::TypeExprRef,
    iface_ty: crate::types::type_expr::TypeExprRef,
    visited: &mut ahash::AHashSet<(
        crate::types::type_expr::TypeExprRef,
        crate::types::type_expr::TypeExprRef,
    )>,
) {
    use crate::types::type_expr::{GENERIC_LEVEL, TypeDesc};

    let impl_ty = ctx.repr(impl_ty);
    let iface_ty = ctx.repr(iface_ty);
    if impl_ty == iface_ty {
        return;
    }
    if !visited.insert((impl_ty, iface_ty)) {
        return;
    }

    let impl_desc = ctx.get_desc(impl_ty);
    let iface_desc = ctx.get_desc(iface_ty);

    match (&*impl_desc, &*iface_desc) {
        (TypeDesc::Tvar(..), _) if ctx.get_level(impl_ty) != GENERIC_LEVEL => {
            // Non-generic impl Tvar: link to interface type
            crate::types::ctype::link_type(ctx, impl_ty, iface_ty);
        }
        (
            TypeDesc::Tconstr {
                path: p1, args: a1, ..
            },
            TypeDesc::Tconstr {
                path: p2, args: a2, ..
            },
        ) if moregen_paths_compatible(p1, p2) && a1.len() == a2.len() => {
            let a1 = *a1;
            let a2 = *a2;
            for (a, b) in ctx.type_list(a1).iter().zip(ctx.type_list(a2).iter()) {
                moregen_link(ctx, a, b, visited);
            }
        }
        (TypeDesc::Tarrow { args: a1, ret: r1 }, TypeDesc::Tarrow { args: a2, ret: r2 })
            if a1.len() == a2.len() =>
        {
            let (a1, a2, r1, r2) = (*a1, *a2, *r1, *r2);
            for (a1, a2) in ctx.type_args(a1).iter().zip(ctx.type_args(a2).iter()) {
                moregen_link(ctx, a1.typ, a2.typ, visited);
            }
            moregen_link(ctx, r1, r2, visited);
        }
        (TypeDesc::Ttuple(t1), TypeDesc::Ttuple(t2)) if t1.len() == t2.len() => {
            let t1 = *t1;
            let t2 = *t2;
            for (a, b) in ctx.type_list(t1).iter().zip(ctx.type_list(t2).iter()) {
                moregen_link(ctx, a, b, visited);
            }
        }
        _ => {}
    }
}

/// Per-file configuration overrides extracted from `@@config({flags: [...]})`.
///
/// OCaml's `file_level_flags_handler` (compiler/bsc/rescript_compiler_driver.ml:539-557)
/// runs `Bsc_args.parse_exn` over the whole `command_line_flags` table, so a
/// file flag mutates the same request-local `Clflags`/`Js_config` state the
/// command line set, after it: file flags win for the rest of that compile.
/// This records the flags whose effect a later phase can observe; see
/// `run_file_level_flags` for the ones that have none.
#[derive(Debug, Default, Clone)]
pub struct FileConfigOverrides {
    /// `-enable-experimental LetUnwrap`.
    pub let_unwrap: bool,
    /// `-bs-jsx`.
    pub jsx_version: Option<i32>,
    /// `-bs-jsx-module`.
    pub jsx_module: Option<String>,
    /// `-w`/`-warn-error` specs in application order (`true` = `-warn-error`).
    pub warning_ops: Vec<(bool, String)>,
    /// `-bs-cross-module-opt` (`Some(true)`) or `-bs-no-cross-module-opt`
    /// (`Some(false)`), the last one given (`Js_config.cross_module_inline`).
    pub cross_module_inline: Option<bool>,
    /// `-bs-g` (`Js_config.debug`, read by js_dump.ml:934).
    pub debug: bool,
    /// `-bs-jsx-preserve` (`Clflags.jsx_preserve`, read by
    /// lam_pass_remove_alias.ml:74, js_pass_flatten_and_mark_dead.ml:280 and
    /// js_dump.ml:180).
    pub jsx_preserve: bool,
    /// `-bs-noassertfalse` (`Clflags.no_assert_false`, translcore.ml:1555).
    pub no_assert_false: bool,
    /// `-bs-no-bin-annot` (`Clflags.binary_annotations`): OCaml writes no
    /// `.cmt` or `.cmti` for the file, so tools that read those do not see
    /// it. A build writes neither; `reanalyze` reads this to skip the file.
    pub no_bin_annot: bool,
    /// `-noassert` (`Clflags.noassert`, translcore.ml:1558).
    pub noassert: bool,
    /// `-bs-no-check-div-by-zero` (`Js_config.check_div_by_zero`,
    /// lam_compile_primitive.ml:246-261).
    pub no_check_div_by_zero: bool,
    /// `-bs-no-version-header` (`Js_config.no_version_header`,
    /// js_dump_program.ml:133).
    pub no_version_header: bool,
    /// `-bs-no-builtin-ppx` (`Js_config.no_builtin_ppx`), which
    /// `Ppx_entry` reads right after processing the `@@config`
    /// (compiler/frontend/ppx_entry.ml:39, 58). Only the frontend reads it,
    /// so [`Self::apply`] leaves it out; see [`Self::no_builtin_ppx`].
    pub no_builtin_ppx: bool,
    /// `-open` modules in the order given (`Clflags.open_modules`), opened
    /// after the command line's by `Res_compmisc.initial_env`
    /// (compiler/core/res_compmisc.ml:47-66), which runs after the
    /// `@@config` is processed. See [`Self::open_modules`].
    pub open_modules: Vec<String>,
    /// `-nopervasives` (`Clflags.nopervasives`, res_compmisc.ml:57).
    pub nopervasives: bool,
    /// `-no-alias-deps` (`Clflags.transparent_modules`), read when typing.
    pub transparent_modules: bool,
    /// `-keep-locs` (`Some(true)`) or `-no-keep-locs` (`Some(false)`), the
    /// last one given (`Clflags.keep_locs`, read when saving the signature).
    pub keep_locs: Option<bool>,
}

impl FileConfigOverrides {
    /// Whether the builtin PPX is off for this file: by the command line or
    /// its `@@config`.
    pub fn no_builtin_ppx(&self, options: &CompilerOptions) -> bool {
        options.no_builtin_ppx || self.no_builtin_ppx
    }

    /// The modules this file's initial environment opens: the command
    /// line's, then the `@@config`'s. OCaml processes the `@@config` twice
    /// (ppx_entry.ml:48, js_implementation.ml:129), adding each module twice;
    /// opening a module again changes nothing, so it is opened once.
    /// [`Self::apply`] leaves `options.open_modules` alone: the persistent
    /// environment compiles other units from source with the command line's.
    pub fn open_modules<'a>(&self, options: &'a CompilerOptions) -> std::borrow::Cow<'a, [String]> {
        if self.open_modules.is_empty() {
            return std::borrow::Cow::Borrowed(&options.open_modules);
        }
        let mut open_modules = options.open_modules.clone();
        open_modules.extend(self.open_modules.iter().cloned());
        std::borrow::Cow::Owned(open_modules)
    }

    /// Whether this file's initial environment leaves out Pervasives and
    /// Stdlib. Like [`Self::open_modules`], only this file's initial
    /// environment reads it.
    pub fn nopervasives(&self, options: &CompilerOptions) -> bool {
        options.nopervasives || self.nopervasives
    }

    /// Whether any flag changes a [`CompilerOptions`] field in [`Self::apply`].
    fn changes_options(&self) -> bool {
        self.cross_module_inline.is_some()
            || self.debug
            || self.jsx_preserve
            || self.no_assert_false
            || self.noassert
            || self.no_check_div_by_zero
            || self.no_version_header
            || self.transparent_modules
            || self.keep_locs.is_some()
    }

    /// The options of this file's compile: the command line's with the
    /// `@@config` flags applied after them, as `file_level_flags_handler`
    /// does to the request state. Warning, JSX and `let?` flags are not
    /// folded in: the frontend applies them itself, in OCaml's order.
    pub fn apply<'a>(&self, options: &'a CompilerOptions) -> std::borrow::Cow<'a, CompilerOptions> {
        if !self.changes_options() {
            return std::borrow::Cow::Borrowed(options);
        }
        let mut options = options.clone();
        if let Some(cross_module_inline) = self.cross_module_inline {
            options.cross_module_inline = cross_module_inline;
        }
        // `set` flags (rescript_compiler_driver.ml:213): a file can turn
        // them on, never off.
        options.debug |= self.debug;
        options.jsx_preserve |= self.jsx_preserve;
        options.no_assert_false |= self.no_assert_false;
        options.noassert |= self.noassert;
        options.no_version_header |= self.no_version_header;
        // A `clear` flag: it can only turn the check off.
        options.check_div_by_zero &= !self.no_check_div_by_zero;
        options.transparent_modules |= self.transparent_modules;
        if let Some(keep_locs) = self.keep_locs {
            options.keep_locs = keep_locs;
        }
        std::borrow::Cow::Owned(options)
    }
}

#[derive(Clone, Copy)]
enum BscFlagArity {
    Unit,
    String,
}

/// The arity of a `command_line_flags` entry
/// (compiler/bsc/rescript_compiler_main.ml:233-499), or `None` for an
/// unknown option.
fn bsc_flag_arity(flag: &str) -> Option<BscFlagArity> {
    Some(match flag {
        "-I"
        | "-w"
        | "-o"
        | "-ppx"
        | "-open"
        | "-bs-jsx"
        | "-bs-jsx-module"
        | "-bs-jsx-mode"
        | "-bs-source-map"
        | "-bs-source-map-sources-content"
        | "-bs-source-map-root"
        | "-bs-package-output"
        | "-bs-project-root"
        | "-bs-package-name"
        | "-bs-ns"
        | "-bs-gentype-module"
        | "-bs-gentype-module-resolution"
        | "-bs-gentype-generated-extension"
        | "-bs-gentype-suffix"
        | "-bs-gentype-shim"
        | "-bs-gentype-debug"
        | "-bs-gentype-dep"
        | "-bs-gentype-source-dir"
        | "-bs-gentype-dep-path"
        | "-bs-gentype-bsb-project-root"
        | "-color"
        | "-e"
        | "-reprint-source"
        | "-format"
        | "-enable-experimental"
        | "-runtime-path"
        | "-warn-error" => BscFlagArity::String,
        "-bs-read-cmi"
        | "-bs-jsx-preserve"
        | "-bs-ast"
        | "-bs-test-ast-conversion"
        | "-bs-syntax-only"
        | "-bs-g"
        | "-as-pp"
        | "-no-alias-deps"
        | "-bs-gentype"
        | "-bs-gentype-export-interfaces"
        | "-nostdlib"
        | "-bs-cmi-only"
        | "-bs-cmi"
        | "-bs-cmj"
        | "-bs-no-version-header"
        | "-bs-no-builtin-ppx"
        | "-bs-cross-module-opt"
        | "-bs-no-cross-module-opt"
        | "-debug-ir"
        | "-check-lam"
        | "-bs-no-check-div-by-zero"
        | "-bs-noassertfalse"
        | "-noassert"
        | "-bs-loc"
        | "-dtypedtree"
        | "-dtyped-sexp"
        | "-dtyped-sexp-locs"
        | "-dparsetree"
        | "-dparsetree-sexp-locs"
        | "-drawlambda"
        | "-dlambda-sexp"
        | "-dlambda-sexp-locs"
        | "-draw-coercions"
        | "-dsource"
        | "-only-parse"
        | "-editor-mode"
        | "-ignore-parse-errors"
        | "-verbose"
        | "-keep-locs"
        | "-no-keep-locs"
        | "-nopervasives"
        | "-v"
        | "-version"
        | "-absname"
        | "-bs-no-bin-annot"
        | "-short-paths"
        | "-unsafe"
        | "-warn-help"
        | "-make-runtime" => BscFlagArity::Unit,
        _ => return None,
    })
}

/// `file_level_flags_handler` on a string array: `Bsc_args.parse_exn`
/// (compiler/ext/bsc_args.ml) applying each option in order. Returns `false`
/// when parsing raises, after the options before the failure were applied.
///
/// Every `command_line_flags` entry is accepted. The ones recorded in
/// [`FileConfigOverrides`] are those whose state a later phase of the same
/// compile reads. The rest are accepted without effect:
///
/// - Read before the `@@config` is processed, so OCaml ignores them too:
///   `-I`, `-nostdlib` and `-runtime-path` (`Res_compmisc.init_path` fixes
///   the load path before parsing, compiler/core/js_implementation.ml:170),
///   `-ppx` and `-bs-test-ast-conversion` (`Cmd_ppx_apply` already ran),
///   `-ignore-parse-errors` (parsing is done), and the no-ops `-bs-jsx-mode`,
///   `-unsafe` and `-verbose`.
/// - Without an observable effect: `-bs-cmi` and `-bs-cmj` only skip
///   rewriting an unchanged `.cmi`/`.cmj` (js_implementation.ml:141,
///   compiler/core/lam_compile_main.ml:454).
/// - Not applied per file by Rust: the IR dumps and checks (`-d*`,
///   `-bs-loc`, `-debug-ir`, `-check-lam`), which are debugging aids; what
///   the build decides before it compiles the file: its outputs and paths
///   (`-o`, `-bs-package-output`, `-bs-package-name`, `-bs-ns`,
///   `-bs-project-root`, `-bs-source-map*`, `-make-runtime`), whether it
///   has an interface (`-bs-read-cmi`, typemod.ml:1783), the modes that stop
///   the compile early (`-bs-ast`, `-as-pp`, `-bs-syntax-only`,
///   `-only-parse`, `-bs-cmi-only`, `-editor-mode`), `-bs-no-bin-annot` and
///   genType (`-bs-gentype*`); how diagnostics are shown (`-color`,
///   `-absname`, and `-short-paths`, which Rust does not implement); and
///   the flags that act at once on another input (`-e`, `-format`,
///   `-reprint-source`).
fn run_file_level_flags(
    flags: &[String],
    overrides: &mut FileConfigOverrides,
    state: &mut WarningConfig,
) -> bool {
    let mut i = 0;
    while i < flags.len() {
        let flag = flags[i].as_str();
        i += 1;
        // Anything not starting with `-` is an anonymous argument.
        if !flag.starts_with('-') {
            continue;
        }
        let Some(arity) = bsc_flag_arity(flag) else {
            return false;
        };
        let BscFlagArity::String = arity else {
            match flag {
                "-bs-cross-module-opt" => overrides.cross_module_inline = Some(true),
                "-bs-no-cross-module-opt" => overrides.cross_module_inline = Some(false),
                "-bs-g" => overrides.debug = true,
                "-bs-jsx-preserve" => overrides.jsx_preserve = true,
                "-bs-noassertfalse" => overrides.no_assert_false = true,
                "-bs-no-bin-annot" => overrides.no_bin_annot = true,
                "-noassert" => overrides.noassert = true,
                "-bs-no-check-div-by-zero" => overrides.no_check_div_by_zero = true,
                "-bs-no-version-header" => overrides.no_version_header = true,
                "-bs-no-builtin-ppx" => overrides.no_builtin_ppx = true,
                // These print to stdout and raise `Request_exit`, which the
                // handler's `with _` reports as invalid flags
                // (rescript_compiler_driver.ml:209-211, 524-528, 556).
                "-v" | "-version" | "-warn-help" => return false,
                "-nopervasives" => overrides.nopervasives = true,
                "-no-alias-deps" => overrides.transparent_modules = true,
                "-keep-locs" => overrides.keep_locs = Some(true),
                "-no-keep-locs" => overrides.keep_locs = Some(false),
                _ => {}
            }
            continue;
        };
        let Some(arg) = flags.get(i) else {
            return false;
        };
        i += 1;
        match flag {
            // `Warnings.parse_options` commits only a well-formed list
            // (compiler/ext/warnings.ml:250-254).
            "-w" | "-warn-error" => {
                let as_error = flag == "-warn-error";
                let mut next = state.clone();
                let parsed = if as_error {
                    next.parse_as_error(arg)
                } else {
                    next.parse(arg)
                };
                if parsed.is_err() {
                    return false;
                }
                *state = next;
                overrides.warning_ops.push((as_error, arg.clone()));
            }
            "-bs-jsx" => {
                if arg != "4" {
                    return false;
                }
                overrides.jsx_version = Some(4);
            }
            "-bs-jsx-module" => {
                apply_jsx_module_flag(arg, &mut overrides.jsx_module, &mut overrides.jsx_version);
            }
            "-open" => overrides.open_modules.push(arg.clone()),
            "-enable-experimental" => {
                if arg == "LetUnwrap" {
                    overrides.let_unwrap = true;
                }
            }
            "-bs-source-map"
                if !matches!(
                    arg.to_ascii_lowercase().as_str(),
                    "linked" | "inline" | "hidden" | "false" | "none"
                ) =>
            {
                return false;
            }
            "-bs-source-map-sources-content"
                if !matches!(arg.to_ascii_lowercase().as_str(), "true" | "false") =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

/// `Ast_payload.semantic_string_of_payload`, raising its error as a
/// directive payload error.
fn extract_single_string_payload(
    payload: &Payload,
    arena: &crate::parse_arena::ParseArena,
) -> std::result::Result<Option<String>, DirectivePayloadError> {
    crate::ast_payload::semantic_string_of_payload(arena, payload).map_err(|error| {
        DirectivePayloadError {
            loc: error.loc,
            message: error.message,
        }
    })
}

fn extract_file_directives_from_structure(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> std::result::Result<Vec<String>, DirectivePayloadError> {
    let mut directives = Vec::new();

    for item in structure {
        let StructureItemDesc::Pstr_attribute(attr) = &item.pstr_desc else {
            continue;
        };
        if arena.get_string(attr.0.txt) != "directive" {
            continue;
        }
        // ast_config.ml process_directives: read the payload's semantic string.
        let Some(directive) = extract_single_string_payload(&attr.1, arena)? else {
            return Err(DirectivePayloadError {
                loc: item.pstr_loc,
                message: "Expected a string literal.",
            });
        };
        directives.push(directive);
    }

    Ok(directives)
}

#[derive(Debug, Clone, Copy)]
struct DirectivePayloadError {
    loc: LocIdx,
    message: &'static str,
}

#[derive(Debug, Clone)]
struct ConfigPayloadError {
    loc: LocIdx,
    message: String,
}

impl std::fmt::Display for DirectivePayloadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message)
    }
}

impl std::error::Error for DirectivePayloadError {}

impl std::fmt::Display for ConfigPayloadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ConfigPayloadError {}

fn config_payload_error_to_anyhow(
    err: ConfigPayloadError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    UserDiagnostic::new(
        format_compiler_error_report(arena, source, filename, err.loc, &err.message),
        2,
    )
    .into()
}

#[derive(Debug, Clone, Copy)]
struct ConfigAction {
    name: StrIdx,
    loc: LocIdx,
    expr: Option<ExprIdx>,
}

fn push_config_warning(
    warnings: &mut Vec<ppx::PpxWarning>,
    loc: LocIdx,
    warning: crate::diagnostics::Warning,
) {
    warnings.push(ppx::PpxWarning { loc, warning });
}

fn push_invalid_config_record_warning(warnings: &mut Vec<ppx::PpxWarning>, loc: LocIdx) {
    push_config_warning(
        warnings,
        loc,
        crate::diagnostics::Warning::BsDeriveWarning {
            message: "invalid attribute config-record, ignoring".to_string(),
        },
    );
}

fn config_payload_actions(
    payload: &Payload,
    default_loc: LocIdx,
    arena: &ParseArena,
    warnings: &mut Vec<ppx::PpxWarning>,
) -> Result<Vec<ConfigAction>, ConfigPayloadError> {
    let Payload::PStr(items) = payload else {
        push_invalid_config_record_warning(warnings, default_loc);
        return Ok(Vec::new());
    };
    if items.is_empty() {
        return Ok(Vec::new());
    }
    if items.len() != 1 {
        push_invalid_config_record_warning(warnings, default_loc);
        return Ok(Vec::new());
    }
    let StructureItemDesc::Pstr_eval(inner) = &items[0].pstr_desc else {
        push_invalid_config_record_warning(warnings, default_loc);
        return Ok(Vec::new());
    };
    let (expr_idx, _) = &**inner;
    let expr = arena.get_expr(*expr_idx);
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, with_obj) = inner;
            if with_obj.is_some() {
                push_config_warning(
                    warnings,
                    expr.pexp_loc,
                    crate::diagnostics::Warning::BsDeriveWarning {
                        message: "`with` is not supported, discarding".to_string(),
                    },
                );
                return Ok(Vec::new());
            }
            let mut actions = Vec::with_capacity(fields.len());
            for field in arena.expr_field_list(*fields) {
                let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) else {
                    return Err(ConfigPayloadError {
                        loc: default_loc,
                        message: "Qualified label is not allowed".to_string(),
                    });
                };
                let field_expr = arena.get_expr(field.expr);
                let punned = match &field_expr.pexp_desc {
                    // OCaml compiler/ml/ast_payload.ml:206-214 compares the
                    // label and identifier names, so separately interned Rust
                    // StrIdx values for `no_export: no_export` must still
                    // count as the punned `None` payload.
                    ExpressionDesc::Pexp_ident(lid) => matches!(
                        arena.get_longident(lid.txt),
                        Longident::Lident(value_idx) if value_idx == name_idx
                            || arena.get_string(*value_idx) == arena.get_string(*name_idx)
                    ),
                    _ => false,
                };
                actions.push(ConfigAction {
                    name: *name_idx,
                    loc: field.lid.loc,
                    expr: if punned { None } else { Some(field.expr) },
                });
            }
            Ok(actions)
        }
        ExpressionDesc::Pexp_ident(lid) => {
            let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
                push_invalid_config_record_warning(warnings, default_loc);
                return Ok(Vec::new());
            };
            Ok(vec![ConfigAction {
                name: *name_idx,
                loc: lid.loc,
                expr: None,
            }])
        }
        _ => {
            push_invalid_config_record_warning(warnings, default_loc);
            Ok(Vec::new())
        }
    }
}

fn validate_config_bool_literal(
    expr_idx: ExprIdx,
    arena: &ParseArena,
) -> Result<(), ConfigPayloadError> {
    let expr = arena.get_expr(expr_idx);
    let is_bool_literal = match &expr.pexp_desc {
        ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => matches!(
            arena.get_longident(lid.txt),
            Longident::Lident(name_idx)
                if matches!(arena.get_string(*name_idx), "true" | "false")
        ),
        _ => false,
    };
    if is_bool_literal {
        Ok(())
    } else {
        Err(ConfigPayloadError {
            loc: expr.pexp_loc,
            message: "expect `true` or `false` in this field".to_string(),
        })
    }
}

/// Compiling a stored `.ast`/`.iast`: `Js_implementation.after_parsing_impl`
/// (and `interface_mliast`) run `Ast_config.process_str`/`process_sig` once
/// more under the command-line warning state
/// (compiler/core/js_implementation.ml:38, 129). Returns whether a reported
/// warning is an error.
fn report_stored_ast_config_warnings(
    attr: Option<&crate::parser::ast::Attribute>,
    allow_no_export: bool,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> bool {
    let processing = process_file_config(
        attr,
        allow_no_export,
        arena,
        &warning_config_for_options(options),
        1,
    );
    let mut out = String::new();
    let mut has_error = false;
    for (warning, config) in &processing.warnings {
        has_error |= format_ppx_warnings_with_config(
            arena,
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            &mut out,
        );
    }
    write_stderr(&out);
    has_error
}

/// The string array of a `flags` field, or the error
/// `file_level_flags_handler` raises before parsing
/// (compiler/bsc/rescript_compiler_main.ml:502-514).
fn config_flags_strings(
    expr_idx: Option<ExprIdx>,
    arena: &ParseArena,
) -> Result<Option<(Vec<String>, LocIdx)>, ConfigPayloadError> {
    let Some(expr_idx) = expr_idx else {
        return Ok(None);
    };
    let expr = arena.get_expr(expr_idx);
    let ExpressionDesc::Pexp_array(elements) = &expr.pexp_desc else {
        return Err(ConfigPayloadError {
            loc: expr.pexp_loc,
            message: "string array expected".to_string(),
        });
    };
    let mut flags = Vec::with_capacity(elements.len());
    for elem_idx in arena.expr_list(*elements).iter() {
        let elem = arena.get_expr(*elem_idx);
        // rescript_compiler_main.ml file_level_flags_handler:
        // `Ast_payload.semantic_string_of_expression`.
        let value = match crate::ast_payload::semantic_string_of_expression(arena, elem) {
            Ok(value) => value,
            Err(err) => {
                return Err(ConfigPayloadError {
                    loc: err.loc,
                    message: err.message.to_string(),
                });
            }
        };
        let Some(value) = value else {
            return Err(ConfigPayloadError {
                loc: elem.pexp_loc,
                message: "string literal expected".to_string(),
            });
        };
        flags.push(value);
    }
    Ok(Some((flags, expr.pexp_loc)))
}

/// `Ast_config.process_str`/`process_sig` (compiler/frontend/ast_config.ml),
/// run `runs` times like the direct bsc path (Ppx_entry, then
/// Js_implementation.after_parsing_impl).
#[derive(Default)]
struct FileConfigProcessing {
    overrides: FileConfigOverrides,
    /// Warnings together with the warning state they were emitted under.
    warnings: Vec<(ppx::PpxWarning, WarningConfig)>,
    /// The warnings of the second `Ast_config.process_str`, which
    /// `Js_implementation.after_parsing_impl` runs after the builtin ppx
    /// (js_implementation.ml:125-129).
    late_warnings: Vec<(ppx::PpxWarning, WarningConfig)>,
    error: Option<ConfigPayloadError>,
}

fn process_file_config(
    attr: Option<&crate::parser::ast::Attribute>,
    allow_no_export: bool,
    arena: &ParseArena,
    base: &WarningConfig,
    runs: usize,
) -> FileConfigProcessing {
    let mut result = FileConfigProcessing::default();
    let Some(attr) = attr else {
        return result;
    };
    let mut state = base.clone();
    for run in 0..runs {
        let mut run_warnings: Vec<(ppx::PpxWarning, WarningConfig)> = Vec::new();
        let mut overrides = FileConfigOverrides::default();
        let mut payload_warnings = Vec::new();
        let actions = config_payload_actions(&attr.1, attr.0.loc, arena, &mut payload_warnings);
        for warning in payload_warnings {
            run_warnings.push((warning, state.clone()));
        }
        let actions = match actions {
            Ok(actions) => actions,
            Err(err) => {
                push_config_run_warnings(&mut result, run, run_warnings);
                result.error = Some(err);
                return result;
            }
        };
        // `Ast_payload.table_dispatch` (compiler/ml/ast_payload.ml).
        for action in actions {
            let outcome = match arena.get_string(action.name) {
                "no_export" if allow_no_export => match action.expr {
                    Some(expr_idx) => validate_config_bool_literal(expr_idx, arena),
                    None => Ok(()),
                },
                "flags" => match config_flags_strings(action.expr, arena) {
                    Ok(Some((flags, loc))) => {
                        if !run_file_level_flags(&flags, &mut overrides, &mut state) {
                            run_warnings.push((
                                ppx::PpxWarning {
                                    loc,
                                    warning: crate::diagnostics::Warning::Preprocessor {
                                        message: "invalid flags for bsc".to_string(),
                                    },
                                },
                                state.clone(),
                            ));
                        }
                        Ok(())
                    }
                    Ok(None) => Ok(()),
                    Err(err) => Err(err),
                },
                name => Err(ConfigPayloadError {
                    loc: action.loc,
                    message: format!("{name} is not supported"),
                }),
            };
            if let Err(err) = outcome {
                push_config_run_warnings(&mut result, run, run_warnings);
                result.overrides = overrides;
                result.error = Some(err);
                return result;
            }
        }
        push_config_run_warnings(&mut result, run, run_warnings);
        result.overrides = overrides;
    }
    result
}

fn push_config_run_warnings(
    result: &mut FileConfigProcessing,
    run: usize,
    warnings: Vec<(ppx::PpxWarning, WarningConfig)>,
) {
    if run == 0 {
        result.warnings.extend(warnings);
    } else {
        result.late_warnings.extend(warnings);
    }
}

/// `iter_on_config_str`: only the first `@@config` among the leading
/// attributes is processed (compiler/frontend/ast_config.ml:55-65).
fn first_config_attribute_of_structure<'s>(
    structure: &'s Structure,
    arena: &ParseArena,
) -> Option<&'s crate::parser::ast::Attribute> {
    for item in structure {
        let StructureItemDesc::Pstr_attribute(attr) = &item.pstr_desc else {
            return None;
        };
        if arena.get_string(attr.0.txt) == "config" {
            return Some(attr);
        }
    }
    None
}

/// `iter_on_config_sig` (compiler/frontend/ast_config.ml:72-81).
fn first_config_attribute_of_signature<'s>(
    signature: &'s Signature,
    arena: &ParseArena,
) -> Option<&'s crate::parser::ast::Attribute> {
    for item in signature {
        let SignatureItemDesc::Psig_attribute(attr) = &item.psig_desc else {
            return None;
        };
        if arena.get_string(attr.0.txt) == "config" {
            return Some(attr);
        }
    }
    None
}

fn validate_file_config_from_structure(
    structure: &Structure,
    arena: &ParseArena,
    base: &WarningConfig,
) -> FileConfigProcessing {
    process_file_config(
        first_config_attribute_of_structure(structure, arena),
        true,
        arena,
        base,
        2,
    )
}

fn validate_file_config_from_signature(
    signature: &Signature,
    arena: &ParseArena,
    base: &WarningConfig,
) -> FileConfigProcessing {
    process_file_config(
        first_config_attribute_of_signature(signature, arena),
        false,
        arena,
        base,
        2,
    )
}

/// Extract `@@config({flags: [...]})` overrides from a parsed structure.
pub fn extract_file_config_from_structure(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> FileConfigOverrides {
    process_file_config(
        first_config_attribute_of_structure(structure, arena),
        true,
        arena,
        &WarningConfig::new(),
        1,
    )
    .overrides
}

/// Extract `@@config({flags: [...]})` overrides from a parsed signature.
pub fn extract_file_config_from_signature(
    signature: &Signature,
    arena: &crate::parse_arena::ParseArena,
) -> FileConfigOverrides {
    process_file_config(
        first_config_attribute_of_signature(signature, arena),
        false,
        arena,
        &WarningConfig::new(),
        1,
    )
    .overrides
}

/// Normalize types to match OCaml's normalize_signature.
/// OCaml calls normalize_type on each Sig_value's val_type in the top-level
/// inferred signature. normalize_type is recursive (walks all children via
/// iter_type_expr), so all types reachable from a top-level val_type are normalized.
///
/// Key: OCaml's val_type comes from `enter_variable` during pattern typing, which
/// uses `build_as_type(inner)` for alias patterns. For `Tpat_alias(Tpat_any, "v")`,
/// val_type = Tpat_any's pat_type, NOT the outer pattern's pat_type. We look up
/// val_type from the env to match this behavior exactly.
/// `Typemod.normalize_signature` (compiler/ml/typemod.ml:1634-1645): run
/// `Ctype.normalize_type` over the value types of the (simplified)
/// signature, recursing into module types. typemod.ml:1765-1766 applies it to
/// `simplify_signature sg`, so shadowed items are left as typed.
pub(crate) fn normalize_signature(
    type_ctx: &TypeContext,
    env: &Env,
    sig: &[crate::types::decl::SignatureItem],
) {
    use crate::types::decl::SignatureItem;
    for item in sig {
        match item {
            SignatureItem::SigValue(_, desc) => {
                crate::types::ctype::normalize_type(type_ctx, env, desc.val_type);
            }
            SignatureItem::SigModule(_, md, _) => normalize_modtype(type_ctx, env, &md.md_type),
            _ => {}
        }
    }
}

fn normalize_modtype(type_ctx: &TypeContext, env: &Env, mty: &crate::types::decl::ModuleType) {
    use crate::types::decl::ModuleType;
    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig) => normalize_signature(type_ctx, env, sig),
        ModuleType::MtyFunctor { result, .. } => normalize_modtype(type_ctx, env, result),
    }
}

fn rename_saved_module_type_idents(type_ctx: &TypeContext, mty: &crate::types::decl::ModuleType) {
    use crate::types::decl::ModuleType;

    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig) => rename_saved_signature_idents(type_ctx, sig),
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            // Subst.modtype renames the functor binder before traversing its
            // argument and result module types (compiler/ml/subst.ml:345-348).
            type_ctx.rename_ident(param);
            if let Some(param_type) = param_type {
                rename_saved_module_type_idents(type_ctx, param_type);
            }
            rename_saved_module_type_idents(type_ctx, result);
        }
    }
}

fn rename_saved_signature_idents(
    type_ctx: &TypeContext,
    sig: &[crate::types::decl::SignatureItem],
) {
    use crate::types::decl::SignatureItem;

    // Subst.signature first runs rename_bound_idents over the complete
    // signature, then traverses each renamed component in source order
    // (compiler/ml/subst.ml:322-354). Preserve both allocation passes even
    // though the direct Rust CMI writer does not need the copied identifiers.
    for item in sig {
        match item {
            SignatureItem::SigType(id, _, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigModtype(id, _)
            | SignatureItem::SigValue(id, _)
            | SignatureItem::SigTypext(id, _, _) => {
                type_ctx.rename_ident(id);
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }

    for item in sig {
        match item {
            SignatureItem::SigModule(_, md, _) => {
                rename_saved_module_type_idents(type_ctx, &md.md_type);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = &mtd.mtd_type {
                    rename_saved_module_type_idents(type_ctx, mty);
                }
            }
            SignatureItem::SigValue(_, _)
            | SignatureItem::SigType(_, _, _)
            | SignatureItem::SigTypext(_, _, _)
            | SignatureItem::SigClass
            | SignatureItem::SigClassType => {}
        }
    }
}

/// `Env.save_signature` (env.ml:1886-1892) writes `Subst.signature
/// (Subst.for_saving Subst.identity) sg`: a copy whose bound identifiers are
/// renamed (subst.ml:322-364), taking fresh stamps.
fn saved_signature_copy(
    type_ctx: &TypeContext,
    sig: &[crate::types::decl::SignatureItem],
) -> crate::types::decl::Signature {
    crate::cmi::persistent_env::freshened_signature_bound_idents_from_kind(
        "save_signature",
        sig,
        type_ctx,
    )
}

fn synchronize_lambda_start_stamp(type_ctx: &TypeContext) -> i32 {
    // OCaml uses a single mutable `Ident.currentstamp` across typechecking and
    // Lambda translation. Rust still has a few typedtree locals created through
    // `Ident::create_local`, so synchronize before raw-lambda creates fresh
    // identifiers. Otherwise a raw-lambda temp can reuse a typedtree stamp.
    let stamp = type_ctx
        .current_stamp()
        .max(crate::ident::Ident::current_local_stamp());
    type_ctx.set_current_time(stamp);
    crate::ident::Ident::set_current_time(stamp);
    stamp
}

/// Result of an in-process `.res` compilation.
#[derive(Default)]
pub struct InProcessCompileResult {
    /// The JavaScript when the compile has no output path, else empty.
    pub js_output: String,
    /// The JavaScript for each configured output path.
    pub js_outputs: Vec<JsOutput>,
    /// The unit's typed signature.
    pub signature: crate::types::decl::Signature,
    /// The unit's interface, published to the modules that depend on it.
    pub pers_struct: Option<std::sync::Arc<PortablePersStruct>>,
    /// The module has no top-level side effects (`.cmj` `pure`).
    pub is_pure: bool,
    /// `.cmj` constants other modules inline in place of the export.
    pub cmj_export_constants: ahash::AHashMap<String, CmjExportConstant>,
    /// `.cmj` arities of the exports.
    pub cmj_export_arities: ahash::AHashMap<String, CmjExportArity>,
    /// `.cmj` `persistent_closed_lambda` exports for cross-module inlining
    /// (lam_stats_export.ml:53-89).
    pub cmj_export_lambdas: crate::lambda::CmjExportLambdas,
    /// Intermediate-representation sexps, populated when
    /// `CompilerOptions::capture_intermediates` is true (for the playground).
    pub typed_tree_sexp: String,
    /// The raw Lambda sexp, populated with `typed_tree_sexp`.
    pub raw_lambda_sexp: String,
    /// The optimized Lambda sexp, populated with `typed_tree_sexp`.
    pub lambda_sexp: String,
    /// The intermediate representations requested by `CompilerOptions::dumps`.
    pub dumps: Vec<(DumpKind, String)>,
    /// The warning reports the file compile prints to stderr.
    pub warnings: String,
    /// GenType's part of the compile, applied after the JavaScript is
    /// written (`apply_gentype_outcome`).
    pub gentype: Option<crate::gentype::main::Outcome>,
}

/// Owned in-process compilation state after typechecking and Lambda lowering,
/// before JS backend metadata from dependencies is required.
#[derive(Default)]
pub struct InProcessPreJsCompileResult {
    /// Optional accounting carried across the worker handoff without thread-local state.
    pub derived_census: Option<Box<crate::derived_census::Census>>,
    /// The unit's Lambda program, or None when compilation stopped after typing.
    pub lowered_lambda: Option<crate::lambda::arena::LamProgram>,
    /// The modules the program references, whose `.cmj` metadata the JS
    /// backend may read.
    pub possible_required_modules: AHashSet<ModuleId>,
    /// The paths through module fields to the nested `make` functions the
    /// final signature exports (`Translmod.flat_make_paths`).
    pub flat_make_paths: Vec<crate::lambda::FlatMakePath>,
    /// The identifier stamp counter when lowering ended; the JS backend
    /// resumes from it.
    pub ident_stamp_at_js_boundary: i32,
    /// The file's `@@directive` payloads, printed atop the JavaScript.
    pub file_directives: Vec<String>,
    /// The file's `@@config` flags, which the JS backend applies to the
    /// options it is given ([`FileConfigOverrides::apply`]).
    pub file_config: FileConfigOverrides,
    /// The unit's typed signature.
    pub signature: crate::types::decl::Signature,
    /// The unit's interface, published to the modules that depend on it.
    pub pers_struct: Option<std::sync::Arc<PortablePersStruct>>,
    /// Resolves the location handles of `lowered_lambda`; outlives the parse
    /// arena and typed tree.
    pub lam_locs: crate::lambda::LamLocTable,
    /// Intermediate-representation sexps, populated when
    /// `CompilerOptions::capture_intermediates` is true (for the playground).
    pub typed_tree_sexp: String,
    /// The raw Lambda sexp, populated with `typed_tree_sexp`.
    pub raw_lambda_sexp: String,
    /// The optimized Lambda sexp, populated with `typed_tree_sexp`.
    pub lambda_sexp: String,
    /// The intermediate representations requested by `CompilerOptions::dumps`.
    pub dumps: Vec<(DumpKind, String)>,
    /// The warning reports the file compile prints to stderr.
    pub warnings: String,
    /// GenType's part of the compile, applied after the JavaScript is
    /// written (`apply_gentype_outcome`).
    pub gentype: Option<crate::gentype::main::Outcome>,
    /// The units whose interface type checking read.
    pub loaded_units: Vec<String>,
    /// What the typed tree read of other units (with
    /// `CompilerOptions::collect_unit_reads`).
    pub unit_reads: Vec<crate::cmi::item_deps::UnitRead>,
    /// With `RESCRIPT_DERIVED_PATH=check`, the same unit compiled from the
    /// general forms of its derived items; the JS backend runs on both and
    /// compares what they produce.
    pub derived_reference: Option<Box<InProcessPreJsCompileResult>>,
    /// The collector the check of this unit reports to
    /// ([`CompilerOptions::derived_differences`]).
    pub derived_differences: Option<DerivedDifferences>,
}

/// The `.cmj` metadata of an in-process compile, available after the JS
/// backend ran and before its output is printed, so dependents can start.
pub struct InProcessJsMetadataReady {
    /// The module has no top-level side effects (`.cmj` `pure`).
    pub is_pure: bool,
    /// `.cmj` constants other modules inline in place of the export.
    pub cmj_export_constants: ahash::AHashMap<String, CmjExportConstant>,
    /// `.cmj` arities of the exports.
    pub cmj_export_arities: ahash::AHashMap<String, CmjExportArity>,
    /// `.cmj` `persistent_closed_lambda` exports for cross-module inlining.
    pub cmj_export_lambdas: crate::lambda::CmjExportLambdas,
    /// The unit's interface, published to the modules that depend on it.
    pub pers_struct: Option<std::sync::Arc<PortablePersStruct>>,
}

/// Signature payload produced after in-process implementation typechecking but
/// before Lambda/JS compilation. Rewatch uses this to unblock dependent
/// typechecking while preserving OCaml's save-before-translation order
/// (compiler/ml/typemod.ml:1779-1788; compiler/ml/translmod.ml:267).
pub struct InProcessSignatureReady {
    /// The unit's interface, published to the modules that depend on it.
    pub pers_struct: Option<std::sync::Arc<PortablePersStruct>>,
}

/// Receives a unit's signature once it is typed; may return a registry to
/// continue with.
pub type InProcessSignatureReadyHook<'a> =
    dyn FnMut(InProcessSignatureReady) -> Result<Option<ModuleRegistry>> + 'a;

/// Receives the modules the JS backend may require; may return a refreshed
/// registry holding their metadata.
pub type InProcessBeforeJsHook<'a> =
    dyn FnMut(&AHashSet<ModuleId>) -> Result<Option<ModuleRegistry>> + 'a;

/// Receives a unit's `.cmj` metadata before its JavaScript is printed.
pub type InProcessJsMetadataReadyHook<'a> = dyn FnMut(InProcessJsMetadataReady) -> Result<()> + 'a;

/// Result of an in-process `.resi` interface type-check.
pub struct InProcessInterfaceResult {
    /// The interface's typed signature.
    pub signature: crate::types::decl::Signature,
    /// The interface, published to the modules that depend on it.
    pub pers_struct: Option<std::sync::Arc<PortablePersStruct>>,
    /// What GenType read in the interface (GenTypeMain.ml:91-107), for the
    /// implementation's compile; `None` without GenType.
    pub gentype: Option<crate::gentype::main::InterfaceRead>,
    /// The typed-tree dumps requested by `CompilerOptions::dumps`.
    pub dumps: Vec<(DumpKind, String)>,
    /// The warning reports the file compile prints to stderr.
    pub warnings: String,
    /// The units whose interface type checking read.
    pub loaded_units: Vec<String>,
    /// What the typed signature read of other units (with
    /// `CompilerOptions::collect_unit_reads`).
    pub unit_reads: Vec<crate::cmi::item_deps::UnitRead>,
}

/// The compiler error bsc reports for an invalid string escape GenType read
/// (Ast_payload.ml:39-51), which GenType does not catch.
fn gentype_escape_report(
    arena: &ParseArena,
    type_ctx: &TypeContext,
    source: &str,
    filename: &str,
    escape: crate::gentype::annotation::InvalidEscape,
) -> String {
    const MESSAGE: &str = "Invalid string escape sequence";
    match escape {
        crate::gentype::annotation::InvalidEscape::Parsed(loc) => {
            format_compiler_error_report(arena, source, filename, loc, MESSAGE)
        }
        crate::gentype::annotation::InvalidEscape::Decl(loc) => {
            format_compiler_error_report_from_external_location(
                type_ctx,
                filename,
                &type_ctx.resolve_loc(loc),
                MESSAGE,
            )
        }
    }
}

/// A typed unit as GenType reads it.
struct GentypeUnit<'a> {
    /// The typed structure or signature.
    annots: crate::gentype::main::TypedArtifactAnnots<'a>,
    arena: &'a ParseArena,
    ta: &'a crate::types::typedtree::TypedArena,
    type_ctx: &'a TypeContext,
    /// Reads the source text GenType's reports quote.
    source: &'a dyn Fn() -> String,
    filename: &'a str,
    module_name: &'a str,
}

/// Run `f` on the artifact GenType reads for a typed unit, when GenType is
/// enabled. Mirrors compiler/core/js_implementation.ml:170, but uses the
/// in-memory typedtree that Rust already has instead of reopening the CMT
/// saved by compiler/ml/typemod.ml:1763-1764 and 1785-1787.
fn with_gentype_artifact<R>(
    options: &CompilerOptions,
    unit: GentypeUnit<'_>,
    f: impl FnOnce(
        &crate::gentype::config::T,
        Option<&crate::gentype::module_resolver::Resolver>,
        crate::gentype::main::TypedArtifact<'_>,
    ) -> R,
) -> Option<R> {
    if options.check_only {
        return None;
    }
    let config = options.gentype_config.as_ref()?;
    let GentypeUnit {
        annots,
        arena,
        ta,
        type_ctx,
        source,
        filename,
        module_name,
    } = unit;
    let is_interface = matches!(
        annots,
        crate::gentype::main::TypedArtifactAnnots::Interface(_)
    );
    let render_escape =
        |escape| gentype_escape_report(arena, type_ctx, &source(), filename, escape);
    Some(crate::timing::measure(crate::timing::Phase::Gentype, || {
        f(
            config,
            options.gentype_resolver.as_deref(),
            crate::gentype::main::TypedArtifact {
                annots,
                arena,
                ta,
                ctx: type_ctx,
                source_file: Some(filename),
                compiler_module_name: module_name.to_string(),
                // OCaml passes outputprefix.cmt into GenTypeMain.process_cmt_file
                // from compiler/core/js_implementation.ml:72/170, then computes
                // file_name with compiler/gentype/Paths.ml:61-86. The in-process
                // path has the source filename here, so derive the same
                // outputprefix-shaped GenType name instead of reusing the
                // capitalized compiler module name.
                file_name: crate::gentype::paths::get_module_name_from_source_path(filename),
                is_interface,
                declarations_only: options.gentype_declarations_only,
                declarations_needed: options.gentype_declarations_needed,
                render_escape: &render_escape,
            },
        )
    }))
}

/// GenType for an implementation (GenTypeMain.ml:136-175), given what
/// reading its interface found when it has one: what to apply once the
/// unit's JavaScript is written (`apply_gentype_outcome`).
fn process_gentype_typed_artifact_if_enabled(
    options: &CompilerOptions,
    interface: Option<crate::gentype::main::InterfaceRead>,
    unit: GentypeUnit<'_>,
) -> Option<crate::gentype::main::Outcome> {
    with_gentype_artifact(
        options,
        unit,
        |config, resolver, artifact| match interface {
            None => crate::gentype::main::process_typed_artifact(config, resolver, artifact),
            Some(interface) => crate::gentype::main::process_implementation_with_interface(
                config, resolver, interface, artifact,
            ),
        },
    )
}

/// Run GenType's part of a compile once the unit's JavaScript is written
/// (js_implementation.ml:164-171): write its file and return the warnings it
/// prints, which follow the compile's, or fail the compile with the
/// exception it raised, reported after `warnings` (the compile's warnings,
/// which bsc printed before) and GenType's own.
pub fn apply_gentype_outcome(
    outcome: Option<crate::gentype::main::Outcome>,
    warnings: &str,
    filename: &str,
) -> Result<String> {
    let Some(outcome) = outcome else {
        return Ok(String::new());
    };
    match outcome.apply() {
        Ok((printed, Ok(()))) => Ok(printed),
        Ok((printed, Err(report))) => {
            Err(UserDiagnostic::new(format!("{warnings}{printed}{report}"), 2).into())
        }
        Err(error) => {
            Err(anyhow::Error::new(error).context(format!("GenType failed for {filename}")))
        }
    }
}

/// `apply_gentype_outcome` for a build. GenType's notes go to bsc's stdout,
/// which rescript-ocaml drops for a compile that succeeds and shows after
/// its stderr for one that fails (rewatch-ocaml/compiler_scheduler.ml:229-244):
/// the notes are dropped, or follow the exception GenType raised, which
/// follows `warnings`.
pub fn apply_gentype_outcome_in_build(
    outcome: Option<crate::gentype::main::Outcome>,
    warnings: &str,
    filename: &str,
) -> Result<()> {
    let Some(outcome) = outcome else {
        return Ok(());
    };
    match outcome.apply() {
        Ok((_, Ok(()))) => Ok(()),
        Ok((printed, Err(report))) => {
            Err(UserDiagnostic::new(format!("{warnings}{report}{printed}"), 2).into())
        }
        Err(error) => {
            Err(anyhow::Error::new(error).context(format!("GenType failed for {filename}")))
        }
    }
}

/// Type-check an interface source in process, running the frontend as the
/// file compile does (its warnings go to stderr).
pub fn typecheck_interface_source_in_process(
    source: &str,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> Result<InProcessInterfaceResult> {
    let mut parser = Parser::new(filename, source);
    let signature = module::parse_signature(&mut parser);
    let mut frontend_output = String::new();
    let frontend = run_interface_frontend(
        &mut parser,
        signature,
        source,
        filename,
        options,
        &mut frontend_output,
    );
    write_stderr(&frontend_output);
    let frontend = frontend?;
    let mut effective_options = options.clone();
    effective_options.experimental_let_unwrap = frontend.experimental_let_unwrap;
    let mut arena = parser.into_arena();
    crate::types::typecore::prepare_typecheck_arena(&mut arena);
    let result = typecheck_preprocessed_signature_in_process(
        &arena,
        &frontend.signature,
        filename,
        module_name,
        &effective_options,
        registry,
    )?;
    if frontend.warnings_fatal {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }
    Ok(result)
}

/// Parse an implementation source, run the frontend (its warnings go to
/// stderr) and compile it in process to JavaScript.
pub fn compile_source_in_process(
    source: &str,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
    gentype_interface: Option<crate::gentype::main::InterfaceRead>,
) -> Result<InProcessCompileResult> {
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    let mut frontend_output = String::new();
    let frontend = run_implementation_frontend(
        &mut parser,
        structure,
        source,
        filename,
        options,
        &mut frontend_output,
    );
    write_stderr(&frontend_output);
    let frontend = frontend?;
    let warnings_fatal = frontend.warnings_fatal;
    let experimental_let_unwrap = frontend.experimental_let_unwrap;
    // The frontend already applied `no_export` (js_implementation.ml:130).
    let structure = frontend.structure;
    parser.arena_mut().reserve_typecheck_synthetic_capacity();

    let mut effective_options = if options.experimental_let_unwrap == experimental_let_unwrap {
        std::borrow::Cow::Borrowed(options)
    } else {
        let mut options = options.clone();
        options.experimental_let_unwrap = experimental_let_unwrap;
        std::borrow::Cow::Owned(options)
    };
    if options.derived_path == DerivedPath::Check && parser.arena().plans().item_count() > 0 {
        let source = source.to_owned();
        let filename = filename.to_owned();
        let mut general_options = options.clone();
        general_options.derived_path = DerivedPath::General;
        general_options.derived_census = None;
        general_options.derived_reference = None;
        effective_options.to_mut().derived_reference = Some(std::sync::Arc::new(move || {
            let mut parser = Parser::new(&filename, &source);
            let structure = module::parse_structure(&mut parser);
            let frontend = run_implementation_frontend(
                &mut parser,
                structure,
                &source,
                &filename,
                &general_options,
                &mut String::new(),
            )
            .map_err(|error| anyhow::anyhow!("the frontend failed on {filename}: {error}"))?;
            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            Ok((parser.into_arena(), frontend.structure))
        }));
    }

    // Borrow source/options for the duration of this synchronous compile.
    // No owned fallback inputs are built unless the attempt requests them.
    let fallback = general_syntax_provider(source, filename, options);

    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    let result = compile_preprocessed_structure_in_process_with_signature_hook(
        parser.arena(),
        &structure,
        filename,
        module_name,
        &effective_options,
        registry,
        has_interface,
        gentype_interface,
        None,
        None,
        Some(&fallback),
    )?;
    // Like the direct compile: a frontend warning configured as an error fails
    // the compilation once type checking has reported its own diagnostics.
    if warnings_fatal {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }
    Ok(result)
}

fn module_format_for_output_path(path: &FsPath) -> ModuleFormat {
    match path.file_name().and_then(|name| name.to_str()) {
        Some(name) if name.ends_with(".mjs") => ModuleFormat::EsModule,
        _ => ModuleFormat::CommonJs,
    }
}

fn effective_js_output_targets(options: &CompilerOptions) -> Vec<JsOutputTarget> {
    if !options.js_output_targets.is_empty() {
        return options.js_output_targets.clone();
    }

    options
        .output_path
        .as_ref()
        .map(|path| JsOutputTarget {
            path: path.clone(),
            module_format: options
                .output_module_format
                .unwrap_or_else(|| module_format_for_output_path(path)),
        })
        .into_iter()
        .collect()
}

/// The JavaScript printing settings a source file sets for itself.
#[derive(Clone, Copy)]
struct JsFileSettings<'a> {
    /// `@@directive` lines printed at the top of the output.
    file_directives: &'a [String],
    /// `-bs-g` or `@@config({flags: ["-bs-g"]})`.
    debug: bool,
    /// `-bs-jsx-preserve` or its file-level override.
    jsx_preserve: bool,
}

// Keep opt-in source-map setup out of the default printer's register allocation.
#[cold]
#[inline(never)]
fn render_oxc_source_map(
    program: &DepsProgram,
    resolver: &ModulePathResolver,
    settings: JsFileSettings<'_>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    lam_locs: std::sync::Arc<crate::lambda::LamLocTable>,
) -> Result<(String, Option<String>), crate::emit::Unsupported> {
    let source_path = options.source_filename.as_deref().map(FsPath::new);
    let source_map_target = output_path.map(FsPath::to_path_buf).or_else(|| {
        (options.source_map == crate::js_ir::source_map::SourceMapMode::Inline).then(|| {
            let source = source_path.unwrap_or_else(|| FsPath::new("_none_.res"));
            source.with_extension("js")
        })
    });
    let (Some(target), Some(source)) = (source_map_target.as_deref(), source_path) else {
        return Err(crate::emit::Unsupported("source map: missing output or source path"));
    };
    crate::emit::emit_with_source_map(
        program, resolver, settings.file_directives, settings.debug, settings.jsx_preserve,
        !options.no_version_header, &crate::emit::sourcemap::Options {
            target, source, mode: options.source_map,
            sources_content: options.source_map_sources_content,
            source_root: &options.source_map_root, locations: lam_locs,
        },
    )
}

fn render_js_program(
    program: &DepsProgram,
    resolver: &ModulePathResolver,
    settings: JsFileSettings<'_>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    lam_locs: std::sync::Arc<crate::lambda::LamLocTable>,
) -> (String, Option<String>) {
    let JsFileSettings {
        file_directives,
        debug,
        jsx_preserve,
    } = settings;
    if let crate::emit::PrinterMode::Oxc(stats) = &options.js_printer {
        let mut raw_audit = stats.raw_audit_buffer();
        let result = if options.source_map != crate::js_ir::source_map::SourceMapMode::None
            && std::env::var("RESCRIPT_JS_PRINTER_SOURCE_MAPS").as_deref() == Ok("legacy")
        {
            Err(crate::emit::Unsupported(
                "source maps: parity legacy policy",
            ))
        } else if options.source_map != crate::js_ir::source_map::SourceMapMode::None {
            render_oxc_source_map(
                program,
                resolver,
                JsFileSettings {
                    file_directives,
                    debug,
                    jsx_preserve,
                },
                options,
                output_path,
                lam_locs.clone(),
            )
        } else {
            crate::emit::emit_audited(
                program,
                resolver,
                file_directives,
                debug,
                jsx_preserve,
                !options.no_version_header,
                raw_audit.as_mut(),
            )
        };
        stats.record(&result);
        if let Err(error) = stats.report_output(
            &result,
            options.source_filename.as_deref().map(FsPath::new),
            output_path,
        ) {
            log::error!("oxc printer coverage report: {error}");
        }
        if result.is_ok() {
            stats.record_raw(raw_audit);
        }
        match result {
            Ok(output) => return output,
            Err(reason) => log::debug!("oxc printer fallback: {}", reason.0),
        }
    }
    let source_path = options.source_filename.as_deref().map(FsPath::new);
    let source_map_target = output_path.map(FsPath::to_path_buf).or_else(|| {
        (options.source_map == crate::js_ir::source_map::SourceMapMode::Inline).then(|| {
            let source = source_path.unwrap_or_else(|| FsPath::new("_none_.res"));
            source.with_extension("js")
        })
    });
    if let (Some(target), Some(source)) = (source_map_target.as_deref(), source_path) {
        print_deps_program_with_source_map(
            program,
            Some(resolver),
            file_directives,
            debug,
            jsx_preserve,
            !options.no_version_header,
            target,
            source,
            options.source_map,
            options.source_map_sources_content,
            &options.source_map_root,
            lam_locs,
        )
    } else {
        (
            print_deps_program_with_directives_and_options(
                program,
                Some(resolver),
                file_directives,
                debug,
                jsx_preserve,
                !options.no_version_header,
            ),
            None,
        )
    }
}

type JsBackendOutput = (
    DepsProgram,
    ModulePathResolver,
    ahash::AHashMap<String, CmjExportConstant>,
    ahash::AHashMap<String, CmjExportArity>,
    crate::lambda::CmjExportLambdas,
    // Resolves the program's location handles (source maps) after the
    // backend imported inlined `.cmj` lambdas into it.
    crate::lambda::LamLocTable,
);

/// Build the `LambdaCompiler` for one JS output target: resolve local module
/// path overrides for the possibly-required modules and install the flat
/// `make` export paths.
#[allow(clippy::too_many_arguments)]
fn js_backend_compiler(
    flat_make_paths: Vec<crate::lambda::FlatMakePath>,
    possible_required_modules: &AHashSet<ModuleId>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    output_module_format: Option<ModuleFormat>,
    persistent_env: Option<PersistentEnv>,
    jsx_preserve: bool,
    cross_module_inline: bool,
    lam_locs: crate::lambda::LamLocTable,
) -> LambdaCompiler {
    let mut module_path_resolver = ModulePathResolver::from_compile_options(
        options.source_filename.as_deref(),
        output_path,
        output_module_format,
        options.package_name.as_deref(),
        options.runtime_path.as_deref(),
        persistent_env,
        options.make_runtime,
    );
    module_path_resolver.set_package_specs(&options.js_package_specs);
    for module in possible_required_modules {
        if matches!(module.kind, Kind::Ml) && !module.dynamic_import {
            if let Some(path) =
                module_path_resolver.resolve_local_module_fallback_path(module.id.name())
            {
                module_path_resolver.set_module_path_override(module.id.name(), path);
            }
        }
    }
    let mut compiler = LambdaCompiler::with_module_path_resolver_and_options(
        Some(module_path_resolver),
        jsx_preserve,
        options.check_div_by_zero,
        cross_module_inline,
    );
    compiler.set_source_map_enabled(
        options.source_map != crate::js_ir::source_map::SourceMapMode::None,
    );
    compiler.set_flat_make_paths(flat_make_paths);
    compiler.set_lam_locs(lam_locs);
    if options.backend == crate::bir::shadow::BackendMode::Check {
        compiler.set_shadow_unit(options.source_filename.as_deref().unwrap_or("_none_"));
    }
    compiler
}

// Keep the opt-in capture off the monomorphized legacy path.
fn compile_with_lower_check(
    compiler: &mut LambdaCompiler,
    arena: crate::lambda::arena::LamArena,
    root: crate::lambda::arena::Lam,
    possible: AHashSet<ModuleId>,
    options: &CompilerOptions,
    jsx_preserve: bool,
    unit: &str,
) -> Result<DepsProgram> {
    if !options.backend.checks_lowering() {
        return Ok(compiler.compile_deps_program_in_arena(arena, root, possible));
    }
    let (program, check) = compiler.compile_deps_program_with_lower_check::<true>(arena, root, possible);
    crate::bir::shadow::check_lower(check.expect("opt-in capture"), unit, jsx_preserve)?;
    Ok(program)
}

fn finish_js_backend(
    mut compiler: LambdaCompiler,
    program: DepsProgram,
    options: &CompilerOptions,
) -> Result<JsBackendOutput> {
    if let Some(error) = compiler.take_shadow_error() {
        return Err(error);
    }
    // lam_compile_main.ml reports a primitive's Location error before the
    // fatal-warnings check, as the file compile does.
    if let Some(diagnostic) = compiler.take_diagnostic() {
        let Some(diagnostic_loc) = diagnostic.loc else {
            return Err(LocationRetry::Diagnostic.into());
        };
        let filename = options.source_filename.as_deref().unwrap_or("_none_");
        return Err(UserDiagnostic::new(
            format_compiler_error_report_from_location(
                &read_in_process_source(filename),
                filename,
                &diagnostic_loc,
                &diagnostic.message,
            ),
            2,
        )
        .into());
    }
    let module_path_resolver = compiler
        .take_module_path_resolver()
        .expect("lambda compiler retained module path resolver");
    let cmj_export_constants = compiler.take_cmj_export_constants();
    let cmj_export_arities = compiler.take_cmj_export_arities();
    let cmj_export_lambdas = compiler.take_cmj_export_lambdas();
    let lam_locs = compiler.take_lam_locs();
    Ok((
        program,
        module_path_resolver,
        cmj_export_constants,
        cmj_export_arities,
        cmj_export_lambdas,
        lam_locs,
    ))
}

#[allow(clippy::too_many_arguments)]
fn compile_js_program_for_output(
    lowered_lambda: &crate::lambda::arena::LamProgram,
    flat_make_paths: &[crate::lambda::FlatMakePath],
    possible_required_modules: &AHashSet<ModuleId>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    output_module_format: Option<ModuleFormat>,
    persistent_env: Option<PersistentEnv>,
    jsx_preserve: bool,
    cross_module_inline: bool,
    lam_locs: &crate::lambda::LamLocTable,
) -> Result<JsBackendOutput> {
    let _span = info_span!(
        "compiler.js_backend",
        module = options.module_name.as_deref().unwrap_or(""),
        owned = false,
        possible_required_modules = possible_required_modules.len()
    )
    .entered();
    let mut compiler = js_backend_compiler(
        flat_make_paths.to_vec(),
        possible_required_modules,
        options,
        output_path,
        output_module_format,
        persistent_env,
        jsx_preserve,
        cross_module_inline,
        lam_locs.clone(),
    );
    // `possible_required_modules` already holds the modules of the lowered
    // program (collected at the pre-JS boundary).
    let program = compile_with_lower_check(
        &mut compiler, lowered_lambda.arena.clone(), lowered_lambda.root,
        possible_required_modules.clone(), options, jsx_preserve,
        options.source_filename.as_deref().unwrap_or("_none_"),
    )?;
    finish_js_backend(compiler, program, options)
}

/// Single-target variant that consumes the lowered lambda. The pre-JS result
/// already collected the modules of this lambda into
/// `possible_required_modules` (see
/// `compile_preprocessed_structure_in_process_until_js`).
#[allow(clippy::too_many_arguments)]
fn compile_js_program_for_output_owned(
    lowered_lambda: crate::lambda::arena::LamProgram,
    flat_make_paths: Vec<crate::lambda::FlatMakePath>,
    possible_required_modules: AHashSet<ModuleId>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    output_module_format: Option<ModuleFormat>,
    persistent_env: Option<PersistentEnv>,
    jsx_preserve: bool,
    cross_module_inline: bool,
    lam_locs: crate::lambda::LamLocTable,
) -> Result<JsBackendOutput> {
    let _span = info_span!(
        "compiler.js_backend",
        module = options.module_name.as_deref().unwrap_or(""),
        owned = true,
        possible_required_modules = possible_required_modules.len(),
        precomputed_possible_required_modules = true
    )
    .entered();
    let mut compiler = js_backend_compiler(
        flat_make_paths,
        &possible_required_modules,
        options,
        output_path,
        output_module_format,
        persistent_env,
        jsx_preserve,
        cross_module_inline,
        lam_locs,
    );
    let program = compile_with_lower_check(
        &mut compiler, lowered_lambda.arena, lowered_lambda.root,
        possible_required_modules, options, jsx_preserve,
        options.source_filename.as_deref().unwrap_or("_none_"),
    )?;
    finish_js_backend(compiler, program, options)
}

/// Compile a parsed and preprocessed implementation in process to JavaScript,
/// type checking it against the units in `registry`.
pub fn compile_preprocessed_structure_in_process(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
) -> Result<InProcessCompileResult> {
    compile_preprocessed_structure_in_process_with_signature_hook(
        arena,
        structure,
        filename,
        module_name,
        options,
        registry,
        has_interface,
        None,
        None,
        None,
        None,
    )
}

/// [`compile_preprocessed_structure_in_process`] with build-system hooks:
/// `signature_ready` receives the unit's signature as soon as it is typed,
/// and `before_js` may return a refreshed registry once the modules the JS
/// backend can require are known.
// The arguments are the in-process compile entry point's inputs, shared
// one for one with `compile_preprocessed_structure_in_process_until_js`,
// which rewatch calls directly.
#[allow(clippy::too_many_arguments)]
pub fn compile_preprocessed_structure_in_process_with_signature_hook(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
    gentype_interface: Option<crate::gentype::main::InterfaceRead>,
    signature_ready: Option<&mut InProcessSignatureReadyHook<'_>>,
    before_js: Option<&mut InProcessBeforeJsHook<'_>>,
    fallback: Option<DerivedFallback<'_>>,
) -> Result<InProcessCompileResult> {
    let pre_js = compile_preprocessed_structure_in_process_until_js(
        arena,
        structure,
        filename,
        module_name,
        options,
        registry,
        has_interface,
        gentype_interface,
        signature_ready,
        SignaturePublicationMode::Eager,
        fallback,
    )?;

    let refreshed_registry = if let Some(hook) = before_js {
        hook(&pre_js.possible_required_modules)?
    } else {
        None
    };
    let js_registry = refreshed_registry.as_ref().unwrap_or(registry);
    finish_preprocessed_structure_in_process_from_js_boundary(pre_js, options, js_registry)
}

/// A fresh type context with the stamp counter where OCaml's starts.
/// Cost: one context allocation/setup per unit attempt.
fn fresh_type_context() -> TypeContext {
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    TypeContext::new(std::sync::Arc::new(id_gen))
}

/// The type-checking context and initial environment an in-process
/// implementation or interface is typed in: the registry's units are the persistent
/// environment, Pervasives (and `-open`s) opened as `Res_compmisc.initial_env`
/// does (res_compmisc.ml:56-62). The environment is an error when an `-open`
/// module cannot be found; report it like a type error of the unit.
fn in_process_type_check_context<'a>(
    type_ctx: &'a TypeContext,
    unit: &CheckUnit<'a>,
    arena: &'a ParseArena,
    mode: crate::types::context::CheckMode,
) -> (TypeCheckContext<'a>, crate::types::typemod::TypeModResult<Env>) {
    let CheckUnit { options, registry, module_name, file_config,
        frontend_warning_specs, .. } = *unit;
    type_ctx.set_explain_mode(mode);
    let effective_options = file_config.apply(options);
    let options = &*effective_options;
    let mut tctx = TypeCheckContext::new(type_ctx, arena);
    tctx.experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
    tctx.transparent_modules = options.transparent_modules;
    apply_warning_options(&mut tctx, options);
    // Ppx_entry.rewrite_* (ppx_entry.ml:28, 47) applies the leading warning
    // attributes; compiling a preprocessed `.ast` does not run it again.
    if !options.frontend_already_reported {
        apply_leading_warning_attribute_options(&mut tctx, frontend_warning_specs);
    }
    apply_file_config_warning_options(&mut tctx, file_config);
    let mut pers_env = registry.map_or_else(PersistentEnv::new, PersistentEnv::from_registry);
    pers_env.set_visible_package_roots(options.visible_package_roots.clone());
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    type_ctx.set_load_paths_shared(load_path.clone());
    pers_env.set_load_path_shared(load_path, load_path_display);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_experimental_let_unwrap(options.experimental_let_unwrap);
    pers_env.set_jsx_module(options.jsx_module.clone());
    pers_env.set_nopervasives(options.nopervasives);
    pers_env.set_compiling_module(module_name.map(str::to_owned));
    tctx.set_persistent_env(pers_env);
    let env = initial_type_env(
        &mut tctx,
        &file_config.open_modules(options),
        file_config.nopervasives(options),
        module_name,
    );
    (tctx, env)
}

/// Borrowed inputs prepared once per unit, not passed down a node walk.
/// Cost: copying 80 bytes on 64-bit targets; no allocation.
#[derive(Clone, Copy)]
struct CheckUnit<'a> {
    filename: &'a str,
    options: &'a CompilerOptions,
    registry: Option<&'a ModuleRegistry>,
    module_name: Option<&'a str>,
    file_config: &'a FileConfigOverrides,
    frontend_warning_specs: &'a [ppx::WarningAttributeSpec],
    derived_plans: bool,
    mode: crate::types::context::CheckMode,
}

/// The syntax one attempt of a unit is checked from: the unit's first tree,
/// or its general form once a plan could not be used. Cost: three words
/// copied per attempt, never per node.
struct UnitSyntax<'a, S> {
    arena: &'a ParseArena,
    tree: &'a S,
    /// See [`CompilerOptions::warning_locations`]: the located parse of
    /// this syntax.
    warning_locations: Option<&'a WarningLocations>,
}

impl<S> Clone for UnitSyntax<'_, S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S> Copy for UnitSyntax<'_, S> {}

impl<'a, S> UnitSyntax<'a, S> {
    /// A first tree with the options' located parse. O(1).
    fn new(arena: &'a ParseArena, tree: &'a S, options: &'a CompilerOptions) -> Self {
        Self { arena, tree, warning_locations: options.warning_locations.as_ref() }
    }
}

/// Settings of one whole-unit attempt, owned by the unit's single attempt
/// loop ([`type_structure_two_modes`]): every retry reason changes these and
/// nothing else. Cost: two bytes copied per attempt, never per node.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct CheckAttempt {
    mode: crate::types::context::CheckMode,
    /// The checker may discharge the plans of derived items. Cleared, once,
    /// when a plan could not be used: the attempt after it runs on the
    /// unit's general syntax.
    derived_plans: bool,
}

/// Why an attempt is discarded and the unit checked again.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AttemptRetry {
    /// A plan of a derived item could not be used.
    DerivedFallback,
    /// A Success attempt failed: explain the failure.
    Explain,
}

impl CheckAttempt {
    /// The settings of the attempt after one discarded for `reason`, or
    /// `None` when that reason cannot apply again. Each reason applies at
    /// most once per unit, so a unit has at most three attempts. O(1).
    fn after(self, reason: AttemptRetry) -> Option<Self> {
        use crate::types::context::CheckMode;
        match reason {
            AttemptRetry::DerivedFallback if self.derived_plans => Some(Self { derived_plans: false, ..self }),
            AttemptRetry::Explain if self.mode == CheckMode::Success => Some(Self { mode: CheckMode::Explain, ..self }),
            AttemptRetry::DerivedFallback | AttemptRetry::Explain => None,
        }
    }
}

/// Output is private until the attempt crosses its publication boundary.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum AttemptPublication { Pending, Committed }

/// One byte buffer per unit, allocated only when there are reports to print.
/// This is not stored per node or passed down a checker walk.
struct AttemptOutput {
    stderr: Vec<u8>,
    publication: AttemptPublication,
    mode: crate::types::context::CheckMode,
    signature_report: Option<Box<crate::cmi::signature_check::PreparedReport>>,
    #[cfg(feature = "test-hooks")]
    force_unexplained_failure: bool,
}

impl AttemptOutput {
    /// O(1), no allocation until the first diagnostic or requested dump.
    fn new(mode: crate::types::context::CheckMode) -> Self {
        Self {
            stderr: Vec::new(), publication: AttemptPublication::Pending, mode, signature_report: None,
            #[cfg(feature = "test-hooks")]
            force_unexplained_failure: false,
        }
    }

    /// No allocation on the default path. Check mode retains report bytes until
    /// publication; a mismatch still participates in pre-publication validation.
    fn signature_report(&mut self, report: Option<crate::cmi::signature_check::PreparedReport>) -> Result<()> {
        let Some(report) = report else { return Ok(()) };
        if self.publication == AttemptPublication::Committed {
            return report.publish();
        }
        let result = report.validate();
        self.signature_report = Some(Box::new(report));
        result
    }

    /// O(report bytes), only on a diagnostic path. Discarded reports are never emitted.
    fn warnings(&mut self, arena: &ParseArena, source: &str, filename: &str, warnings: &[TypeCoreWarning]) {
        if !warnings.is_empty() {
            self.stderr.extend_from_slice(format_type_warnings(arena, source, filename, warnings).as_bytes());
        }
    }

    /// O(1) without diagnostics; otherwise O(report bytes). Called before the
    /// first externally visible artifact/signature, after every fallible check.
    fn publish(&mut self, ctx: &TypeContext) -> Result<()> {
        if self.publication == AttemptPublication::Pending {
            // Test-only: fail after private freezing and continuation work,
            // before anything can escape. Explain then checks the same unit.
            #[cfg(feature = "test-hooks")]
            if self.force_unexplained_failure {
                ctx.note_unexplained_unify_failure();
                self.force_unexplained_failure = false;
            }
            if self.mode == crate::types::context::CheckMode::Success && ctx.unexplained_unify_failure() {
                return Err(anyhow!("unit requires an explanatory check"));
            }
            ctx.keep_attempt_counters();
            self.publication = AttemptPublication::Committed;
        }
        if let Some(report) = self.signature_report.take() {
            report.publish()?;
        }
        if !self.stderr.is_empty() {
            let mut stderr = std::io::stderr();
            let _ = std::io::Write::write_all(&mut stderr, &self.stderr);
            let _ = std::io::Write::flush(&mut stderr);
            self.stderr.clear();
        }
        Ok(())
    }
}

/// The names check of `RESCRIPT_CHECKER=both` (CHECKER_REWRITE.md, "R4 as
/// designed", decision 4): with `Both`, `type_check` runs under
/// `tc::scope_trace::capture` and every lookup by name the old environment
/// made is replayed on a new `tc::scope::Scopes`; the first lookup it
/// answers with another item fails the unit with the mismatch and the
/// unit's name. With `Old` or `New` no capture starts. Builds with debug
/// assertions only. Cost: `type_check`'s plus, under `Both`, the replay
/// (O(events x depth of the version tree + lookups x items of the trace));
/// O(1) otherwise.
#[cfg(debug_assertions)]
fn names_replayed<T>(
    choice: CheckerChoice,
    unit: &str,
    type_check: impl FnOnce() -> T,
) -> std::result::Result<T, String> {
    use crate::tc::scope_oracle::{OnScopes, replay};
    if choice != CheckerChoice::Both {
        return Ok(type_check());
    }
    let (checked, events) = crate::tc::scope_trace::capture(type_check);
    match replay(&events, &mut OnScopes::new()) {
        Ok(done) => {
            log::debug!(target: "rescript_checker", "tc-names-replayed {unit} {}", done.lookups);
            Ok(checked)
        }
        Err(mismatch) => Err(format!("{unit}: the names replay differs from the old checker: {mismatch:?}")),
    }
}

/// The one attempt loop of a unit: check it with diagnostic-only snapshots
/// elided, continue on its general syntax when a plan of a derived item
/// cannot be used, and explain it if the check fails. Every retry reason
/// changes the loop's [`CheckAttempt`] settings, so the reasons compose: a
/// unit that falls back keeps its check mode, and one that then fails is
/// explained once, on its general syntax. Cost: one check on success, one
/// more for a fallback (plus the frontend run `fallback` makes) and one
/// more to explain a failure; O(1) dispatch.
///
/// `fallback` makes the unit's general syntax; without it a fallback fails
/// the compile with [`DerivedRetry`]. The continuation validates the checked
/// unit while its output stays private. Its publication boundary commits the
/// attempt before external artifacts or callbacks become observable; all
/// errors before that boundary get Explain. Returning the owned context
/// separately keeps tooling's typed handles valid without a self-referential
/// context or retaining the discarded type graph.
fn type_structure_two_modes<S, T, R>(
    unit: CheckUnit<'_>,
    first: UnitSyntax<'_, S>,
    fallback: Option<&dyn Fn() -> Result<GeneralSyntax<S>>>,
    check: impl for<'a> Fn(&mut TypeCheckContext<'a>, &Env, UnitSyntax<'a, S>)
        -> crate::types::typemod::TypeModResult<T>,
    mut finish: impl for<'a> FnMut(&'a TypeContext, TypeCheckContext<'a>,
        crate::types::typemod::TypeModResult<(T, Env)>, UnitSyntax<'a, S>, &mut AttemptOutput) -> Result<R>,
) -> (TypeContext, Result<R>) {
    use crate::types::context::CheckMode;
    let CheckUnit { filename, options, .. } = unit;
    offer_unit_to_checker(options.checker, filename);
    let mut attempt = CheckAttempt { mode: unit.mode, derived_plans: unit.derived_plans };
    // Owned here once made, so every later attempt borrows it.
    let mut general: Option<GeneralSyntax<S>> = None;
    loop {
        let syntax = match &general {
            Some(general) => UnitSyntax {
                arena: &general.arena,
                tree: &general.tree,
                warning_locations: general.warning_locations.as_ref(),
            },
            None => first,
        };
        crate::perf_counters::record_check_attempt();
        let type_ctx = fresh_type_context();
        type_ctx.set_location_namespace(&options.location_identity(filename));
        type_ctx.defer_attempt_counters();
        let type_check = || {
            let (mut tctx, env) = crate::timing::measure(crate::timing::Phase::EnvSetup, || {
                in_process_type_check_context(&type_ctx, &unit, syntax.arena, attempt.mode)
            });
            // Census ownership follows the syntax, including its general form
            // after fallback; it is not conditional on using derived plans.
            tctx.derived_census = syntax.arena.derived_census.clone();
            let typed = crate::timing::measure(crate::timing::Phase::Typecheck, || {
                env.and_then(|env| check(&mut tctx, &env, syntax).map(|typed| (typed, env)))
            });
            (tctx, typed)
        };
        #[cfg(not(debug_assertions))]
        let (tctx, typed) = type_check();
        #[cfg(debug_assertions)]
        let (tctx, typed) = match names_replayed(options.checker, unit.module_name.unwrap_or(filename), type_check) {
            Ok(checked) => checked,
            Err(mismatch) => return (type_ctx, Err(anyhow::Error::msg(mismatch))),
        };
        if tctx.derived_fallback {
            // Dropped in dependency order: nothing of this attempt survives.
            drop(typed);
            drop(tctx);
            let (Some(next), Some(fallback)) = (attempt.after(AttemptRetry::DerivedFallback), fallback) else {
                return (type_ctx, Err(DerivedRetry.into()));
            };
            // The frontend's own errors were reported with the first tree;
            // one here is the compile's error, not a check to explain.
            match fallback() {
                Ok(syntax) => general = Some(syntax),
                Err(error) => return (type_ctx, Err(error)),
            }
            drop(type_ctx);
            attempt = next;
            continue;
        }
        if attempt.mode == CheckMode::Success
            && (typed.is_err() || type_ctx.unexplained_unify_failure())
        {
            // Dropped in dependency order before constructing the next attempt.
            drop(typed);
            drop(tctx);
            drop(type_ctx);
            crate::perf_counters::record_explain_rerun();
            attempt = attempt.after(AttemptRetry::Explain).expect("a Success attempt can be explained");
            continue;
        }
        let mut reports = AttemptOutput::new(attempt.mode);
        #[cfg(feature = "test-hooks")]
        {
            reports.force_unexplained_failure = attempt.mode == CheckMode::Success
                && std::env::var("RESCRIPT_TEST_DISCARD_UNIT").ok().is_some_and(|unit| {
                    FsPath::new(filename).file_stem().and_then(|s| s.to_str()) == Some(unit.as_str())
                });
        }
        let output = finish(&type_ctx, tctx, typed, syntax, &mut reports);
        // Location retries request another parse, not an explanation of this
        // check. Leave its reports and counters private; the located compile
        // will explain any actual failure on its own syntax.
        if reports.publication == AttemptPublication::Pending
            && output.as_ref().is_err_and(|error| error.is::<LocationRetry>())
        {
            return (type_ctx, output);
        }
        if reports.publication == AttemptPublication::Pending && attempt.mode == CheckMode::Success
            && (output.is_err() || type_ctx.unexplained_unify_failure())
        {
            drop(output);
            drop(type_ctx);
            crate::perf_counters::record_explain_rerun();
            attempt = attempt.after(AttemptRetry::Explain).expect("a Success attempt can be explained");
            continue;
        }
        let output = reports.publish(&type_ctx).and(output);
        // Common final context use for all six entry points, after their
        // continuation (including lowering, GenType and signature hooks).
        // One Cell read per published Success unit, never per node.
        if reports.publication == AttemptPublication::Committed && attempt.mode == CheckMode::Success {
            assert!(!type_ctx.unexplained_unify_failure(),
                "{filename}: unexplained unification failure after Success publication");
        }
        return (type_ctx, output);
    }
}

/// The typed tree of one module, type-checked on demand for editor tooling,
/// which works on it in memory.
pub struct ToolingTypedModule {
    /// The type graph the typed tree refers to.
    pub type_ctx: TypeContext,
    /// The typed tree, or the type error.
    pub typed: ToolingTyped,
    /// Node storage of `typed`.
    pub typed_arena: crate::types::typedtree::TypedArena,
    /// Whether the file's `@@config` leaves binary annotations on: with
    /// `-bs-no-bin-annot` OCaml writes no `.cmt` or `.cmti` for it.
    pub binary_annotations: bool,
}

/// What type-checking a module for editor tooling produced.
pub enum ToolingTyped {
    /// The typed structure of an implementation.
    Implementation(crate::types::typedtree::Structure),
    /// The typed signature of an interface.
    Interface(crate::types::typedtree::TypedSignature),
    /// The compiler's report of a module that does not type-check.
    Failed(String),
}

/// Type-check an implementation for editor tooling, as the in-process build
/// does (`compile_preprocessed_structure_in_process_until_js`), keeping the
/// typed tree instead of compiling it further.
pub fn typecheck_structure_for_tooling(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
) -> ToolingTypedModule {
    let file_config = extract_file_config_from_structure(structure, arena);
    // The frontend raised on any payload these cannot read.
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_attribute_specs(structure, arena)
            .expect("the frontend read these attributes");
    let (type_ctx, output) = type_structure_two_modes(
        CheckUnit { filename, options, registry: Some(registry),
            module_name: Some(module_name), file_config: &file_config,
            frontend_warning_specs: &frontend_warning_specs, derived_plans: true,
            mode: crate::types::context::CheckMode::from_env() },
        // Tooling parses derived code as syntax: nothing to fall back from.
        UnitSyntax::new(arena, structure, options),
        None,
        |tctx, env, syntax| type_structure(tctx, env, syntax.arena, syntax.tree),
        |type_ctx, mut tctx, result, UnitSyntax { arena, .. }, _attempt_output| {
        let typed = match result {

            Ok(((typed_structure, _final_env), env)) => {
                // typemod.ml:1742-1758: an implementation is checked against
                // its interface, which records the values the interface
                // exports (`Cmt_format.record_value_dependency`). The build
                // reported a mismatch already.
                if has_interface {
                    drop(check_compunit_inclusion_for_errors(
                        &mut tctx,
                        &env,
                        &typed_structure,
                        filename,
                        &|| read_in_process_source(filename),
                        filename,
                        options.current_unit_name().as_deref(),
                    ));
                }
                ToolingTyped::Implementation(typed_structure)
            }
            Err(e) => {
                let source = read_in_process_source(filename);
                let report = match tctx
                    .persistent_env
                    .as_ref()
                    .and_then(|env| env.last_error())
                {
                    Some(error) => persistent_env_error_to_anyhow(error, filename),
                    None => type_mod_error_to_anyhow(e, type_ctx, arena, &source, filename, false),
                };
                ToolingTyped::Failed(format!("{report:#}"))
            }
        };
        Ok((typed, tctx.take_typed_arena()))
        },
    );
    let (typed, typed_arena) = output.expect("tooling represents errors as ToolingTyped::Failed");
    ToolingTypedModule {
        type_ctx,
        typed,
        typed_arena,
        binary_annotations: !file_config.no_bin_annot,
    }
}

/// Type-check an interface for editor tooling, as the in-process build does
/// (`typecheck_preprocessed_signature_in_process`), keeping the typed tree.
pub fn typecheck_signature_for_tooling(
    arena: &crate::parse_arena::ParseArena,
    signature: &Signature,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> ToolingTypedModule {
    let file_config = extract_file_config_from_signature(signature, arena);
    // The frontend raised on any payload these cannot read.
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_signature_attribute_specs(signature, arena)
            .expect("the frontend read these attributes");
    let (type_ctx, output) = type_structure_two_modes(
        CheckUnit { filename, options, registry: Some(registry),
            module_name: Some(module_name), file_config: &file_config,
            frontend_warning_specs: &frontend_warning_specs, derived_plans: true,
            mode: crate::types::context::CheckMode::from_env() },
        UnitSyntax::new(arena, signature, options),
        None,
        |tctx, env, syntax| transl_signature(tctx, env, syntax.arena, syntax.tree),
        |type_ctx, mut tctx, result, UnitSyntax { arena, .. }, _attempt_output| {
        let typed = match result {

            Ok((typed_signature, _env)) => ToolingTyped::Interface(typed_signature),
            Err(e) => {
                let source = read_in_process_source(filename);
                let report = match tctx
                    .persistent_env
                    .as_ref()
                    .and_then(|env| env.last_error())
                {
                    Some(error) => persistent_env_error_to_anyhow(error, filename),
                    None => type_mod_error_to_anyhow(e, type_ctx, arena, &source, filename, false),
                };
                ToolingTyped::Failed(format!("{report:#}"))
            }
        };
        Ok((typed, tctx.take_typed_arena()))
        },
    );
    let (typed, typed_arena) = output.expect("tooling represents errors as ToolingTyped::Failed");
    ToolingTypedModule {
        type_ctx,
        typed,
        typed_arena,
        binary_annotations: !file_config.no_bin_annot,
    }
}

/// Type check a preprocessed implementation and lower it to Lambda, stopping
/// before the JS backend, which needs dependencies' `.cmj` metadata; finish
/// with `finish_preprocessed_structure_in_process_from_js_boundary`.
/// `gentype_ignore_interface` (the `.resi` has `@@genType.ignoreInterface`)
/// runs GenType on the implementation even though it has an interface.
// Rewatch's in-process scheduler calls this entry point with each argument
// coming from a different part of its build state.
#[allow(clippy::too_many_arguments)]
pub fn compile_preprocessed_structure_in_process_until_js(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
    gentype_interface: Option<crate::gentype::main::InterfaceRead>,
    signature_ready: Option<&mut InProcessSignatureReadyHook<'_>>,
    publication: SignaturePublicationMode,
    fallback: Option<DerivedFallback<'_>>,
) -> Result<InProcessPreJsCompileResult> {
    let unit = UntilJs {
        arena,
        structure,
        filename,
        module_name,
        registry,
        has_interface,
        publication,
        fallback,
    };
    // O(1): one comparison per unit; only `check` compiles a unit twice.
    if options.derived_path == DerivedPath::Check && arena.plans().item_count() > 0 {
        return derived_check::until_js(&unit, options, gentype_interface, signature_ready);
    }
    compile_until_js(&unit, options, gentype_interface, signature_ready)
}

/// The unit an in-process compile works on.
#[derive(Clone, Copy)]
struct UntilJs<'a> {
    arena: &'a crate::parse_arena::ParseArena,
    structure: &'a Structure,
    filename: &'a str,
    module_name: &'a str,
    registry: &'a ModuleRegistry,
    has_interface: bool,
    publication: SignaturePublicationMode,
    fallback: Option<DerivedFallback<'a>>,
}

/// [`compile_preprocessed_structure_in_process_until_js`] for one tree of
/// the unit.
fn compile_until_js(
    unit: &UntilJs<'_>,
    options: &CompilerOptions,
    gentype_interface: Option<crate::gentype::main::InterfaceRead>,
    mut signature_ready: Option<&mut InProcessSignatureReadyHook<'_>>,
) -> Result<InProcessPreJsCompileResult> {
    let UntilJs {
        arena,
        structure,
        filename,
        module_name,
        registry,
        has_interface,
        publication,
        fallback,
    } = *unit;
    if !arena.stores_locations()
        && (options.source_map != crate::js_ir::source_map::SourceMapMode::None
            || options.capture_intermediates
            || options.dumps.iter().any(|kind| kind.needs_locations()))
    {
        return Err(LocationRetry::Output.into());
    }
    let _span = info_span!(
        "compiler.in_process_compile",
        module = %module_name,
        file = %filename,
        has_interface,
        skip_js_render = options.skip_js_render,
        js_targets = options.js_output_targets.len()
    )
    .entered();
    let census_timing = options.derived_census.as_ref().map(|_| crate::timing::ThreadTimingGuard::start());
    let file_directives = {
        let _phase = info_span!("compiler.directives").entered();
        extract_file_directives_from_structure(structure, arena)?
    };
    let file_config = extract_file_config_from_structure(structure, arena);
    // The rest of the compile sees the `@@config` flags applied after the
    // command line (rescript_compiler_driver.ml:539-557).
    let effective_options = file_config.apply(options);
    let options = &*effective_options;
    // The frontend raised on any payload these cannot read.
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_attribute_specs(structure, arena)
            .expect("the frontend read these attributes");

    log::debug!(
        "[compile_source_in_process] {} type-check start",
        module_name
    );
    // Read source only when retained diagnostics need it.
    let source_cell = std::cell::OnceCell::new();
    let source = || -> &str { source_cell.get_or_init(|| read_in_process_source(filename)) };
    let result = type_structure_two_modes(
        CheckUnit { filename, options, registry: Some(registry),
            module_name: Some(module_name), file_config: &file_config,
            frontend_warning_specs: &frontend_warning_specs,
            derived_plans: options.derived_path.plans_off().is_none(),
            mode: crate::types::context::CheckMode::from_env() },
        UnitSyntax::new(arena, structure, options),
        fallback,
        |tctx, env, syntax| type_structure(tctx, env, syntax.arena, syntax.tree),
        |type_ctx, mut tctx, typed, syntax, attempt_output| {
    // A unit that fell back is finished from its general syntax.
    let UnitSyntax { arena, tree: structure, warning_locations } = syntax;
    let ((typed_structure, final_env), env) = match typed {
        Ok(result) => result,
        Err(e) => {
            // As in the file compile: the warnings reported so far precede
            // the error report.
            tctx.drain_open_slot_uses();
            let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            if let Some(error) = tctx
                .persistent_env
                .as_ref()
                .and_then(|persistent_env| persistent_env.last_error())
            {
                return Err(prefix_diagnostic(
                    &warnings,
                    persistent_env_error_to_anyhow(error, filename),
                ));
            }
            return Err(prefix_diagnostic(
                &warnings,
                type_mod_error_to_anyhow(
                    e,
                    type_ctx,
                    arena,
                    source(),
                    filename,
                    suppress_info_style,
                ),
            ));
        }
    };
    tctx.drain_open_slot_uses();
    // Debugging aid: `RESCRIPT_DUMP_TYPED_SEXP=<Module>` prints the
    // in-process typed tree of that module like `bsc -dtyped-sexp`.
    static DUMP_TYPED_SEXP_MODULE: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    if DUMP_TYPED_SEXP_MODULE
        .get_or_init(|| std::env::var("RESCRIPT_DUMP_TYPED_SEXP").ok())
        .as_deref()
        == Some(module_name)
    {
        let _ = print_typed_structure(
            arena,
            type_ctx,
            &tctx.typed,
            &typed_structure,
            &mut attempt_output.stderr,
        );
    }

    let mut inferred_implementation_coercion = None;
    // Interface matching, non-generalizable checks and signature
    // normalization are part of OCaml's `type_implementation`
    // (compiler/ml/typemod.ml:1740-1788); account for them as typecheck.
    let signature_prepare_start = crate::timing::enabled().then(std::time::Instant::now);
    let mut published_signature = {
        let _phase = info_span!("compiler.signature_prepare").entered();
        if has_interface {
            apply_moregen_constraints(
                &mut tctx,
                type_ctx,
                &typed_structure,
                options,
                has_interface,
            );
        }

        let simple_signature =
            crate::types::includemod::simplify_signature(&typed_structure.str_type);
        if !has_interface {
            // typemod.ml `type_implementation_more`: `check_js_names
            // ~toplevel:true simple_sg` before the inferred-signature inclusion.
            if let Err(e) =
                crate::types::typemod::check_js_names(type_ctx, true, &simple_signature)
            {
                if !arena.stores_locations() {
                    return Err(LocationRetry::Diagnostic.into());
                }
                let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
                let suppress_info_style =
                    !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
                return Err(prefix_diagnostic(
                    &warnings,
                    type_mod_error_to_anyhow(
                        e,
                        type_ctx,
                        arena,
                        source(),
                        filename,
                        suppress_info_style,
                    ),
                ));
            }
            let inferred_inclusion = coerce_to_inferred_signature(
                type_ctx,
                &env,
                filename,
                &typed_structure.str_type,
                &simple_signature,
            );
            // A payload reader's error escapes the inclusion (includecore.ml:45).
            let inferred_inclusion =
                crate::types::includemod::escaped(type_ctx, inferred_inclusion).map_err(|e| {
                    in_process_typed_unit_error(
                        e.into(),
                        type_ctx,
                        arena,
                        &source,
                        filename,
                        &tctx.warnings,
                    )
                })?;
            inferred_implementation_coercion = Some(
                inferred_inclusion
                    .map_err(|e| anyhow!("Inferred signature inclusion failed: {e:?}"))?,
            );
            if let Err(e) = crate::types::typemod::check_nongen_schemes(
                type_ctx,
                &final_env,
                &simple_signature,
            ) {
                let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
                let suppress_info_style =
                    !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
                return Err(prefix_diagnostic(
                    &warnings,
                    type_mod_error_to_anyhow(
                        e,
                        type_ctx,
                        arena,
                        source(),
                        filename,
                        suppress_info_style,
                    ),
                ));
            }
            normalize_signature(type_ctx, &final_env, &simple_signature);
        }

        // `Env.save_signature` (typemod.ml:1779-1788) renames the bound
        // identifiers of a copy of the signature (env.ml:1886-1892). In-process
        // builds write no `.cmi`, but the copy still takes its stamps.
        if !has_interface {
            saved_signature_copy(type_ctx, &simple_signature);
        }

        simple_signature
    };
    if let Some(start) = signature_prepare_start {
        crate::timing::record(crate::timing::Phase::Typecheck, start.elapsed());
    }
    // typemod.ml:1742-1758: with an interface, the implementation is checked
    // against it (marking the included declarations used) before the delayed
    // checks, as the file compile does.
    let mut interface_inclusion = None;
    if has_interface {
        match check_compunit_inclusion_for_errors(
            &mut tctx,
            &env,
            &typed_structure,
            filename,
            &|| source().to_string(),
            filename,
            options.current_unit_name().as_deref(),
        ) {
            Ok(inclusion) => interface_inclusion = inclusion,
            Err(error) => {
                let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
                return Err(prefix_diagnostic(&warnings, error));
            }
        }
    }
    // typemod.ml:1769-1776 forces the delayed usage checks before Lambda
    // translation, as the file compile does.
    tctx.flush_value_usage_checks();
    let mut located_warnings = None;
    if !place_location_free_warnings(arena, warning_locations, &mut located_warnings, &mut tctx.warnings) {
        return Err(LocationRetry::Warning.into());
    }
    let post_type_warning_start = tctx.warnings.len();
    // js_implementation.ml:148-156 prints `-dtyped-sexp` here, before the
    // signature is saved: `register_in_memory_signature` below finalizes the
    // current unit's type paths in place (`allOptRec` becomes
    // `Current.allOptRec`), which must not show in the dump.
    let mut dumps: Vec<(DumpKind, String)> = Vec::new();
    for kind in [DumpKind::TypedTree, DumpKind::TypedTreeLocs] {
        if options.dumps.contains(&kind) {
            let mut buf = Vec::new();
            let _ = if kind == DumpKind::TypedTree {
                crate::types::sexp_typedtree::print_typed_structure(
                    arena,
                    type_ctx,
                    &tctx.typed,
                    &typed_structure,
                    &mut buf,
                )
            } else {
                crate::types::sexp_typedtree::print_typed_structure_with_locs(
                    arena,
                    type_ctx,
                    &tctx.typed,
                    &typed_structure,
                    &mut buf,
                )
            };
            dumps.push((kind, latin1_dump(buf)));
        }
    }

    let unit_reads = if options.collect_unit_reads {
        crate::types::unit_reads::structure_reads(
            type_ctx,
            &tctx.typed,
            &typed_structure,
            &options.open_modules,
        )
    } else {
        Vec::new()
    };

    // OCaml saves the inferred `.cmi` only in the no-interface branch before
    // Lambda translation mutates any shared type nodes
    // (compiler/ml/typemod.ml:1768-1788; translmod.ml:267). With a `.resi`,
    // the already-published interface remains the target signature for
    // `Translmod.transl_implementation`; do not replace it with the
    // implementation signature or the export coercion becomes identity.
    let (mut pers_struct, persistent_env_after_signature) = if has_interface {
        (None, tctx.persistent_env.take().unwrap_or_else(PersistentEnv::new))
    } else {
        let _phase = info_span!("compiler.signature_extract").entered();
        let signature_publish_start = crate::timing::enabled().then(std::time::Instant::now);
        let mut internal_env = tctx
            .persistent_env
            .take()
            .unwrap_or_else(PersistentEnv::new);

        let mut signature_for_save = if signature_ready.is_some() {
            std::mem::take(&mut published_signature)
        } else {
            published_signature.clone()
        };
        if !options.keep_locs {
            strip_saved_signature_locations(&mut signature_for_save);
        }
        // OCaml compiler/ml/env.ml:1949-1952 saves a fresh
        // `Subst.signature (Subst.for_saving Subst.identity) sg` copy before
        // installing the persistent structure. Keep Rust's GenType raw-signature
        // cache on its own type nodes too; `register_in_memory_signature`
        // finalizes component lookup paths in-place, and sharing those refs
        // would leak qualified `Current.t` paths back into the CMT-shaped
        // signature that compiler/gentype/TranslateStructure.ml:174-183 reads
        // through Env.scrape_alias.
        let current_raw_sig = std::sync::Arc::new(
            crate::types::typecore::copy_lookup_signature_for_subst(&signature_for_save, type_ctx),
        );
        // `save_signature` saves a copy (`Subst.signature (Subst.for_saving
        // Subst.identity) sg`, env.ml:1949-1952): finalizing the saved paths
        // (`t` -> `Current.t`) must not reach the typed tree's type nodes,
        // which Lambda translation reads next (Typeopt expansions).
        let signature_for_save =
            crate::types::typecore::copy_lookup_signature_for_subst(&signature_for_save, type_ctx);
        // typemod.ml:1825: `Builtin_attributes.deprecated_of_str ast`, raising
        // where `string_of_payload` raises.
        let deprecated =
            crate::types::typemod::deprecated_of_str(arena, structure).map_err(|error| {
                in_process_typed_unit_error(
                    payload_type_error(error),
                    type_ctx,
                    arena,
                    &source,
                    filename,
                    &tctx.warnings,
                )
            })?;
        if type_ctx.compiler_counters_enabled() {
            crate::perf_counters::census_exported_signature(
                type_ctx,
                module_name,
                &current_raw_sig,
            );
        }
        if options.dumps.contains(&DumpKind::Sig) {
            dumps.push(canonical_signature_dump(
                type_ctx,
                module_name,
                &current_raw_sig,
                deprecated.as_deref(),
                arena,
            ));
        }
        internal_env.register_in_memory_signature(
            module_name,
            signature_for_save,
            filename,
            deprecated,
            Vec::new(),
            type_ctx,
        );
        // OCaml saves the current unit into the persistent table before
        // lambda translation (compiler/ml/typemod.ml:1779-1788). That save
        // also installs `ps_sig` for later lazy component forcing
        // (compiler/ml/env.ml:1960-1977). In-process builds do not write/read
        // the `.cmi`, so keep the pre-finalized current signature in the
        // TypeContext raw-signature cache before hiding the transient module.
        // This preserves the OCaml split between raw `ps_sig` and later lazy
        // component substitution in compiler/ml/env.ml:669-678 and
        // compiler/ml/env.ml:1513-1530.
        type_ctx.register_gentype_raw_module_sig(module_name, current_raw_sig.clone());
        type_ctx.register_raw_module_sig(module_name, current_raw_sig);

        // Freeze the inferred signature before raw translation mutates type
        // nodes, but keep the result private until all validation has passed.
        let pers_struct = if options.publish_in_process_signature {
            let _publication_guard = crate::perf_counters::SignaturePublication::begin();
            let (signature, report) = publish_signature(&internal_env, options, module_name, filename, type_ctx, arena, publication)?;
            attempt_output.signature_report(report)?;
            signature
        } else { None };
        if let Some(start) = signature_publish_start {
            crate::timing::record(crate::timing::Phase::SignaturePublish, start.elapsed());
        }
        (pers_struct, internal_env)
    };
    tctx.persistent_env = Some(persistent_env_after_signature);

    // Neither a frozen signature nor a unit result is handed to another worker
    // until every validation that uses the checker context has completed.
    let mut publish_checked = || -> Result<_> {
        attempt_output.publish(type_ctx)?;
        if !has_interface && let Some(hook) = signature_ready.as_deref_mut() {
            hook(InProcessSignatureReady { pers_struct: pers_struct.take() })?;
        }
        Ok(pers_struct.take())
    };

    if options.check_only {
        if let Some(inclusion) = interface_inclusion {
            report_compunit_inclusion_warnings(&mut tctx, inclusion.warnings);
        }
        // The earlier typing warnings already carry located parse slots.
        // Only inclusion warnings appended since then still need placement.
        if !place_location_free_warnings(
            arena, warning_locations, &mut located_warnings,
            &mut tctx.warnings[post_type_warning_start..],
        ) {
            return Err(LocationRetry::Warning.into());
        }
        let warnings = format_type_warnings_lazy(
            located_warnings.as_ref().unwrap_or(arena),
            &source,
            filename,
            &tctx.warnings,
        );
        if type_warnings_have_errors(&tctx.warnings) {
            return Err(UserDiagnostic::new(warnings, 2).into());
        }
        let pers_struct = publish_checked()?;
        return Ok(InProcessPreJsCompileResult {
            signature: published_signature,
            pers_struct,
            warnings,
            unit_reads,
            loaded_units: tctx
                .persistent_env
                .as_ref()
                .map(PersistentEnv::loaded_units)
                .unwrap_or_default(),
            ..Default::default()
        });
    }

    // Capture typed tree sexp for the playground (only if requested).
    let typed_tree_sexp = if options.capture_intermediates {
        let mut buf = Vec::new();
        let _ = crate::types::sexp_typedtree::print_typed_structure_with_locs(
            arena,
            type_ctx,
            &tctx.typed,
            &typed_structure,
            &mut buf,
        );
        String::from_utf8_lossy(&buf).into_owned()
    } else {
        String::new()
    };

    // With a `.resi`, compiler/gentype/Paths.ml:59-85 makes the
    // implementation's compile read the `.cmti` first: what the interface
    // step read (`gentype_interface`) is raised, or selects the output, here
    // (GenTypeMain.ml:108-134). A caller that did not read it leaves the
    // output alone.
    let gentype = if !has_interface || gentype_interface.is_some() {
        process_gentype_typed_artifact_if_enabled(
            options,
            gentype_interface.clone(),
            GentypeUnit {
                annots: crate::gentype::main::TypedArtifactAnnots::Implementation(&typed_structure),
                arena,
                ta: &tctx.typed,
                type_ctx,
                source: &|| source().to_string(),
                filename,
                module_name,
            },
        )
    } else {
        None
    };
    // A GenType note quotes a location: like a warning, it needs a located
    // parse (`place_location_free_warnings`).
    if gentype.as_ref().is_some_and(|outcome| outcome.needs_locations) {
        return Err(LocationRetry::Warning.into());
    }

    let lambda_start_stamp = synchronize_lambda_start_stamp(type_ctx);

    let unit_name = options.current_unit_name().unwrap_or_default();
    let (
        (raw_arena, raw_lambda),
        raw_warnings,
        raw_diagnostic,
        raw_possible_required_modules,
        flat_make_paths,
        lam_locs,
    ) = match crate::timing::measure(crate::timing::Phase::Lambda, || {
        let _phase = info_span!("compiler.raw_lambda").entered();
        // The interface check above already computed the coercion; report
        // its inclusion warnings where the coercion is used, as before.
        let implementation_coercion = match (inferred_implementation_coercion, interface_inclusion)
        {
            (Some(coercion), _) => coercion,
            (None, Some(inclusion)) => {
                report_compunit_inclusion_warnings(&mut tctx, inclusion.warnings);
                inclusion.coercion
            }
            (None, None) => compute_raw_implementation_coercion(
                &mut tctx,
                type_ctx,
                &env,
                &typed_structure,
                options,
                has_interface,
            ),
        };
        let raw_arena = crate::raw_lambda::RawArena::for_typed_exprs(tctx.typed.expr_count());
        let mut raw_converter =
            crate::raw_lambda::convert::RawLambdaConverter::with_start_stamp_and_unit_name(
                arena,
                &tctx.typed,
                type_ctx,
                &env,
                lambda_start_stamp,
                unit_name,
                &raw_arena,
            );
        raw_converter.derived_census = tctx.derived_census.take();
        raw_converter.set_preserve_expanded_sparse_records(
            options.capture_intermediates || options.dumps.iter().any(|kind| kind.is_lambda()),
        );
        raw_converter.set_no_assert_false(options.no_assert_false);
        raw_converter.set_noassert(options.noassert);
        raw_converter.set_warning_config(tctx.warning_config.clone());
        if let Some(persistent_env) = tctx.persistent_env.clone() {
            raw_converter.set_persistent_env(persistent_env);
        }
        // An uncaught exception in Translmod (`Misc.fatal_error`) ends the
        // file compile after the warnings it already printed; report it with
        // the warnings this compile buffered.
        let raw_lambda = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            raw_converter
                .convert_structure_with_coercion(&typed_structure, &implementation_coercion)
        })) {
            Ok(raw_lambda) => raw_lambda,
            Err(payload) => return Err(payload),
        };
        // The signature `type_implementation_more` returns: the interface's,
        // or the inferred one saved for this unit above.
        let final_signature = if has_interface {
            implementation_interface_signature(
                &mut tctx.persistent_env,
                type_ctx,
                filename,
                options.current_unit_name().as_deref(),
            )
        } else {
            type_ctx.get_gentype_raw_module_sig(module_name)
        };
        let flat_make_paths = flat_make_paths_of_signature(
            &mut tctx.persistent_env,
            type_ctx,
            &final_env,
            final_signature.as_deref().map(Vec::as_slice),
        );
        raw_converter.set_flat_make_paths(&raw_lambda, flat_make_paths);
        let raw_warnings = raw_converter.take_warnings();
        let raw_diagnostic = raw_converter.take_diagnostic();
        let possible_required_modules = raw_converter.take_possible_required_modules();
        let flat_make_paths = raw_converter.take_flat_make_paths();
        let lam_locs = raw_converter.take_lam_locs();
        tctx.derived_census = raw_converter.derived_census.take();
        drop(raw_converter);
        Ok((
            (raw_arena.into_inner(), raw_lambda),
            raw_warnings,
            raw_diagnostic,
            possible_required_modules,
            flat_make_paths,
            lam_locs,
        ))
    }) {
        Ok(converted) => converted,
        Err(payload) => {
            let Some(report) = crate::misc::uncaught_exception_report(&*payload) else {
                std::panic::resume_unwind(payload);
            };
            return Err(UserDiagnostic::new(
                format!(
                    "{}{report}\n",
                    format_type_warnings_lazy(
                        located_warnings.as_ref().unwrap_or(arena),
                        &source,
                        filename,
                        &tctx.warnings,
                    )
                ),
                2,
            )
            .into());
        }
    };
    let mut raw_warnings = raw_warnings;
    if !arena.stores_locations() {
        if raw_diagnostic.is_some() {
            return Err(LocationRetry::Diagnostic.into());
        }
        if arena.locations_required() {
            return Err(LocationRetry::Output.into());
        }
        if !place_location_free_warnings(
            arena,
            warning_locations,
            &mut located_warnings,
            &mut tctx.warnings[post_type_warning_start..],
        ) || !place_location_free_warnings(
            arena,
            warning_locations,
            &mut located_warnings,
            &mut raw_warnings,
        ) {
            return Err(LocationRetry::Warning.into());
        }
    }
    // Warnings of a location-free compile were placed in a located parse.
    let warning_arena = located_warnings.as_ref().unwrap_or(arena);

    // The file compile reports the typing warnings, then Translmod's
    // (js_implementation.ml:161-167); a Translmod error escapes before
    // `Warnings.check_fatal`.
    let mut warnings = format_type_warnings_lazy(
        warning_arena,
        &source,
        filename,
        &tctx.warnings[..post_type_warning_start],
    );
    if let Some(diagnostic) = raw_diagnostic {
        warnings.push_str(&format_type_warnings_lazy(
            warning_arena,
            &source,
            filename,
            &raw_warnings,
        ));
        return Err(prefix_diagnostic(
            &warnings,
            UserDiagnostic::new(
                format_compiler_error_report_from_location(
                    source(),
                    filename,
                    &diagnostic.loc,
                    &diagnostic.message,
                ),
                2,
            )
            .into(),
        ));
    }
    let late_type_warnings = &tctx.warnings[post_type_warning_start..];
    warnings.push_str(&format_type_warnings_lazy(
        warning_arena,
        &source,
        filename,
        late_type_warnings,
    ));
    warnings.push_str(&format_type_warnings_lazy(
        warning_arena,
        &source,
        filename,
        &raw_warnings,
    ));
    // lam_compile_main.ml:420 `Warnings.check_fatal ()`: a warning configured
    // as an error fails the compilation after its reports.
    if type_warnings_have_errors(&tctx.warnings) || type_warnings_have_errors(&raw_warnings) {
        return Err(UserDiagnostic::new(warnings, 2).into());
    }
    // Capture raw lambda sexp for the playground (only if requested).
    let raw_lambda_sexp = if options.capture_intermediates {
        let mut buf = Vec::new();
        crate::raw_lambda::print::print_raw_lambda(&raw_arena, raw_lambda, &mut buf);
        String::from_utf8_lossy(&buf).into_owned()
    } else {
        String::new()
    };

    let (mut lowered_arena, lowered_root, export_idents) =
        crate::timing::measure(crate::timing::Phase::Lambda, || {
            let _phase = info_span!("compiler.lower_lambda").entered();
            crate::raw_lambda::lower::lower_to_translmod_lambda(raw_arena, raw_lambda)
        });
    // js_implementation.ml:165 prints `-drawlambda` on Translmod's result.
    if options.dumps.contains(&DumpKind::RawLambda) {
        let mut buf = Vec::new();
        crate::lambda::printlambda::print_lambda(&lowered_arena.export(lowered_root), &mut buf);
        buf.push(b'\n');
        dumps.push((DumpKind::RawLambda, latin1_dump(buf)));
    }
    // lam_compile_main.ml:288-290: the first pass of Lam_compile_main.compile.
    let lowered_root = crate::timing::measure(crate::timing::Phase::Lambda, || {
        crate::lambda::lam_pass_collapse_var_aliases::collapse(
            &mut lowered_arena,
            lowered_root,
            &export_idents,
        )
    });
    if options.backend != crate::bir::shadow::BackendMode::Legacy {
        crate::bir::shadow::check_lambda(&lowered_arena, lowered_root, filename)?;
        crate::bir::shadow::check_norm(&lowered_arena, raw_lambda, filename)?;
    }
    let lowered_lambda = crate::lambda::arena::LamProgram {
        arena: lowered_arena,
        root: lowered_root,
    };
    let mut possible_required_modules =
        crate::lambda::lam_compile::collect_possible_required_modules_in_arena(
            &lowered_lambda.arena,
            lowered_lambda.root,
        );
    possible_required_modules.extend(raw_possible_required_modules);
    // OCaml has one mutable `Ident.currentstamp` through typechecking,
    // `Translmod.transl_implementation`, and `Lam_compile_main.compile`
    // (compiler/ext/ident.ml:26-58; compiler/core/js_implementation.ml:161-167).
    // Rewatch can split Rust in-process compilation before JS and resume it on a
    // different worker thread, so carry the module-local legacy stamp explicitly
    // instead of reading that worker's unrelated thread-local counter.
    let ident_stamp_at_js_boundary = crate::ident::Ident::current_local_stamp();

    for kind in [DumpKind::Lambda, DumpKind::LambdaLocs] {
        if options.dumps.contains(&kind) {
            let mut buf = Vec::new();
            let tree = lowered_lambda.to_tree();
            let _ = if kind == DumpKind::Lambda {
                crate::lambda::sexp_lambda::print_lambda(&tree, &mut buf)
            } else {
                crate::lambda::sexp_lambda::print_lambda_with_locs(&tree, &mut buf)
            };
            dumps.push((kind, latin1_dump(buf)));
        }
    }

    // Capture lambda sexp for the playground (only if requested).
    let lambda_sexp = if options.capture_intermediates {
        let mut buf = Vec::new();
        let _ =
            crate::lambda::sexp_lambda::print_lambda_with_locs(&lowered_lambda.to_tree(), &mut buf);
        String::from_utf8_lossy(&buf).into_owned()
    } else {
        String::new()
    };

    let pers_struct = publish_checked()?;
    if let (Some(census), Some(timing)) = (&mut tctx.derived_census, &census_timing) {
        census.account_pre_js(timing.snapshot());
        if let Some(warnings) = located_warnings.as_ref().and_then(|a| a.derived_census.as_ref()) {
            census.add_parse_work(warnings.parse_work());
        }
    }
    Ok(InProcessPreJsCompileResult {
        derived_census: tctx.derived_census.take(),
        lowered_lambda: Some(lowered_lambda),
        possible_required_modules,
        flat_make_paths,
        ident_stamp_at_js_boundary,
        file_directives: Vec::new(),
        file_config: Default::default(),
        signature: published_signature,
        pers_struct,
        lam_locs,
        typed_tree_sexp,
        raw_lambda_sexp,
        lambda_sexp,
        dumps,
        warnings,
        gentype,
        unit_reads,
        loaded_units: tctx
            .persistent_env
            .as_ref()
            .map(PersistentEnv::loaded_units)
            .unwrap_or_default(),
        derived_reference: None,
        derived_differences: None,
    })
        },
    ).1;
    result.map(|mut result| {
        result.file_directives = file_directives;
        result.file_config = file_config;
        result
    })
}

/// Run the JS backend on the result of
/// [`compile_preprocessed_structure_in_process_until_js`] and print the
/// JavaScript.
pub fn finish_preprocessed_structure_in_process_from_js_boundary(
    pre_js: InProcessPreJsCompileResult,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> Result<InProcessCompileResult> {
    finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook(
        pre_js, options, registry, None,
    )
}

/// [`finish_preprocessed_structure_in_process_from_js_boundary`], handing
/// the `.cmj` metadata to `metadata_ready` before the JavaScript is printed.
pub fn finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook(
    mut pre_js: InProcessPreJsCompileResult,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    metadata_ready: Option<&mut InProcessJsMetadataReadyHook<'_>>,
) -> Result<InProcessCompileResult> {
    // O(1): absent unless `RESCRIPT_DERIVED_PATH=check` compiled a unit
    // with a planned item.
    let Some(reference) = pre_js.derived_reference.take() else {
        return finish_from_js_boundary(pre_js, options, registry, metadata_ready);
    };
    let differences = pre_js.derived_differences.take();
    let differences = differences.as_ref();
    let unit = options.module_name.as_deref().unwrap_or("");
    let reference = finish_from_js_boundary(*reference, options, registry, None)?;
    let result = match metadata_ready {
        // The hook takes the export summary: compare what it is handed.
        Some(forward) => {
            let mut hook = |metadata: InProcessJsMetadataReady| {
                derived_check::settle(
                    differences,
                    derived_check::compare_exports(
                        unit,
                        metadata.is_pure,
                        &metadata.cmj_export_constants,
                        &metadata.cmj_export_arities,
                        &metadata.cmj_export_lambdas,
                        &reference,
                    ),
                )?;
                forward(metadata)
            };
            finish_from_js_boundary(pre_js, options, registry, Some(&mut hook))?
        }
        None => {
            let result = finish_from_js_boundary(pre_js, options, registry, None)?;
            derived_check::settle(
                differences,
                derived_check::compare_exports(
                    unit,
                    result.is_pure,
                    &result.cmj_export_constants,
                    &result.cmj_export_arities,
                    &result.cmj_export_lambdas,
                    &reference,
                ),
            )?;
            result
        }
    };
    derived_check::settle(differences, derived_check::compare_js(unit, &result, &reference))?;
    Ok(result)
}

/// The JS backend and printer of one pre-JS result.
fn finish_from_js_boundary(
    mut pre_js: InProcessPreJsCompileResult,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    metadata_ready: Option<&mut InProcessJsMetadataReadyHook<'_>>,
) -> Result<InProcessCompileResult> {
    if options.check_only {
        return Ok(InProcessCompileResult {
            signature: pre_js.signature,
            pers_struct: pre_js.pers_struct,
            warnings: pre_js.warnings,
            ..Default::default()
        });
    }
    // The same `@@config` flags the typing phase applied.
    let effective_options = pre_js.file_config.apply(options);
    let options = &*effective_options;
    let _span = info_span!(
        "compiler.in_process_js_finish",
        module = options.module_name.as_deref().unwrap_or(""),
        skip_js_render = options.skip_js_render,
        js_targets = options.js_output_targets.len()
    )
    .entered();
    let census_timing = pre_js.derived_census.as_ref().map(|_| crate::timing::ThreadTimingGuard::start());
    let mut persistent_env_for_js = PersistentEnv::from_registry(registry);
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    persistent_env_for_js.set_load_path_shared(load_path, load_path_display);
    persistent_env_for_js.set_open_modules(options.open_modules.clone());
    persistent_env_for_js.set_jsx_version(options.jsx_version);
    persistent_env_for_js.set_experimental_let_unwrap(options.experimental_let_unwrap);
    persistent_env_for_js.set_jsx_module(options.jsx_module.clone());
    persistent_env_for_js.set_nopervasives(options.nopervasives);
    persistent_env_for_js.set_compiling_module(options.module_name.clone());
    if let Some(module_name) = options.module_name.as_deref() {
        persistent_env_for_js.unregister_in_memory_signature(module_name);
    }
    let persistent_env_for_js = Some(persistent_env_for_js);
    crate::ident::Ident::set_current_time(pre_js.ident_stamp_at_js_boundary);
    let js_targets = effective_js_output_targets(options);
    let primary_target = js_targets.first();
    let primary_output_path = primary_target
        .map(|target| target.path.as_path())
        .or(options.output_path.as_deref());
    let primary_output_module_format = primary_target
        .map(|target| target.module_format)
        .or(options.output_module_format);
    let compile_multiple_js_targets = !options.skip_js_render && js_targets.len() > 1;
    let mut lowered_lambda = pre_js.lowered_lambda;
    let (
        program,
        module_path_resolver,
        mut cmj_export_constants,
        mut cmj_export_arities,
        mut cmj_export_lambdas,
        lam_locs,
    ) = {
        let _phase = info_span!(
            "compiler.js_compile",
            multiple_targets = compile_multiple_js_targets
        )
        .entered();
        if compile_multiple_js_targets {
            compile_js_program_for_output(
                lowered_lambda
                    .as_ref()
                    .expect("lowered lambda retained for multiple JS targets"),
                &pre_js.flat_make_paths,
                &pre_js.possible_required_modules,
                options,
                primary_output_path,
                primary_output_module_format,
                persistent_env_for_js.clone(),
                options.jsx_preserve,
                options.cross_module_inline,
                &pre_js.lam_locs,
            )?
        } else {
            compile_js_program_for_output_owned(
                lowered_lambda
                    .take()
                    .expect("lowered lambda consumed by single JS target"),
                std::mem::take(&mut pre_js.flat_make_paths),
                std::mem::take(&mut pre_js.possible_required_modules),
                options,
                primary_output_path,
                primary_output_module_format,
                persistent_env_for_js.clone(),
                options.jsx_preserve,
                options.cross_module_inline,
                std::mem::take(&mut pre_js.lam_locs),
            )?
        }
    };
    let lam_locs = std::sync::Arc::new(lam_locs);
    if !options.skip_js_render {
        check_module_path_resolution_errors(
            &program,
            &module_path_resolver,
            options.source_filename.as_deref().unwrap_or("_none_"),
        )?;
    }
    let is_pure = program.side_effect.is_none();
    if let Some(hook) = metadata_ready {
        hook(InProcessJsMetadataReady {
            is_pure,
            cmj_export_constants: std::mem::take(&mut cmj_export_constants),
            cmj_export_arities: std::mem::take(&mut cmj_export_arities),
            cmj_export_lambdas: std::mem::take(&mut cmj_export_lambdas),
            pers_struct: pre_js.pers_struct.take(),
        })?;
    }
    let mut rendered_programs = if options.skip_js_render {
        drop(program);
        Vec::new()
    } else {
        let mut rendered_programs = vec![(
            primary_target.map(|target| target.path.clone()),
            program,
            module_path_resolver,
            lam_locs,
        )];
        for target in js_targets.iter().skip(1) {
            let (program, module_path_resolver, _, _, _, target_lam_locs) =
                compile_js_program_for_output(
                    lowered_lambda
                        .as_ref()
                        .expect("lowered lambda retained for secondary JS targets"),
                    &pre_js.flat_make_paths,
                    &pre_js.possible_required_modules,
                    options,
                    Some(&target.path),
                    Some(target.module_format),
                    persistent_env_for_js.clone(),
                    options.jsx_preserve,
                    options.cross_module_inline,
                    &pre_js.lam_locs,
                )?;
            check_module_path_resolution_errors(
                &program,
                &module_path_resolver,
                options.source_filename.as_deref().unwrap_or("_none_"),
            )?;
            rendered_programs.push((
                Some(target.path.clone()),
                program,
                module_path_resolver,
                std::sync::Arc::new(target_lam_locs),
            ));
        }
        rendered_programs
    };

    let js_settings = JsFileSettings {
        file_directives: &pre_js.file_directives,
        debug: options.debug,
        jsx_preserve: options.jsx_preserve,
    };
    if options.backend != crate::bir::shadow::BackendMode::Legacy {
        for (_, program, resolver, _) in &rendered_programs {
            crate::bir::shadow::check_js(
                program, resolver, js_settings.file_directives, js_settings.debug,
                js_settings.jsx_preserve, !options.no_version_header,
                options.source_filename.as_deref().unwrap_or("_none_"),
            )?;
        }
    }
    let census_print_start = crate::derived_census::start(pre_js.derived_census.is_some());
    let (js, js_outputs) = crate::timing::measure(crate::timing::Phase::Codegen, || {
        let _phase = info_span!(
            "compiler.js_print",
            skip_js_render = options.skip_js_render,
            rendered_programs = rendered_programs.len()
        )
        .entered();
        if options.skip_js_render {
            (String::new(), Vec::new())
        } else {
            let (primary_path, primary_program, primary_resolver, primary_lam_locs) =
                rendered_programs.remove(0);
            let (mut primary_js, primary_source_map) = render_js_program(
                &primary_program,
                &primary_resolver,
                js_settings,
                options,
                primary_path.as_deref(),
                primary_lam_locs,
            );
            let mut js_outputs = Vec::new();
            let js = if let Some(path) = primary_path {
                js_outputs.push(JsOutput {
                    path,
                    code: std::mem::take(&mut primary_js),
                    source_map: primary_source_map,
                });
                drop(primary_program);
                String::new()
            } else {
                drop(primary_program);
                primary_js
            };
            for (path, program, module_path_resolver, lam_locs) in rendered_programs {
                let Some(path) = path else {
                    drop(program);
                    continue;
                };
                let (code, source_map) = render_js_program(
                    &program,
                    &module_path_resolver,
                    js_settings,
                    options,
                    Some(&path),
                    lam_locs,
                );
                drop(program);
                js_outputs.push(JsOutput {
                    path,
                    code,
                    source_map,
                });
            }
            (js, js_outputs)
        }
    });
    if let (Some(census), Some(timing), Some(print_start)) =
        (&mut pre_js.derived_census, &census_timing, census_print_start)
    {
        census.account_js(timing.snapshot(), crate::derived_census::nanos(print_start.elapsed()));
        census.finish(std::iter::once(js.as_str()).chain(js_outputs.iter().map(|out| out.code.as_str())))?;
    }
    Ok(InProcessCompileResult {
        js_output: js,
        js_outputs,
        signature: pre_js.signature,
        pers_struct: pre_js.pers_struct,
        is_pure,
        cmj_export_constants,
        cmj_export_arities,
        cmj_export_lambdas,
        typed_tree_sexp: pre_js.typed_tree_sexp,
        raw_lambda_sexp: pre_js.raw_lambda_sexp,
        lambda_sexp: pre_js.lambda_sexp,
        dumps: pre_js.dumps,
        warnings: pre_js.warnings,
        gentype: pre_js.gentype,
    })
}

/// Type check a preprocessed interface in process against the units in
/// `registry`, producing the signature its dependents read.
pub fn typecheck_preprocessed_signature_in_process(
    arena: &crate::parse_arena::ParseArena,
    signature: &Signature,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> Result<InProcessInterfaceResult> {
    let _span = info_span!(
        "compiler.in_process_signature",
        module = %module_name,
        file = %filename
    )
    .entered();
    let census_timing = options.derived_census.as_ref().map(|_| crate::timing::ThreadTimingGuard::start());
    let file_config = extract_file_config_from_signature(signature, arena);
    // The saved signature keeps its locations per the file's `-keep-locs`.
    let effective_options = file_config.apply(options);
    let options = &*effective_options;
    // The frontend raised on any payload these cannot read.
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_signature_attribute_specs(signature, arena)
            .expect("the frontend read these attributes");

    let source_cell = std::cell::OnceCell::new();
    let source = || -> &str { source_cell.get_or_init(|| read_in_process_source(filename)) };
    type_structure_two_modes(
        CheckUnit { filename, options, registry: Some(registry),
            module_name: Some(module_name), file_config: &file_config,
            frontend_warning_specs: &frontend_warning_specs, derived_plans: true,
            mode: crate::types::context::CheckMode::from_env() },
        // An interface has no derived item that can fall back.
        UnitSyntax::new(arena, signature, options),
        None,
        |tctx, env, syntax| transl_signature(tctx, env, syntax.arena, syntax.tree),
        |type_ctx, mut tctx, typed, UnitSyntax { arena, warning_locations, .. }, attempt_output| {
    let (typed_signature, env) = match typed {
        Ok(typed_signature) => typed_signature,
        Err(e) => {
            // As in the file compile: the warnings reported so far precede
            // the error report.
            tctx.drain_open_slot_uses();
            if !arena.stores_locations() {
                return Err(LocationRetry::Diagnostic.into());
            }
            let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            if let Some(error) = tctx
                .persistent_env
                .as_ref()
                .and_then(|persistent_env| persistent_env.last_error())
            {
                return Err(prefix_diagnostic(
                    &warnings,
                    persistent_env_error_to_anyhow(error, filename),
                ));
            }
            return Err(prefix_diagnostic(
                &warnings,
                type_mod_error_to_anyhow(
                    e,
                    type_ctx,
                    arena,
                    source(),
                    filename,
                    suppress_info_style,
                ),
            ));
        }
    };
    let unit_reads = if options.collect_unit_reads {
        crate::types::unit_reads::signature_reads(
            type_ctx,
            &tctx.typed,
            &typed_signature,
            &options.open_modules,
        )
    } else {
        Vec::new()
    };
    // js_implementation.ml:62: `ignore (Includemod.signatures initial_env sg
    // sg)`, which marks the declarations of the interface used.
    let sig_type = crate::types::typemod::decl_signature_from_typed_signature(
        &tctx.typed,
        &typed_signature,
        arena,
        type_ctx,
    );
    // js_implementation.ml `after_parsing_sig`: `Typemod.check_js_names
    // ~toplevel:true sg` before the self-inclusion.
    if let Err(e) = crate::types::typemod::check_js_names(type_ctx, true, &sig_type) {
        if !arena.stores_locations() {
            return Err(LocationRetry::Diagnostic.into());
        }
        let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
        let suppress_info_style =
            !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
        return Err(prefix_diagnostic(
            &warnings,
            type_mod_error_to_anyhow(e, type_ctx, arena, source(), filename, suppress_info_style),
        ));
    }
    // js_implementation.ml:56: `ignore (Includemod.signatures initial_env sg
    // sg)` drops the coercion; a payload reader's error escapes it.
    let self_inclusion = crate::types::includemod::compunit(
        type_ctx, &env, filename, &sig_type, filename, &sig_type,
    );
    if let Err(e) = crate::types::includemod::escaped(type_ctx, self_inclusion) {
        return Err(in_process_typed_unit_error(
            e.into(),
            type_ctx,
            arena,
            &source,
            filename,
            &tctx.warnings,
        ));
    }
    // js_implementation.ml:64 `Delayed_checks.force_delayed_checks ()`.
    tctx.flush_value_usage_checks();
    let mut located_warnings = None;
    if !place_location_free_warnings(arena, warning_locations, &mut located_warnings, &mut tctx.warnings) {
        return Err(LocationRetry::Warning.into());
    }
    let warnings = format_type_warnings_lazy(
        located_warnings.as_ref().unwrap_or(arena),
        &source,
        filename,
        &tctx.warnings,
    );
    if type_warnings_have_errors(&tctx.warnings) {
        return Err(UserDiagnostic::new(warnings, 2).into());
    }
    let mut dumps: Vec<(DumpKind, String)> = Vec::new();
    for kind in [DumpKind::TypedTree, DumpKind::TypedTreeLocs] {
        if options.dumps.contains(&kind) {
            let mut buf = Vec::new();
            let _ = if kind == DumpKind::TypedTree {
                print_typed_signature(arena, type_ctx, &tctx.typed, &typed_signature, &mut buf)
            } else {
                print_typed_signature_with_locs(
                    arena,
                    type_ctx,
                    &tctx.typed,
                    &typed_signature,
                    &mut buf,
                )
            };
            dumps.push((kind, latin1_dump(buf)));
        }
    }
    // GenTypeMain.ml:91-107: read for the implementation's compile, which
    // raises and writes what this finds.
    let gentype = with_gentype_artifact(
        options,
        GentypeUnit {
            annots: crate::gentype::main::TypedArtifactAnnots::Interface(&typed_signature),
            arena,
            ta: &tctx.typed,
            type_ctx,
            source: &|| source().to_string(),
            filename,
            module_name,
        },
        crate::gentype::main::read_interface_artifact,
    );
    if gentype.as_ref().is_some_and(crate::gentype::main::InterfaceRead::needs_locations) {
        return Err(LocationRetry::Warning.into());
    }
    let decl_signature = crate::types::typemod::decl_signature_from_typed_signature(
        &tctx.typed,
        &typed_signature,
        arena,
        type_ctx,
    );

    let typed_module_type = crate::types::typedtree::ModuleType {
        mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_signature(typed_signature),
        mty_type: crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(decl_signature)),
        mty_env: crate::types::typedtree::EnvRef(0),
        mty_loc: crate::parse_arena::LocIdx(0),
        mty_attributes: crate::parser::ast::Attributes::new(),
    };
    let published_signature =
        match crate::types::typemod::decl_module_type_from_typed(&typed_module_type) {
            Some(crate::types::decl::ModuleType::MtySignature(sig)) => {
                std::sync::Arc::unwrap_or_clone(sig)
            }
            _ => {
                return Err(anyhow!(
                    "Failed to extract interface signature from typed tree"
                ));
            }
        };

    // js_implementation.ml:66-70 saves the interface through
    // `Env.save_signature`, whose `Subst.for_saving` copy renames the bound
    // identifiers (env.ml:1886-1892). In-process builds write no `.cmi`, but
    // the copy still takes its stamps, as in OCaml.
    if let crate::types::typedtree::ModuleTypeDesc::Tmty_signature(_) = &typed_module_type.mty_desc
    {
        saved_signature_copy(type_ctx, &published_signature);
    }

    let mut internal_env = tctx
        .persistent_env
        .take()
        .unwrap_or_else(PersistentEnv::new);

    let _publication_guard = crate::perf_counters::SignaturePublication::begin();
    // js_implementation.ml:66: `Builtin_attributes.deprecated_of_sig ast`.
    // The raw `ps_sig` of the saved interface (env.ml:1949-1952,
    // env.ml:669-678), before registration substitutes component paths in
    // place. The implementation is checked against it (typemod.ml:1742-1758),
    // as the file compile checks against the `.cmi`.
    let raw_signature = {
        let mut raw = crate::types::typecore::copy_lookup_signature_for_subst(
            &published_signature,
            type_ctx,
        );
        // The check reads the signature as saved in the `.cmi`
        // (env.ml:1949-1952 reads the file back), so drop the same locations.
        if !options.keep_locs {
            strip_saved_signature_locations(&mut raw);
        }
        std::sync::Arc::new(raw)
    };
    let mut saved_signature = published_signature.clone();
    if !options.keep_locs {
        strip_saved_signature_locations(&mut saved_signature);
    }
    let crcs = Vec::new();
    // js_implementation.ml:59: `Builtin_attributes.deprecated_of_sig ast`.
    let deprecated =
        crate::types::typemod::deprecated_of_sig(arena, signature).map_err(|error| {
            in_process_typed_unit_error(
                payload_type_error(error),
                type_ctx,
                arena,
                &source,
                filename,
                &tctx.warnings,
            )
        })?;
    attempt_output.publish(type_ctx)?;
    if type_ctx.compiler_counters_enabled() {
        crate::perf_counters::census_exported_signature(type_ctx, module_name, &raw_signature);
    }
    if options.dumps.contains(&DumpKind::Sig) {
        dumps.push(canonical_signature_dump(
            type_ctx,
            module_name,
            &raw_signature,
            deprecated.as_deref(),
            arena,
        ));
    }
    internal_env.register_in_memory_signature(
        module_name,
        saved_signature,
        filename,
        deprecated,
        crcs,
        type_ctx,
    );
    type_ctx.register_raw_module_sig(module_name, raw_signature);

    // The implementation reads its own interface even when the module is a leaf.
    let (pers_struct, signature_report) = publish_signature(
        &internal_env,
        options,
        module_name,
        filename,
        type_ctx,
        arena,
        SignaturePublicationMode::Eager,
    )?;
    attempt_output.signature_report(signature_report)?;

    if let (Some(mut census), Some(timing)) = (arena.derived_census.clone(), &census_timing) {
        census.account_pre_js(timing.snapshot());
        if let Some(warnings) = located_warnings.as_ref().and_then(|a| a.derived_census.as_ref()) {
            census.add_parse_work(warnings.parse_work());
        }
        census.finish(std::iter::empty::<&str>())?;
    }
    Ok(InProcessInterfaceResult {
        signature: published_signature,
        pers_struct,
        gentype,
        dumps,
        warnings,
        loaded_units: internal_env.loaded_units(),
        unit_reads,
    })
        },
    ).1
}

#[cfg(test)]
mod tests {
    #[test]
    fn two_mode_attempts_keep_only_the_final_check() {
        assert_eq!(std::mem::size_of::<super::CheckAttempt>(), 2);
        assert_eq!(std::mem::size_of::<super::AttemptOutput>(), 5 * std::mem::size_of::<usize>());
        assert_eq!(std::mem::size_of::<super::CheckUnit<'_>>(), 10 * std::mem::size_of::<usize>());
        assert_eq!(std::mem::size_of::<super::UnitSyntax<'_, super::Structure>>(), 3 * std::mem::size_of::<usize>());
        for (source, attempts) in [("let x = 1", 1), ("let x: bool = 1", 2)] {
            let mut parser = super::Parser::new("Attempt.res", source);
            let structure = super::module::parse_structure(&mut parser);
            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
            let calls = std::cell::Cell::new(0);
            let finishes = std::cell::Cell::new(0);
            let (_, result) = super::type_structure_two_modes(
                super::CheckUnit { filename: "Attempt.res", options: &options,
                    registry: Some(&super::ModuleRegistry::new()), module_name: Some("Attempt"),
                    file_config: &Default::default(), frontend_warning_specs: &[], derived_plans: true,
                    mode: crate::types::context::CheckMode::Success },
                super::UnitSyntax::new(parser.arena(), &structure, &options),
                None,
                |tctx, env, syntax| {
                    calls.set(calls.get() + 1);
                    super::type_structure(tctx, env, syntax.arena, syntax.tree)
                },
                |_, _, result, _, _reports| {
                    finishes.set(finishes.get() + 1);
                    assert_eq!(result.is_ok(), attempts == 1);
                    Ok(())
                },
            );
            result.unwrap();
            assert_eq!(calls.get(), attempts);
            assert_eq!(finishes.get(), 1);
        }
    }
    #[test]
    fn a_unit_of_ten_thousand_items_that_fails_in_its_last_item_is_checked_exactly_twice() {
        std::thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(|| {
            use crate::types::context::CheckMode;
            use std::fmt::Write;
            let mut source = String::new();
            for n in 0..10_000 {
                writeln!(source, "let x{n} = {n}").unwrap();
            }
            source.push_str("let bad: bool = 1\n");
            let mut reports = Vec::new();
            // Explicit Explain is the mode selected by RESCRIPT_CHECK_MODE=explain;
            // do not mutate process environment in parallel unit tests.
            for first_mode in [CheckMode::Success, CheckMode::Explain] {
                let mut parser = super::Parser::new("TenThousand.res", &source);
                let structure = super::module::parse_structure(&mut parser);
                crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
                let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
                let attempts = std::cell::RefCell::new(Vec::new());
                let (_, result) = super::type_structure_two_modes(
                    super::CheckUnit {
                        filename: "TenThousand.res", options: &options, registry: None,
                        module_name: None, file_config: &Default::default(),
                        frontend_warning_specs: &[], derived_plans: true, mode: first_mode,
                    },
                    super::UnitSyntax::new(parser.arena(), &structure, &options), None,
                    |tctx, env, syntax| {
                        let mode = if tctx.type_ctx.unify_takes_snapshot() {
                            CheckMode::Explain
                        } else { CheckMode::Success };
                        attempts.borrow_mut().push(mode);
                        let result = super::type_structure(tctx, env, syntax.arena, syntax.tree);
                        if mode == CheckMode::Success {
                            assert_eq!(tctx.type_ctx.journal_entries_for_test(), 0);
                        }
                        result
                    },
                    |ctx, _, typed, syntax, _| -> super::Result<()> {
                        typed.map(|_| ()).map_err(|error| super::type_mod_error_to_anyhow(
                            error, ctx, syntax.arena, &source, "TenThousand.res", false,
                        ))
                    },
                );
                assert_eq!(*attempts.borrow(), if first_mode == CheckMode::Success {
                    vec![CheckMode::Success, CheckMode::Explain]
                } else { vec![CheckMode::Explain] });
                reports.push(format!("{:#}", result.unwrap_err()));
            }
            assert_eq!(reports[0], reports[1]);
            assert!(reports[0].contains("bool"));
        }).unwrap().join().unwrap();
    }

    /// The settings of the one attempt loop: each retry reason applies once,
    /// a fallback keeps the check mode and an explanation keeps the path.
    #[test]
    fn attempt_settings_compose_each_reason_once() {
        use super::{AttemptRetry, CheckAttempt};
        use crate::types::context::CheckMode;
        let first = CheckAttempt { mode: CheckMode::Success, derived_plans: true };
        let general = first.after(AttemptRetry::DerivedFallback).unwrap();
        assert_eq!(general, CheckAttempt { mode: CheckMode::Success, derived_plans: false });
        let explained = general.after(AttemptRetry::Explain).unwrap();
        assert_eq!(explained, CheckAttempt { mode: CheckMode::Explain, derived_plans: false });
        assert_eq!(explained.after(AttemptRetry::Explain), None);
        assert_eq!(explained.after(AttemptRetry::DerivedFallback), None);
        assert_eq!(
            first.after(AttemptRetry::Explain).unwrap().after(AttemptRetry::DerivedFallback),
            Some(explained),
        );
    }

    /// A unit whose plan cannot be used continues, in the same attempt loop
    /// and check mode, on its general syntax, made once. A Success unit
    /// that then type-checks has no explanation; one with a type error is
    /// explained once, on the general syntax, and reports what a forced
    /// Explain check reports.
    #[test]
    fn a_derived_fallback_and_an_explanation_share_one_attempt_loop() {
        use crate::binary_ast::derive::fixtures::{CURRIED_LIBRARY, derive_source};
        use crate::types::context::CheckMode;
        for (error, success_checks) in [(false, 2), (true, 3)] {
            let source = if error {
                format!("{CURRIED_LIBRARY}\nlet bad: bool = 1")
            } else {
                CURRIED_LIBRARY.to_owned()
            };
            let mut reports = Vec::new();
            for mode in [CheckMode::Success, CheckMode::Explain] {
                let (parser, structure) = derive_source(&source, true);
                assert!(parser.arena().plans().item_count() > 0);
                let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
                let regenerated = std::cell::Cell::new(0);
                let fallback = || {
                    regenerated.set(regenerated.get() + 1);
                    let (mut parser, tree) = derive_source(&source, false);
                    parser.arena_mut().derived_census = Some(Box::new(
                        crate::derived_census::Census::new(std::path::Path::new("unused-census.jsonl"), "General.res"),
                    ));
                    Ok(super::GeneralSyntax { arena: parser.into_arena(), tree, warning_locations: None })
                };
                // The syntax and mode of each check, in order.
                let checks = std::cell::RefCell::new(Vec::new());
                let finishes = std::cell::Cell::new(0);
                let first_arena: *const super::ParseArena = parser.arena();
                let (_, result) = super::type_structure_two_modes(
                    super::CheckUnit {
                        filename: "Fallback.res", options: &options, registry: None,
                        module_name: Some("Fallback"), file_config: &Default::default(),
                        frontend_warning_specs: &[], derived_plans: true, mode,
                    },
                    super::UnitSyntax::new(parser.arena(), &structure, &options),
                    Some(&fallback),
                    |tctx, env, syntax| {
                        // Outside any speculation only an Explain check snapshots.
                        let mode = if tctx.type_ctx.unify_takes_snapshot() { CheckMode::Explain } else { CheckMode::Success };
                        let first = std::ptr::eq(syntax.arena, first_arena);
                        checks.borrow_mut().push((first, mode));
                        assert_eq!(tctx.derived_census.is_some(), !first,
                            "fallback attempts retain the general syntax's census");
                        super::type_structure(tctx, env, syntax.arena, syntax.tree)
                    },
                    |ctx, _, typed, syntax, _| -> super::Result<()> {
                        finishes.set(finishes.get() + 1);
                        assert!(!std::ptr::eq(syntax.arena, first_arena), "finished from the general syntax");
                        match typed {
                            Ok(_) => Ok(()),
                            Err(error) => Err(super::type_mod_error_to_anyhow(
                                error, ctx, syntax.arena, "", "Fallback.res", false,
                            )),
                        }
                    },
                );
                assert_eq!(regenerated.get(), 1, "the general syntax is made once");
                assert_eq!(finishes.get(), 1, "only the final attempt is finished");
                let checks = checks.into_inner();
                let expected: Vec<(bool, CheckMode)> = match (mode, error) {
                    (CheckMode::Success, false) => vec![(true, CheckMode::Success), (false, CheckMode::Success)],
                    (CheckMode::Success, true) => vec![
                        (true, CheckMode::Success), (false, CheckMode::Success), (false, CheckMode::Explain),
                    ],
                    (CheckMode::Explain, _) => vec![(true, CheckMode::Explain), (false, CheckMode::Explain)],
                };
                assert_eq!(checks, expected);
                if mode == CheckMode::Success {
                    assert_eq!(checks.len(), success_checks);
                }
                assert_eq!(result.is_err(), error);
                reports.push(result.err().map(|error| format!("{error:#}")));
            }
            assert_eq!(reports[0], reports[1], "Success and forced Explain report the same");
        }
    }

    /// Without a way to make the general syntax, a fallback fails the
    /// compile with `DerivedRetry` and nothing is finished.
    #[test]
    fn a_derived_fallback_without_general_syntax_is_a_derived_retry() {
        let (parser, structure) =
            crate::binary_ast::derive::fixtures::derive_source(crate::binary_ast::derive::fixtures::CURRIED_LIBRARY, true);
        let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
        let (_, result) = super::type_structure_two_modes(
            super::CheckUnit {
                filename: "Fallback.res", options: &options, registry: None, module_name: None,
                file_config: &Default::default(), frontend_warning_specs: &[], derived_plans: true,
                mode: crate::types::context::CheckMode::Success,
            },
            super::UnitSyntax::new(parser.arena(), &structure, &options),
            None,
            |tctx, env, syntax| super::type_structure(tctx, env, syntax.arena, syntax.tree),
            |_, _, _, _, _| -> super::Result<()> { panic!("an abandoned attempt is not finished") },
        );
        assert!(result.unwrap_err().is::<super::DerivedRetry>());
    }

    /// A codec with an optional parameter fails its plan's arity
    /// obligation; the general form, which applies it to one argument,
    /// types.
    const FALLING_BACK: &str = "type plain = int\nlet plain_encode = Spice.intToJson\nlet plain_encodeJson = (x: plain, ~extra=1) => {\n  let _ = extra\n  plain_encode(x)\n}\nlet plain_decode = Spice.intFromJson\n@spice type t = {a: plain}\n";

    /// The in-process compile of a unit whose plan cannot be used gives its
    /// attempt loop the general syntax: it compiles as the general path
    /// does, and a type error after the fallback is the general path's.
    #[test]
    fn an_in_process_compile_falls_back_within_its_attempt_loop() {
        use super::{CompilerOptions, DerivedPath, compile_source_in_process};
        let compile = |extra: &str, derived_path| {
            let source = format!("{}{FALLING_BACK}{extra}", crate::binary_ast::derive::fixtures::RECORD_LIBRARY);
            let options = CompilerOptions { spice_ppx: true, derived_path, ..Default::default() };
            compile_source_in_process(
                &source, "Fallback.res", "Fallback", &options,
                &crate::cmi::persistent_env::ModuleRegistry::new(), false, None,
            )
        };
        let planned = compile("", DerivedPath::Plans).expect("the unit falls back and compiles");
        let general = compile("", DerivedPath::General).unwrap();
        assert_eq!(planned.js_outputs.len(), general.js_outputs.len());
        for (planned, general) in planned.js_outputs.iter().zip(&general.js_outputs) {
            assert_eq!(planned.code, general.code);
        }
        assert_eq!(planned.warnings, general.warnings);
        let planned = compile("let bad: bool = 1\n", DerivedPath::Plans).err().expect("a type error");
        assert!(!planned.is::<super::DerivedRetry>());
        let general = compile("let bad: bool = 1\n", DerivedPath::General).err().expect("a type error");
        assert_eq!(format!("{planned:#}"), format!("{general:#}"));
        assert!(format!("{planned:#}").contains("bool"));
    }

    /// The fixture falls back: its plan is abandoned once, and with a type
    /// error after it the Success check explains once, on the general
    /// syntax, reporting what a forced Explain check reports.
    #[test]
    fn a_frontend_fallback_then_a_type_error_is_explained_once() {
        use crate::binary_ast::derive::fixtures::frontend_source;
        use crate::types::context::CheckMode;
        let source = format!("{FALLING_BACK}let bad: bool = 1\n");
        let mut reports = Vec::new();
        for mode in [CheckMode::Success, CheckMode::Explain] {
            let (parser, structure) = frontend_source(&source, true);
            let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
            let regenerated = std::cell::Cell::new(0);
            let checks = std::cell::Cell::new(0);
            let fallback = || {
                regenerated.set(regenerated.get() + 1);
                let (parser, tree) = frontend_source(&source, false);
                Ok(super::GeneralSyntax { arena: parser.into_arena(), tree, warning_locations: None })
            };
            let (_, result) = super::type_structure_two_modes(
                super::CheckUnit {
                    filename: "Fallback.res", options: &options, registry: None, module_name: None,
                    file_config: &Default::default(), frontend_warning_specs: &[], derived_plans: true, mode,
                },
                super::UnitSyntax::new(parser.arena(), &structure, &options),
                Some(&fallback),
                |tctx, env, syntax| {
                    checks.set(checks.get() + 1);
                    super::type_structure(tctx, env, syntax.arena, syntax.tree)
                },
                |ctx, _, typed, syntax, _| -> super::Result<()> {
                    typed.map(|_| ()).map_err(|error| {
                        super::type_mod_error_to_anyhow(error, ctx, syntax.arena, &source, "Fallback.res", false)
                    })
                },
            );
            assert_eq!(regenerated.get(), 1);
            assert_eq!(checks.get(), if mode == CheckMode::Success { 3 } else { 2 });
            reports.push(format!("{:#}", result.unwrap_err()));
        }
        assert_eq!(reports[0], reports[1]);
    }

    #[test]
    #[should_panic(expected = "unexplained unification failure after Success publication")]
    fn a_caught_failure_after_publication_is_asserted_at_the_unit_exit() {
        let mut parser = super::Parser::new("Published.res", "let x = 1");
        let structure = super::module::parse_structure(&mut parser);
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
        super::type_structure_two_modes(
            super::CheckUnit {
                filename: "Published.res", options: &options, registry: None, module_name: None,
                file_config: &Default::default(), frontend_warning_specs: &[], derived_plans: true,
                mode: crate::types::context::CheckMode::Success,
            },
            super::UnitSyntax::new(parser.arena(), &structure, &options), None,
            |tctx, env, syntax| super::type_structure(tctx, env, syntax.arena, syntax.tree),
            |ctx, mut tctx, typed, _, output| -> super::Result<()> {
                typed.unwrap();
                output.publish(ctx)?;
                let int = ctx.new_constr(crate::types::predef::path_int(), vec![]);
                let string = ctx.new_constr(crate::types::predef::path_string(), vec![]);
                assert!(crate::types::ctype::unify(ctx, &mut tctx.unify_state, int, string).is_err());
                Ok(())
            },
        ).1.unwrap();
    }

    #[test]
    fn a_successful_planned_unit_allocates_nothing_for_its_borrowed_fallback() {
        let source = "@spice type t = array<A.t>";
        let (parser, structure) = crate::binary_ast::derive::fixtures::derive_source(source, true);
        assert!(parser.arena().plans().item_count() > 0);
        let options = super::CompilerOptions {
            nopervasives: true, publish_in_process_signature: false, ..Default::default()
        };
        // Measure production fallback preparation, not the unrelated checker
        // and backend allocations or shared-store growth of compiling a unit.
        let mut provider = None;
        let setup = allocation_counter::measure(|| {
            provider = Some(super::general_syntax_provider(source, "Allocation.res", &options));
        });
        assert_eq!(setup.count_total, 0);
        assert_eq!(setup.bytes_total, 0);
        let calls = std::cell::Cell::new(0);
        let fallback = || {
            calls.set(calls.get() + 1);
            provider.as_ref().unwrap()()
        };
        super::compile_preprocessed_structure_in_process_until_js(
            parser.arena(), &structure, "Allocation.res", "Allocation", &options,
            &super::ModuleRegistry::new(), false, None, None,
            super::SignaturePublicationMode::Eager, Some(&fallback),
        ).unwrap();
        assert_eq!(calls.get(), 0, "the unit's first attempt must succeed");
    }

    #[test]
    fn a_discarded_attempt_writes_no_signature_report() {
        use crate::cmi::signature_check::{Comparison, SignatureCheck};
        let directory = std::env::temp_dir().join(format!("discarded-report-{}", std::process::id()));
        assert!(!directory.exists());
        let check = SignatureCheck::for_test(directory.clone());
        let comparison = Comparison::not_applicable("test", "no shared graph");
        let mut discarded = super::AttemptOutput::new(crate::types::context::CheckMode::Success);
        discarded.signature_report(Some(check.prepare("Discarded.res", &comparison).unwrap())).unwrap();
        assert!(!directory.exists());
        drop(discarded);
        assert!(!directory.exists(), "discarding must not create a report or directory");
        let ctx = super::fresh_type_context();
        let mut retained = super::AttemptOutput::new(crate::types::context::CheckMode::Explain);
        retained.signature_report(Some(check.prepare("Retained.res", &comparison).unwrap())).unwrap();
        retained.publish(&ctx).unwrap();
        let files: Vec<_> = std::fs::read_dir(&directory).unwrap().map(Result::unwrap).collect();
        assert_eq!(files.len(), 1);
        assert!(std::fs::read_to_string(files[0].path()).unwrap().contains("Retained.res"));
        std::fs::remove_file(files[0].path()).unwrap();
        std::fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn location_retries_do_not_explain_or_publish_the_unlocated_attempt() {
        use crate::types::context::CheckMode;
        for retry in [super::LocationRetry::Warning, super::LocationRetry::Output,
                      super::LocationRetry::Diagnostic] {
            let mut parser = super::Parser::new("Locations.res", "let x = 1");
            let structure = super::module::parse_structure(&mut parser);
            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
            let finishes = std::cell::Cell::new(0);
            let (_, result) = super::type_structure_two_modes(
                super::CheckUnit {
                    filename: "Locations.res", options: &options, registry: None,
                    module_name: None, file_config: &Default::default(),
                    frontend_warning_specs: &[], derived_plans: true, mode: CheckMode::Success,
                },
                super::UnitSyntax::new(parser.arena(), &structure, &options), None,
                |tctx, env, syntax| super::type_structure(tctx, env, syntax.arena, syntax.tree),
                |_, _, typed, _, reports| -> super::Result<()> {
                    typed.unwrap();
                    finishes.set(finishes.get() + 1);
                    // Publishing this deliberately invalid Success report would fail.
                    reports.stderr.extend_from_slice(b"discarded location-free report");
                    Err(retry.into())
                },
            );
            assert_eq!(finishes.get(), 1);
            assert_eq!(result.unwrap_err().downcast_ref::<super::LocationRetry>(), Some(&retry));
        }
    }

    #[test]
    fn post_structure_validation_is_rechecked_before_publication() {
        use crate::types::context::CheckMode;
        let source = "let identity = x => x\nlet applied = identity(identity)";
        let mut reports = Vec::new();
        for mode in [CheckMode::Success, CheckMode::Explain] {
            let mut parser = super::Parser::new("NonGeneralizable.res", source);
            let structure = super::module::parse_structure(&mut parser);
            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
            let attempts = std::cell::Cell::new(0);
            let (_, result) = super::type_structure_two_modes(
                super::CheckUnit {
                    filename: "NonGeneralizable.res", options: &options,
                    registry: None, module_name: None, file_config: &Default::default(),
                    frontend_warning_specs: &[], derived_plans: true, mode,
                },
                super::UnitSyntax::new(parser.arena(), &structure, &options),
                None,
                |tctx, env, syntax| super::type_structure(tctx, env, syntax.arena, syntax.tree),
                |ctx, _, typed, _, output| -> super::Result<()> {
                    attempts.set(attempts.get() + 1);
                    assert!(output.stderr.is_empty(), "discarded reports must not enter the retry");
                    let ((structure, env), _) = typed.expect("structure typing succeeds");
                    let signature = crate::types::includemod::simplify_signature(&structure.str_type);
                    let error = crate::types::typemod::check_nongen_schemes(ctx, &env, &signature)
                        .expect_err("validation, not structure typing, rejects this unit");
                    Err(super::type_mod_error_to_anyhow(
                        error, ctx, parser.arena(), source, "NonGeneralizable.res", false,
                    ))
                },
            );
            assert_eq!(attempts.get(), if mode == CheckMode::Success { 2 } else { 1 });
            reports.push(format!("{:#}", result.unwrap_err()));
        }
        assert_eq!(reports[0], reports[1]);
        assert!(reports[0].contains("cannot be generalized"));
    }

    #[test]
    fn discarded_attempt_warnings_match_explain() {
        use crate::types::context::CheckMode;
        for recovered in [false, true] {
            let source = if recovered {
                "let f = x => switch x { | true => 1 }"
            } else {
                "let f = x => switch x { | true => 1 }\nlet bad: bool = 1"
            };
            let mut reports = Vec::new();
            for mode in [CheckMode::Success, CheckMode::Explain] {
                let mut parser = super::Parser::new("Warnings.res", source);
                let structure = super::module::parse_structure(&mut parser);
                crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
                let options = super::CompilerOptions { nopervasives: true, ..Default::default() };
                let (_, report) = super::type_structure_two_modes(
                    super::CheckUnit {
                        filename: "Warnings.res", options: &options,
                        registry: None, module_name: Some("Warnings"), file_config: &Default::default(),
                        frontend_warning_specs: &[], derived_plans: true, mode,
                    },
                    super::UnitSyntax::new(parser.arena(), &structure, &options),
                    None,
                    |tctx, env, syntax| {
                        if recovered {
                            // Model a caller that catches a failed unification, then
                            // continues checking an expression that emits a warning.
                            let ctx = tctx.type_ctx;
                            let left = ctx.new_constr(crate::types::predef::path_bool(), vec![]);
                            let right = ctx.new_constr(crate::types::predef::path_string(), vec![]);
                            assert!(crate::types::ctype::unify(ctx, &mut tctx.unify_state, left, right).is_err());
                        }
                        let result = super::type_structure(tctx, env, syntax.arena, syntax.tree);
                        tctx.flush_value_usage_checks();
                        result
                    },
                    |ctx, tctx, typed, _, _reports| {
                        assert!(!tctx.warnings.is_empty(), "fixture must exercise a warning");
                        let mut report = super::format_type_warnings(parser.arena(), source, "Warnings.res", &tctx.warnings);
                        if let Err(error) = typed {
                            report.push_str(&format!("{:#}", super::type_mod_error_to_anyhow(
                                error, ctx, parser.arena(), source, "Warnings.res", false,
                            )));
                        }
                        Ok(report)
                    },
                );
                reports.push(report.unwrap());
            }
            assert_eq!(reports[0], reports[1]);
        }
    }

    /// `-bs-cross-module-opt` and `-bs-no-cross-module-opt` in `@@config`
    /// set `Js_config.cross_module_inline` for the file, the last one given
    /// winning, over the command line's.
    #[test]
    fn file_config_flags_set_cross_module_inline() {
        let overrides = |source: &str| {
            let mut parser = super::Parser::new("A.res", source);
            let structure = super::module::parse_structure(&mut parser);
            super::extract_file_config_from_structure(&structure, parser.arena())
        };
        let mut options = super::CompilerOptions::default();
        assert!(!overrides("let x = 1\n").apply(&options).cross_module_inline);
        let on = overrides("@@config({flags: [\"-bs-cross-module-opt\"]})\nlet x = 1\n");
        assert_eq!(on.cross_module_inline, Some(true));
        assert!(on.apply(&options).cross_module_inline);
        let off = overrides(
            "@@config({flags: [\"-bs-cross-module-opt\", \"-bs-no-cross-module-opt\"]})\nlet x = 1\n",
        );
        options.cross_module_inline = true;
        assert!(!off.apply(&options).cross_module_inline);
        assert!(overrides("let x = 1\n").apply(&options).cross_module_inline);
    }

    /// Only the first `@@config` among the leading attributes counts
    /// (compiler/frontend/ast_config.ml:57-71): a later or nested one, or a
    /// flag string in another attribute, changes nothing.
    #[test]
    fn file_config_reads_only_the_first_leading_config() {
        let overrides = |source: &str| {
            let mut parser = super::Parser::new("A.res", source);
            let structure = super::module::parse_structure(&mut parser);
            super::extract_file_config_from_structure(&structure, parser.arena())
        };
        let first = overrides(
            "@@warning(\"-a\")\n@@config({flags: [\"-bs-g\"]})\n@@config({flags: [\"-bs-noassertfalse\"]})\nlet x = 1\n",
        );
        assert!(first.debug);
        assert!(!first.no_assert_false);
        let late = overrides("let x = 1\n@@config({flags: [\"-bs-g\"]})\n");
        assert!(!late.debug);
        let nested =
            overrides("module M = {\n  @@config({flags: [\"-bs-noassertfalse\"]})\n}\n");
        assert!(!nested.no_assert_false);
        let unrelated = overrides("@@deprecated(\"-bs-g\")\nlet x = 1\n");
        assert!(!unrelated.debug);
    }

    /// tests/syntax_tests/res_test.ml:27-84: formatting keeps a file's line
    /// endings, also inside comments, template literals and raw JS, and
    /// formatting the result again changes nothing. The line breaks inside
    /// literals are part of the program and keep their bytes, whatever the
    /// file's line endings, and so do the ones inside comments.
    #[test]
    fn format_keeps_line_endings() {
        let to_crlf = |text: &str| text.split('\n').collect::<Vec<_>>().join("\r\n");
        let format = |source: &str| {
            String::from_utf8(super::format_source(source.as_bytes(), "A.res").unwrap()).unwrap()
        };
        let lf = "/* a\n multi-line comment */\n/* a comment\n * with stars\n */\nlet s = `line 1\nline 2`\n\nlet r = %raw(`\n  function () {\n    return 1\n  }\n`)\n";
        let crlf = to_crlf(lf);
        for source in [
            lf,
            crlf.as_str(),
            "let x = 1\r\n\r\nlet s = \"a\nb\"\r\n",
            "let x = 1\n\nlet s = \"a\r\nb\"\n",
            "let x = 1\r\n\r\nlet t = `a\nb`\r\n\r\nlet c = '\n'\r\n\r\nlet p = #\"a\nb\"\r\n",
            "let x = 1\n\nlet t = `a\r\nb`\n\nlet c = '\r'\n\nlet p = #\"a\r\nb\"\n",
            "let x = 1\n/* a\r\r\nb\nc */\nlet y = 2\n",
            "let x = 1\r\n/* a\nb\r\nc */\r\nlet y = 2\r\n",
        ] {
            let formatted = format(source);
            assert_eq!(formatted, source);
            assert_eq!(format(&formatted), formatted);
        }
        // Formatting keeps a byte order mark, and a lone CR ends a line.
        let bom = "\u{EF}\u{BB}\u{BF}";
        let format_latin1 = |source: &str| -> String {
            let bytes: Vec<u8> = source.chars().map(|c| c as u8).collect();
            super::format_source(&bytes, "A.res")
                .unwrap()
                .into_iter()
                .map(char::from)
                .collect()
        };
        for source in [
            format!("{bom}let x = 1\n"),
            format!("{bom}// c\r\nlet x = 1\r\n"),
        ] {
            let formatted = format_latin1(&source);
            assert_eq!(formatted, source);
            assert_eq!(format_latin1(&formatted), formatted);
        }
        assert_eq!(
            format("let x = 1 // c\rlet y = 2\n"),
            "let x = 1 // c\nlet y = 2\n"
        );
        assert_eq!(format("let x = 1\rlet y = 2\r"), "let x = 1\nlet y = 2\n");
        // The printer writes the line breaks of a comment it reindents.
        let formatted = format("let x = 1\n/* a\r\r\n b */\nlet y = 2\n");
        assert_eq!(formatted, "let x = 1\n/* a\n b */\nlet y = 2\n");
        assert_eq!(format(&to_crlf(&formatted)), to_crlf(&formatted));
        let unformatted = super::format_source(b"let  x  =  1\r\n", "A.res").unwrap();
        assert_eq!(unformatted, b"let x = 1\r\n");
    }

    /// tests/syntax_tests/res_test.ml:95-142: the first line break outside
    /// literals and comments gives the line endings, also with no line break
    /// or no final one, and after a regex, a JSX closing tag or a division
    /// that holds what would otherwise start a literal. Lookahead that reads
    /// the text of a template as code does not count.
    #[test]
    fn format_takes_line_endings_from_a_break_between_tokens() {
        let format = |source: &str| {
            String::from_utf8(super::format_source(source.as_bytes(), "A.res").unwrap()).unwrap()
        };
        for (source, expected) in [
            ("let a = 1", "let a = 1\n"),
            ("let a = \"x\r\ny\"", "let a = \"x\r\ny\"\n"),
            ("let a = 1 // c\r", "let a = 1 // c\n"),
            ("let a = \"x\r\ny\"\nlet b = 1", "let a = \"x\r\ny\"\n\nlet b = 1\n"),
            ("let a = \"x\ny\"\r\nlet b = 1", "let a = \"x\ny\"\r\n\r\nlet b = 1\r\n"),
            ("/* a\r\nb */\nlet b = 1\n", "/* a\n b */\nlet b = 1\n"),
            ("/* a\nb */\r\nlet b = 1\r\n", "/* a\r\n b */\r\nlet b = 1\r\n"),
            (
                "let a = 1 /* a\r\nb */\nlet b = 1\n",
                "let a = 1 /* a\n b */\n\nlet b = 1\n",
            ),
            (
                "let t = `${f({a: 1},\r\n 2)}`\nlet x = 1\n",
                "let t = `${f({a: 1}, 2)}`\r\nlet x = 1\r\n",
            ),
        ] {
            assert_eq!(format(source), expected, "{source:?}");
            assert_eq!(format(expected), expected, "{expected:?}");
        }
        for source in [
            "let a = \"x\r\ny\"\n\nlet b = 1\n",
            "let a = \"x\ny\"\r\n\r\nlet b = 1\r\n",
            "let c = '\"'\n\nlet s = \"a\r\nb\"\n",
            "let t = `a${b}c\r\nd`\n\nlet x = 1\n",
            "let t = `a${b}c\nd`\r\n\r\nlet x = 1\r\n",
            "let t = `${f({\n    \"a\": `${x}\r\n`,\n  })}\r\n`\n\nlet x = 1\n",
            "let t = `${switch x {\n  | _ => 1\n  }}\r\n`\n\nlet x = 1\n",
            "let r = /\"/\n\nlet s = \"a\r\nb\"\n",
            "let r = (1, /\"/)\n\nlet s = \"a\r\nb\"\n",
            "let x = a / f(\"/\")\r\nlet y = 2\r\n",
            "let x = a->f / g(\"/\")\r\nlet y = 2\r\n",
            "let e = (<a></a>, \"/\")\r\n\r\nlet s = \"a\nb\"\r\n",
            "let e = <a>{/\"/->f}</a>\r\n\r\nlet s = \"a\nb\"\r\n",
            "let t = `${/\"/->f}\r\n`\n\nlet x = 1\n",
            "/** a\r\nb */\nlet x = 1\n",
            "let e = (\r\n  <a />,\r\n  <a></a>,\r\n  \"x/y\nz\",\r\n)\r\n\r\nlet y = 2\r\n",
        ] {
            assert_eq!(format(source), source, "{source:?}");
        }
    }

    /// tests/syntax_tests/data/printer/expr/coerce.res:15-19: a labelled
    /// parameter's default is a constrained or coerced expression
    /// (res_core.ml:1931), so the printed defaults, which drop their
    /// parentheses as OCaml's printer does, parse and print again unchanged.
    #[test]
    fn labelled_default_is_constrained_or_coerced() {
        let source = b"let foo = (~a=(3:int), b) => 34\nlet foo = (~a=(3:>int), b) => 34\nlet foo = (~a=(3:int:>int), b) => 34\n";
        let printed = "let foo = (~a=3: int, b) => 34\nlet foo = (~a=3 :> int, b) => 34\nlet foo = (~a=(3: int) :> int, b) => 34\n";
        let formatted = super::format_source(source, "A.res").unwrap();
        assert_eq!(String::from_utf8_lossy(&formatted), printed);
        let again = super::format_source(&formatted, "A.res").unwrap();
        assert_eq!(String::from_utf8_lossy(&again), printed);
    }

    /// typecore.ml Pexp_try types the finally block with
    /// `~nonreturning_warning:false`: a finally block that always throws
    /// gets no warning 21, while a throw followed by code inside the block
    /// still does.
    #[test]
    fn finally_block_that_always_throws_has_no_nonreturning_warning() {
        let compile = |source: &str| {
            let options = super::CompilerOptions {
                nopervasives: true,
                ..Default::default()
            };
            super::compile_source_in_process(
                &format!(
                    "external throw: exn => 'a = \"%raise\"\nexternal log: int => unit = \"log\"\nexception B\n{source}"
                ),
                "Finally.res",
                "Finally",
                &options,
                &crate::cmi::persistent_env::ModuleRegistry::new(),
                false,
                None,
            )
            .expect("compiles")
            .warnings
        };
        for silent in [
            "let k = () => try { 1 } finally { throw(B) }\n",
            "let k = () => try { 1 } finally { log(1); throw(B) }\n",
            "let k = () => try { 1 } catch { | B => 2 } finally { throw(B) }\n",
        ] {
            let warnings = compile(silent);
            assert!(!warnings.contains("Warning number 21"), "{silent}: {warnings}");
        }
        let warnings = compile("let k = () => try { 1 } finally { throw(B); log(2) }\n");
        assert!(warnings.contains("Warning number 21"), "{warnings}");
    }

    /// typecore.ml's `labels_missing`: a literal of a record whose labels
    /// are all optional misses none, and one with required labels still
    /// lists every required label it leaves out, in declaration order.
    #[test]
    fn record_literal_missing_labels_with_optional_labels() {
        let compile = |source: &str| {
            let options = super::CompilerOptions {
                nopervasives: true,
                ..Default::default()
            };
            super::compile_source_in_process(
                source,
                "Missing.res",
                "Missing",
                &options,
                &crate::cmi::persistent_env::ModuleRegistry::new(),
                false,
                None,
            )
            .map(|result| result.js_output)
            .map_err(|err| format!("{err:#}"))
        };
        compile("type o = {a?: int, b?: string}\nlet r: o = {a: 1}\n").expect("compiles");
        let err = compile(
            "type t = {a?: int, b: string, c?: bool, mutable d: int}\nlet r: t = {a: 1}\n",
        )
        .expect_err("misses b and d");
        assert!(err.contains("Some required record fields are missing: b d."), "{err}");
    }

    /// ctype.ml `constructor_coercion`: a variant coercion that fails on an
    /// inline record's fields explains the first such constructor, naming
    /// its records `v1.C` and `v2.C` (printtyp.ml prints the source record
    /// first); a constructor that fails otherwise gives no reason.
    #[test]
    fn variant_coercion_explains_inline_record_fields() {
        let compile = |source: &str| {
            let options = super::CompilerOptions {
                nopervasives: true,
                ..Default::default()
            };
            super::compile_source_in_process(
                source,
                "Coerce.res",
                "Coerce",
                &options,
                &crate::cmi::persistent_env::ModuleRegistry::new(),
                false,
                None,
            )
            .map(|result| result.js_output)
            .map_err(|err| {
                // The record names are highlighted; compare the plain text.
                let text = format!("{err:#}");
                let mut plain = String::with_capacity(text.len());
                let mut rest = text.as_str();
                while let Some(start) = rest.find("\x1b[") {
                    plain.push_str(&rest[..start]);
                    let tail = &rest[start..];
                    rest = tail.find('m').map_or("", |end| &tail[end + 1..]);
                }
                plain.push_str(rest);
                plain
            })
        };
        let err = compile(
            "type v1 = A(int) | B({x: float}) | C({y: int}) | D\ntype v2 = A(int) | B({x: float}) | C({mutable y: int}) | D\nlet toV2 = (a: v1) => (a :> v2)\n",
        )
        .expect_err("y is mutable in v2.C");
        assert!(
            err.contains("The record v1.C cannot be coerced to the record v2.C because:"),
            "{err}"
        );
        assert!(
            err.contains("The field y is mutable in record v2.C, but not in record v1.C."),
            "{err}"
        );
        let err = compile(
            "type v1 = A({x: float})\ntype v2 = A({x: float, y: int})\nlet toV2 = (a: v1) => (a :> v2)\n",
        )
        .expect_err("y is missing in v1.A");
        assert!(
            err.contains("The field y is missing in record v1.A, but present in record v2.A"),
            "{err}"
        );
        let err = compile(
            "type x = {x: int}\ntype y = {x: int, z: int}\nlet toY = (a: x) => (a :> y)\n",
        )
        .expect_err("z is missing in x");
        assert!(
            err.contains("The field z is missing in record x, but present in record y"),
            "{err}"
        );
        let err = compile("type v1 = A(int)\ntype v2 = A(string)\nlet f = (a: v1) => (a :> v2)\n")
            .expect_err("payloads differ");
        assert!(!err.contains("cannot be coerced to the record"), "{err}");
    }

    /// GenTypeMain.ml:93-107's walk over a parsed interface whose `"BAD"`
    /// strings are replaced with a PPX's undecodable template `Fo\xo`:
    /// `Ok(ignore_interface)`, or the offset of the template it raised at.
    fn parsed_interface_walk(source: &str) -> Result<bool, i32> {
        let mut parser = crate::parser::Parser::new("A.resi", source);
        let signature = crate::parser::module::parse_signature(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        let mut arena = parser.into_arena();
        struct BadStrings(Vec<crate::parse_arena::ExprIdx>);
        impl crate::binary_ast::ast_iter::AstIter for BadStrings {
            fn expr(
                &mut self,
                arena: &crate::parse_arena::ParseArena,
                idx: crate::parse_arena::ExprIdx,
            ) {
                if let crate::parser::ast::ExpressionDesc::Pexp_constant(constant) =
                    &arena.get_expr(idx).pexp_desc
                    && let crate::parser::ast::Constant::String(value) = constant
                    && value.semantic(arena) == "BAD"
                {
                    self.0.push(idx);
                }
                crate::binary_ast::ast_iter::walk_expr(self, arena, idx);
            }
        }
        let mut found = BadStrings(Vec::new());
        crate::binary_ast::ast_iter::walk_signature(&mut found, &arena, &signature);
        let source_idx = arena.intern("Fo\\xo");
        for expr_idx in found.0 {
            let loc = arena.get_expr(expr_idx).pexp_loc;
            arena.get_expr_mut(expr_idx).pexp_desc =
                crate::parser::ast::ExpressionDesc::Pexp_template(Box::new(
                    crate::parser::ast::PexpTemplate {
                        source_segments: vec![crate::parser::ast::Loc {
                            txt: source_idx,
                            loc,
                        }],
                        values: vec![],
                    },
                ));
        }
        let ignore_interface = std::cell::Cell::new(false);
        match super::parsed_signature_read_input(&arena, &signature, &ignore_interface) {
            Ok(_) => Ok(ignore_interface.get()),
            Err(crate::gentype::annotation::InvalidEscape::Parsed(loc)) => {
                Err(arena.to_location(loc).loc_start.cnum)
            }
            Err(crate::gentype::annotation::InvalidEscape::Decl(_)) => unreachable!(),
        }
    }

    /// GenTypeMain.ml:93-107 records `@genType.ignoreInterface` only while
    /// walking up to the first annotated item, and reads no payload past it:
    /// an invalid one there neither raises nor selects the implementation.
    #[test]
    fn gentype_interface_walk_stops_at_the_first_annotated_item() {
        let annotated = "@genType let x: int\n";
        for (source, walked) in [
            (format!("@@genType.ignoreInterface\n{annotated}"), Ok(true)),
            (format!("{annotated}@@genType.ignoreInterface\n"), Ok(false)),
            (format!("{annotated}@@genType.ignoreInterface(\"BAD\")\n"), Ok(false)),
            (format!("@@genType.ignoreInterface(\"BAD\")\n{annotated}"), Err(26)),
            (format!("{annotated}@genType.as(\"BAD\") @genType let z: int\n"), Ok(false)),
            ("let x: int\n@@genType.ignoreInterface\n".to_string(), Ok(true)),
        ] {
            assert_eq!(parsed_interface_walk(&source), walked, "{source}");
        }
    }

    /// An in-process compile hands GenType's outcome to its caller, which
    /// applies it after writing the JavaScript (js_implementation.ml:164-171):
    /// the compile itself prints and writes nothing, so a compile that fails
    /// later, or is retried, leaves no GenType output.
    #[test]
    fn in_process_compile_leaves_gentype_output_to_the_caller() {
        let root = std::env::temp_dir().join(format!("gentype-deferred-{}", std::process::id()));
        std::fs::create_dir_all(root.join("src")).unwrap();
        let filename = root.join("src/Deferred.res");
        let options = super::CompilerOptions {
            gentype_config: Some(std::sync::Arc::new(
                crate::gentype::config::build_config_from_cli_args(
                    None,
                    &[
                        "-bs-project-root".to_string(),
                        root.to_string_lossy().into_owned(),
                        "-bs-gentype".to_string(),
                    ],
                ),
            )),
            ..Default::default()
        };
        let result = super::compile_source_in_process(
            "@genType(`x`) let x = 1\n",
            &filename.to_string_lossy(),
            "Deferred",
            &options,
            &crate::cmi::persistent_env::ModuleRegistry::new(),
            false,
            None,
        )
        .expect("compiles");
        let output = root.join("src/Deferred.gen.tsx");
        assert!(!output.exists());
        let outcome = result.gentype.expect("GenType ran");
        assert_eq!(outcome.notes.len(), 1, "{:?}", outcome.notes);
        assert!(outcome.notes[0].contains("Annotation payload is ignored"));
        let printed =
            super::apply_gentype_outcome(Some(outcome), "", &filename.to_string_lossy()).unwrap();
        assert!(printed.contains("Annotation payload is ignored"), "{printed}");
        assert!(output.exists());
    }

    /// bsc prints GenType's notes (its stdout) before the report of the
    /// exception GenType raised; a build shows them as rescript-ocaml shows
    /// bsc's stdout: not at all for a compile that succeeds, and after the
    /// warnings and the report (its stderr) for one that fails.
    #[test]
    fn build_shows_gentype_notes_only_after_a_gentype_failure() {
        let note = "\n  Warning genType\n  A.res:1:1-8\n  Annotation is ignored\n";
        let outcome = |result| crate::gentype::main::Outcome {
            notes: vec![note.to_string()],
            result,
            needs_locations: false,
        };
        let printed = super::apply_gentype_outcome(Some(outcome(Ok(None))), "", "A.res").unwrap();
        assert_eq!(printed, note);
        super::apply_gentype_outcome_in_build(Some(outcome(Ok(None))), "warning\n", "A.res")
            .unwrap();

        let report = || Err("report\n".to_string());
        let output = |error: anyhow::Error| {
            error
                .downcast::<super::UserDiagnostic>()
                .unwrap()
                .output()
                .to_string()
        };
        let bsc = super::apply_gentype_outcome(Some(outcome(report())), "warning\n", "A.res");
        assert_eq!(output(bsc.unwrap_err()), format!("warning\n{note}report\n"));
        let build =
            super::apply_gentype_outcome_in_build(Some(outcome(report())), "warning\n", "A.res");
        assert_eq!(
            output(build.unwrap_err()),
            format!("warning\nreport\n{note}")
        );
    }

    /// A GenType note quotes a location, so a compile from a location-free
    /// parse whose GenType prints one asks to be retried with locations, as
    /// for a warning, instead of rendering it from the location-free parse.
    #[test]
    fn location_free_compile_with_a_gentype_note_is_retried_with_locations() {
        let root = std::env::temp_dir().join(format!("gentype-unlocated-{}", std::process::id()));
        std::fs::create_dir_all(root.join("src")).unwrap();
        let filename = root.join("src/Unlocated.res").to_string_lossy().into_owned();
        let options = super::CompilerOptions {
            gentype_config: Some(std::sync::Arc::new(
                crate::gentype::config::build_config_from_cli_args(
                    None,
                    &[
                        "-bs-project-root".to_string(),
                        root.to_string_lossy().into_owned(),
                        "-bs-gentype".to_string(),
                    ],
                ),
            )),
            ..Default::default()
        };
        let registry = crate::cmi::persistent_env::ModuleRegistry::new();
        let compile = |source: &str| {
            let mut parser =
                crate::parser::Parser::with_locations(filename.clone(), source, false);
            let structure = crate::parser::module::parse_structure(&mut parser);
            let mut out = String::new();
            let frontend = super::run_implementation_frontend(
                &mut parser,
                structure,
                source,
                &filename,
                &options,
                &mut out,
            )
            .expect("frontend");
            let mut arena = parser.into_arena();
            assert!(!arena.stores_locations());
            crate::types::typecore::prepare_typecheck_arena(&mut arena);
            super::compile_preprocessed_structure_in_process(
                &arena,
                &frontend.structure,
                &filename,
                "Unlocated",
                &options,
                &registry,
                false,
            )
            .map(|result| result.gentype)
        };
        let error = compile("@genType(`x`) let x = 1\n").expect_err("retried");
        assert!(matches!(
            error.downcast_ref::<super::LocationRetry>(),
            Some(super::LocationRetry::Warning)
        ));
        // Without notes the location-free compile stands.
        let outcome = compile("@genType let x = 1\n").expect("compiles").expect("GenType ran");
        assert!(outcome.notes.is_empty() && !outcome.needs_locations);
    }

    use super::build_name_based_coercion;
    use super::extract_file_directives_from_structure;
    use super::normalize_load_path_entry;
    use crate::ident::Ident;
    use crate::parser::{Parser, module};
    use crate::types::decl::{
        AliasPresence, ModuleDeclaration, ModuleType, RecStatus, SignatureItem,
    };
    use crate::types::path::Path as TypePath;
    use crate::types::typedtree::ModuleCoercion;
    use std::path::PathBuf;

    #[test]
    fn spellcheck_choices_prepends_ties_like_ocaml() {
        let alternatives: Vec<String> = ["abce", "zzzz", "abcf", "abcd"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        assert_eq!(
            super::spellcheck_choices("abcx", &alternatives),
            vec!["abcd", "abcf", "abce"]
        );
        assert_eq!(
            super::spellcheck_choices("abcd", &alternatives),
            vec!["abcd"]
        );
        let mut scratch = Vec::new();
        assert_eq!(
            super::ocaml_edit_distance("abc", "bac", 1, &mut scratch),
            Some(1)
        );
        assert_eq!(
            super::ocaml_edit_distance("abcdef", "abc", 2, &mut scratch),
            None
        );
        assert_eq!(
            super::ocaml_edit_distance("kitten", "sitting", 3, &mut scratch),
            Some(3)
        );
    }

    #[test]
    fn normalize_load_path_entry_expands_relative_paths_against_cwd() {
        let cwd = std::path::Path::new("/repo/tests/tests/lib/rescript");
        let normalized =
            normalize_load_path_entry(std::path::Path::new("../../src"), None, Some(cwd));
        assert_eq!(normalized, PathBuf::from("/repo/tests/tests/src"));
        let normalized = normalize_load_path_entry(std::path::Path::new("."), None, Some(cwd));
        assert_eq!(normalized, PathBuf::from("/repo/tests/tests/lib/rescript"));
    }

    #[test]
    fn name_based_coercion_keeps_same_absent_module_alias_identity() {
        let module_id = Ident::create_local("Alias");
        let target_id = Ident::create_persistent("Alias_Target");
        let md = ModuleDeclaration {
            md_type: ModuleType::MtyAlias(
                AliasPresence::MtaAbsent,
                std::sync::Arc::new(TypePath::pident(target_id)),
            ),
            md_attributes: vec![],
            md_loc: crate::types::DeclLoc::none(),
            md_path: None,
        };
        let sig = vec![SignatureItem::SigModule(module_id, md, RecStatus::TrecNot)];

        let coercion = build_name_based_coercion(&sig, &sig);

        assert!(matches!(coercion, ModuleCoercion::Tcoerce_none));
    }

    #[test]
    fn normalize_load_path_entry_expands_plus_paths_from_stdlib() {
        let normalized = normalize_load_path_entry(
            std::path::Path::new("+compiler-libs"),
            Some(std::path::Path::new("/runtime/lib/rescript")),
            Some(std::path::Path::new("/repo")),
        );
        assert_eq!(
            normalized,
            PathBuf::from("/runtime/lib/rescript/compiler-libs")
        );
    }

    #[test]
    fn release_optional_default_lowering_compiles_without_arena_aliasing() {
        let source = r#"
let labelled = (~x, ~y=2, ()) => x
let optional = (~x=?, ()) => x
"#;

        let output = super::compile_source_to_js(source, "core_patterns_optional_defaults.res")
            .expect("optional-default functions should compile");
        assert!(output.contains("function labelled"));
        assert!(output.contains("function optional"));
    }

    #[test]
    fn tuple_let_before_nested_optional_default_keeps_stamp_ownership() {
        const SOURCE: &str = r#"
let pair = x => (x, _ => ())

let makeUpdater = initialValue => {
  let (state, setState) = pair(0)
  let (value, setValue) = pair(initialValue)
  let updateValue = (~persist=true, newValue) => {
    if persist {
      setState(newValue)
    }
    setValue(value)
  }
  (state, value, updateValue)
}
"#;
        const CASES: [(&str, i32); 2] = [("fresh_worker_tls", 1000), ("reused_worker_tls", 8192)];

        let mut observations = Vec::new();
        for (case, tls_start) in CASES {
            let observation = std::thread::spawn(move || {
                Ident::set_current_time(tls_start);
                let mut trace = super::PreJsDiscriminatorTrace::default();
                let output = super::compile_source_to_js_with_trace(
                    SOURCE,
                    "hooks_settings_reduced.res",
                    &mut trace,
                )
                .expect("reduced Hooks stamp discriminator should compile");
                (case, tls_start, trace, output)
            })
            .join()
            .expect("owned discriminator thread should not panic");
            observations.push(observation);
        }

        // Preserve both complete traces before checking any invariant so a red
        // assertion still leaves the first execution evidence in test output.
        for (case, tls_start, trace, output) in &observations {
            eprintln!(
                "[hooks-prejs-discriminator] case={case} tls_start={tls_start} type_context_stamp={} raw_converter_stamp={} raw_max_stamp={}\n[raw]\n{}\n[lowered]\n{}\n[js-ir]\n{}\n[js]\n{}",
                trace.type_context_stamp,
                trace.raw_converter_stamp,
                trace.raw_max_stamp,
                trace.raw_lambda,
                trace.lowered_lambda,
                trace.js_program,
                output
            );
        }

        for (case, _, trace, output) in observations {
            assert!(
                trace.raw_max_stamp <= trace.raw_converter_stamp,
                "{case}: RawLambda contains an identifier above the reported raw stamp (raw_max={}, reported={}, type_context={})",
                trace.raw_max_stamp,
                trace.raw_converter_stamp,
                trace.type_context_stamp
            );
            // The typechecker names the optional parameter `persistOpt`
            // (typecore.ml `type_function`'s structural optional default).
            assert!(
                trace.raw_lambda.contains("persistOpt/"),
                "{case}: raw function lost the optional source parameter"
            );
            assert!(
                output.contains("(persistOpt, newValue)"),
                "{case}: JS-visible optional parameter was remapped"
            );
        }
    }

    #[test]
    fn release_synthetic_record_labels_and_qualified_paths_are_stable() {
        let source = r#"
module M = {
  type t = {x: int, y: int, optional?: string}
  let value = {x: 1, y: 2}
}

let extract = ({M.x, y: _}: M.t) => x
let value: M.t = {M.x: 3, y: 4}
"#;

        let output = super::compile_source_to_js(source, "synthetic_record_labels.res")
            .expect("synthetic record labels and qualified paths should compile");
        assert!(output.contains("function extract"));
        assert!(output.contains("value"));
    }

    #[test]
    fn extract_file_directives_preserves_source_order() {
        let mut parser = Parser::new(
            "directives.res",
            "@@directive(\"first directive;\")\n@@directive(\"second directive;\")\nlet a = 1",
        );
        let structure = module::parse_structure(&mut parser);

        assert!(!parser.has_errors());
        assert_eq!(
            extract_file_directives_from_structure(&structure, parser.arena()).unwrap(),
            vec![
                "first directive;".to_string(),
                "second directive;".to_string()
            ]
        );
    }
}

#[cfg(test)]
mod package_location_identity_tests {
    use super::*;

    #[test]
    fn package_relative_identity_survives_relocation_without_collisions() {
        let mut options = CompilerOptions {
            package_name: Some("@rescript/runtime".into()),
            package_root: Some(PathBuf::from("build/runtime")),
            ..Default::default()
        };
        assert_eq!(options.location_identity("build/runtime/src/Module.res"), "@rescript/runtime/src/Module.res");
        assert_eq!(options.location_identity("build/runtime-other/Module.res"), "@rescript/runtime/build/runtime-other/Module.res");
        assert_eq!(options.location_identity("src/Module.res"), "@rescript/runtime/src/Module.res");
        options.package_root = Some(PathBuf::from("installed/runtime"));
        assert_eq!(options.location_identity("installed/runtime/src/Module.res"), "@rescript/runtime/src/Module.res");
        assert_ne!(options.location_identity("installed/runtime/src/Module.resi"), options.location_identity("installed/runtime/src/Module.res"));
        assert_ne!(options.location_identity("installed/runtime/other/Module.res"), options.location_identity("installed/runtime/src/Module.res"));
        options.package_name = Some("other-package".into());
        assert_eq!(options.location_identity("installed/runtime/src/Module.res"), "other-package/src/Module.res");
    }
}
