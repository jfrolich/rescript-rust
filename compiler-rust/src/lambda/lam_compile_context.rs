//! Lambda compilation metadata.
//!
//! Identifier kinds, export/arity tables, and the `LamStats` record shared
//! by the Lambda passes and the JS backend (OCaml `Lam_stats`).

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::ident::Ident;
use crate::lambda::Lambda;
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_constant::Constant;

/// Recursion flag for functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum RecFlag {
    /// Recursive function
    Rec,
    /// Non-recursive function
    NonRec,
    /// Self-recursive function (special case)
    SelfRec,
}

/// Element in a block.
#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum Element {
    /// No information available
    Na,
    /// Simple form - can be substituted
    SimpleForm(Lambda),
}

/// Nullable kind for optional values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoxedNullable {
    Undefined,
    Null,
    NullUndefined,
}

/// Information about an identifier's kind.
///
/// This tracks what kind of value an identifier is bound to,
/// which helps with optimization and code generation.
#[derive(Debug, Clone, Default)]
pub enum IdKind {
    /// Optional value with normal null handling
    NormalOptional(Lambda),
    /// Optional block with nullable kind
    OptionalBlock(Lambda, BoxedNullable),
    /// Immutable block (tuple, record)
    ImmutableBlock(Vec<Element>),
    /// Mutable block
    MutableBlock(Vec<Element>),
    /// Constant value
    Constant(Constant),
    /// Module reference
    Module(Ident),
    /// Function with arity information
    FunctionId {
        arity: Arity,
        lambda: Option<(Lambda, RecFlag)>,
    },
    /// Exception identifier
    Exception,
    /// Function parameter
    Parameter,
    /// No specific information (default)
    #[default]
    Na,
}

/// Identifier table for tracking identifier kinds.
pub type IdentTable = HashMap<Ident, IdKind>;

#[derive(Debug, Clone)]
pub enum ExternalArityInfo {
    Single(Arity),
    Submodule(Vec<Arity>),
}

pub type ExternalArityFieldTable = HashMap<String, Option<ExternalArityInfo>>;

/// `Lam_compile_env.query_external_id_info` results, per module and field.
pub type ExternalArityTable = HashMap<String, ExternalArityFieldTable>;

/// Lambda compilation statistics and metadata.
#[derive(Debug, Clone)]
pub struct LamStats {
    /// Set of export identifiers
    pub export_idents: HashSet<Ident>,
    /// List of exports (in order)
    pub exports: Vec<Ident>,
    /// Identifier kind table
    pub ident_tbl: IdentTable,
    /// Arity metadata loaded from dependency `.cmj` entries.
    ///
    /// OCaml's `Lam_arity_analysis.get_arity` queries
    /// `Lam_compile_env.query_external_id_info` directly
    /// (compiler/core/lam_arity_analysis.ml:43-71). Rust keeps the resolved
    /// metadata here so the later collect/alpha passes can consult it without
    /// probing the filesystem themselves.
    pub external_arities: ExternalArityTable,
    /// Shared stamp counter for `Ident::rename` calls across the pipeline.
    ///
    /// OCaml's `Ident.rename` consults a single global mutable counter, so every
    /// freshly-renamed ident gets a stamp unused anywhere else. The Rust pipeline
    /// previously created a new `IdGenerator::with_start_stamp(max_ident_stamp(..))`
    /// inside each beta-reduce call, which made two inlinings of the same function
    /// produce colliding stamps (e.g. two `let prim` bindings at module top level
    /// in `coercion_module_alias_test`). Threading this shared counter through the
    /// simplify pipeline preserves OCaml's invariant.
    pub id_gen: std::sync::Arc<crate::context::IdGenerator>,
    /// Whether collect stores inlinable function bodies in `FunctionId`.
    /// Only `remove_alias` reads them, so a collect whose table is fully
    /// re-collected before the next `simplify_alias` can skip the copies.
    pub(crate) collect_function_payloads: bool,
}

impl LamStats {
    /// Create a new LamStats with the given exports.
    pub fn new(exports: Vec<Ident>) -> Self {
        let export_idents: HashSet<Ident> = exports.iter().cloned().collect();
        Self {
            export_idents,
            exports,
            ident_tbl: HashMap::new(),
            external_arities: ExternalArityTable::default(),
            id_gen: std::sync::Arc::new(crate::context::IdGenerator::new()),
            collect_function_payloads: true,
        }
    }

    /// Check if an identifier is exported.
    pub fn is_export(&self, id: &Ident) -> bool {
        self.export_idents.contains(id)
    }

    /// Get the kind of an identifier.
    pub fn get_kind(&self, id: &Ident) -> Option<&IdKind> {
        self.ident_tbl.get(id)
    }

    /// Set the kind of an identifier.
    pub fn set_kind(&mut self, id: Ident, kind: IdKind) {
        self.ident_tbl.insert(id, kind);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lam_stats_creation() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let stats = LamStats::new(vec![x, y]);

        assert!(stats.is_export(&x));
        assert!(stats.is_export(&y));
        assert!(!stats.is_export(&Ident::create_local("z")));
    }

    #[test]
    fn test_id_kind() {
        let x = Ident::create_local("x");
        let mut stats = LamStats::new(vec![]);

        stats.set_kind(x, IdKind::Parameter);
        assert!(matches!(stats.get_kind(&x), Some(IdKind::Parameter)));

        stats.set_kind(
            x,
            IdKind::FunctionId {
                arity: Arity::info(vec![2], false),
                lambda: None,
            },
        );
        assert!(matches!(
            stats.get_kind(&x),
            Some(IdKind::FunctionId { .. })
        ));
    }
}
