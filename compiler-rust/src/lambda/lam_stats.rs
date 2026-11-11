//! `Lam_stats`: identifier metadata shared by the optimizer passes over a
//! [`LamArena`](crate::lambda::arena::LamArena).
//!
//! Payloads are handles into the same arena as the program, so recording a
//! function body or a block element is a 4-byte copy, as the pointer
//! sharing of the OCaml record is.

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::ident::Ident;
use crate::lambda::arena::{ConstId, Lam};
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compile_context::{BoxedNullable, ExternalArityTable, RecFlag};

/// `Lam_id_kind.element`.
#[derive(Debug, Clone, Copy)]
pub enum Element {
    /// Nothing is known about the element.
    Na,
    /// The element is this simple expression.
    SimpleForm(Lam),
}

/// `Lam_id_kind.t`.
#[derive(Debug, Clone, Default)]
pub enum IdKind {
    /// An optional value with this payload.
    NormalOptional(Lam),
    /// An optional block with this payload and nullable kind.
    OptionalBlock(Lam, BoxedNullable),
    /// An immutable block with these elements.
    ImmutableBlock(Vec<Element>),
    /// A mutable block with these elements.
    MutableBlock(Vec<Element>),
    /// A constant.
    Constant(ConstId),
    /// A module.
    Module(Ident),
    /// A function.
    FunctionId {
        /// The function's arity.
        arity: Arity,
        /// The function's definition and whether it is recursive, when known.
        lambda: Option<(Lam, RecFlag)>,
    },
    /// An exception.
    Exception,
    /// A function parameter.
    Parameter,
    /// Nothing is known.
    #[default]
    Na,
}

/// What is known about each identifier, by identifier.
pub type IdentTable = HashMap<Ident, IdKind>;

/// `Lam_stats.t`.
#[derive(Debug, Clone)]
pub struct LamStats {
    /// The exported identifiers, as a set.
    pub export_idents: HashSet<Ident>,
    /// The exported identifiers, in export order.
    pub exports: Vec<Ident>,
    /// What is known about each identifier.
    pub ident_tbl: IdentTable,
    /// `Lam_compile_env.query_external_id_info` answers already fetched,
    /// per module and field.
    pub external_arities: ExternalArityTable,
    /// OCaml's global `Ident.currentstamp`, shared by every `Ident.rename`
    /// and `Ident.create` of the pipeline.
    pub id_gen: std::sync::Arc<crate::context::IdGenerator>,
}

impl LamStats {
    /// Metadata for a module exporting `exports`, with nothing known yet.
    pub fn new(exports: Vec<Ident>) -> Self {
        let export_idents: HashSet<Ident> = exports.iter().cloned().collect();
        Self {
            export_idents,
            exports,
            ident_tbl: HashMap::new(),
            external_arities: ExternalArityTable::default(),
            id_gen: std::sync::Arc::new(crate::context::IdGenerator::new()),
        }
    }

    /// Whether `id` is exported.
    pub fn is_export(&self, id: &Ident) -> bool {
        self.export_idents.contains(id)
    }
}
