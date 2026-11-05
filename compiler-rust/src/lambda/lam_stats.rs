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
    Na,
    SimpleForm(Lam),
}

/// `Lam_id_kind.t`.
#[derive(Debug, Clone, Default)]
pub enum IdKind {
    NormalOptional(Lam),
    OptionalBlock(Lam, BoxedNullable),
    ImmutableBlock(Vec<Element>),
    MutableBlock(Vec<Element>),
    Constant(ConstId),
    Module(Ident),
    FunctionId {
        arity: Arity,
        lambda: Option<(Lam, RecFlag)>,
    },
    Exception,
    Parameter,
    #[default]
    Na,
}

pub type IdentTable = HashMap<Ident, IdKind>;

/// `Lam_stats.t`.
#[derive(Debug, Clone)]
pub struct LamStats {
    pub export_idents: HashSet<Ident>,
    pub exports: Vec<Ident>,
    pub ident_tbl: IdentTable,
    /// `Lam_compile_env.query_external_id_info` answers already fetched,
    /// per module and field.
    pub external_arities: ExternalArityTable,
    /// OCaml's global `Ident.currentstamp`, shared by every `Ident.rename`
    /// and `Ident.create` of the pipeline.
    pub id_gen: std::sync::Arc<crate::context::IdGenerator>,
}

impl LamStats {
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

    pub fn is_export(&self, id: &Ident) -> bool {
        self.export_idents.contains(id)
    }
}
