//! R3 skeleton: the declaration facts unification asks for, expansion of
//! abbreviations and its two memos. Bodies are built by slices R3b and R3d
//! (CHECKER_REWRITE.md, "R3 as designed"); every signature, size and stated
//! cost here is fixed.
//!
//! A constructor node's `a` is a *type index*: a row of [`TypeTable`]. For a
//! graph made from a segment it is the segment's `paths` row
//! (bridge/from_old.rs), so two constructor nodes name the same type exactly
//! when their `a` are equal (`Path.same`).
//!
//! The memo of a constructor with arguments is list slot 0 of the node
//! (CHECKER_REWRITE 3.2), with [`MEMO_PRIVATE`] in the node's head when the
//! expansion was a private one. The memo of a nullary constructor is one row
//! of [`Memo::simple`] per type index, shared by every node of that type
//! (`simple_abbrevs`, compiler/ml/ctype.ml:197-202), and slot 0 of a nullary
//! node stays `NONE`.

use super::graph::{Node, Ty};
use super::segment::Segment;
use super::template::Template;
use super::unify::{Checker, Clash};

/// [`TypeInfo::flags`]: the type has a manifest that expands publicly.
pub const ABBREV: u8 = 1;
/// The manifest is private: only [`ExpandMode::Opt`] and [`ExpandMode::Rigid`]
/// expand it (`expand_abbrev_opt`, compiler/ml/ctype.ml:1311).
pub const PRIVATE: u8 = 2;
/// The path is another spelling of the type `manifest` names (a type reached
/// through a module alias); it expands to a constructor node of that type
/// with the same arguments (compiler/ml/ctype.ml:1211-1214).
pub const ALIAS: u8 = 4;
/// A locally abstract type that an equation may refine (`is_newtype`,
/// `is_instantiable`; compiler/ml/ctype.ml:1803). Read by R3h.
pub const NEWTYPE: u8 = 8;
/// A record, a variant or an open type (`expands_to_datatype`,
/// compiler/ml/ctype.ml:2372). Read by R3h.
pub const DATATYPE: u8 = 16;
/// Head flag of a constructor node whose slot 0 holds a private expansion
/// (`Mcons (Private, ..)`, compiler/ml/btype.ml:612). Bit 4 is
/// `segment::EXTENDED`.
pub const MEMO_PRIVATE: u32 = 1 << 5;

/// What expansion and unification read about one type constructor. One row
/// per type index, read with one indexed load.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct TypeInfo {
    /// A [`TypeTable::manifests`] row, or the target type index for
    /// [`ALIAS`], or `NONE`.
    pub manifest: u32,
    /// The level below which a node of this type may not be lowered
    /// (`get_level`, compiler/ml/ctype.ml:562); 0 for a type with no scope.
    pub scope: u32,
    /// A [`TypeTable::newtypes`] row or `NONE`.
    pub newtype: u32,
    pub arity: u16,
    pub flags: u8,
    pub reserved: u8,
}

/// The scheme an expansion instantiates: the parameters and the body are
/// roots of one template, so a parameter that occurs in the body is one node
/// (`instance_parameterized_type`, compiler/ml/ctype.ml:982).
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct Manifest {
    pub template: Template,
    /// First of `arity` consecutive [`TypeTable::roots`] entries.
    pub params: u32,
    /// The body, as a template reference (bit 30: relative to the instance).
    pub body: Ty,
}

/// `type_newtype_level` of a locally abstract type (compiler/ml/ctype.ml:1806).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Newtype {
    pub level: u32,
    pub expansion_level: u32,
}

/// Dense declaration facts, indexed by type index. A type index past the end
/// of `rows` is an abstract type with no scope.
#[derive(Default)]
pub struct TypeTable {
    pub rows: Vec<TypeInfo>,
    pub manifests: Vec<Manifest>,
    pub roots: Vec<Ty>,
    pub newtypes: Vec<Newtype>,
    /// Number of rows with a non-zero `scope`: when 0, lowering never tests a
    /// scope ([`Checker::lower`]).
    pub scoped: u32,
}

impl TypeTable {
    /// O(paths + type declarations of the segment), one pass, no hashing: a
    /// row per `paths` row; the rows of the unit's own type declarations
    /// carry their arity, [`ABBREV`]/[`PRIVATE`]/[`DATATYPE`] and a manifest
    /// whose template is the declaration's item template
    /// (bridge/from_old.rs, "Schemes"). Templates stay in the segment's
    /// graph (`Segment::graph`). (R3b)
    pub fn from_segment(segment: &Segment) -> TypeTable {
        todo!("R3b")
    }

    /// O(1): one bounds test and one 16-byte load. (R3b)
    #[inline]
    pub fn info(&self, type_index: u32) -> TypeInfo {
        todo!("R3b")
    }
}

/// The memo of nullary constructors: one row per type index.
/// `find_repr` reads `node` (compiler/ml/ctype.ml:720), `find_expans` reads
/// `expansion` and, for a private lookup that finds no public one,
/// `private_expansion` (compiler/ml/btype.ml:612). A row is live when its
/// `generation` is [`Memo::generation`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct SimpleMemo {
    /// The constructor node whose public expansion is memorized, or `NONE`.
    pub node: Ty,
    pub expansion: Ty,
    pub private_expansion: Ty,
    pub generation: u32,
}

/// Both memos' bookkeeping. `cleanup_abbrev` is O(1) for the nullary memo
/// (a generation) and O(slots written since the last cleanup) for slot 0.
pub struct Memo {
    pub simple: Vec<SimpleMemo>,
    pub generation: u32,
    /// Live rows of `simple`: when 0, an instance or a copy makes no memo
    /// lookup at all ([`Checker::instance`]).
    pub live: u32,
    /// Constructor nodes whose slot 0 was written since the last cleanup
    /// (`Btype.memo`, compiler/ml/btype.ml:621).
    pub memorized: Vec<Ty>,
    /// The scope of the last expansion (`previous_env`,
    /// compiler/ml/ctype.ml:1163).
    pub env: u32,
}

impl Default for Memo {
    /// O(1), allocates nothing.
    fn default() -> Self {
        Memo {
            simple: Vec::new(),
            generation: 1,
            live: 0,
            memorized: Vec::new(),
            env: super::graph::NONE,
        }
    }
}

/// Which abbreviations a head expansion goes through.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ExpandMode {
    /// `expand_head_unif` (compiler/ml/ctype.ml:1279): public; a clash while
    /// binding the parameters is the caller's clash.
    Unif,
    /// `expand_head` (compiler/ml/ctype.ml:1283): public; a clash while
    /// binding the parameters stops the expansion and is undone.
    Safe,
    /// `expand_head_opt` (compiler/ml/ctype.ml:1323): private ones too.
    Opt,
    /// `expand_head_rigid` (compiler/ml/ctype.ml:3184): as `Opt`, with
    /// polymorphic variant rows kept rigid. Read by R3i.
    Rigid,
}

impl Checker {
    /// O(1) when `env` is the scope of the last expansion; otherwise one
    /// [`Checker::cleanup_abbrev`]. `check_abbrev_env`,
    /// compiler/ml/ctype.ml:1163. (R3b)
    pub fn set_env(&mut self, env: u32) {
        todo!("R3b")
    }

    /// O(slot-0 memos written since the last cleanup): clear each, drop the
    /// list, and advance the nullary memo's generation (one store).
    /// `Btype.cleanup_abbrev`, compiler/ml/btype.ml:623. Not logged in the
    /// trail: a restore runs a cleanup (compiler/ml/btype.ml:779). (R3b)
    pub fn cleanup_abbrev(&mut self) {
        todo!("R3b")
    }

    /// O(1): the memorized expansion of constructor node `ty` for a public
    /// (`private == false`) or private lookup, or `NONE`. One node load, then
    /// one list load (arguments) or one `simple` row load (nullary).
    /// `find_expans`, compiler/ml/btype.ml:612. (R3b)
    pub fn find_expansion(&self, ty: Ty, private: bool) -> Ty {
        todo!("R3b")
    }

    /// O(1): the node a copy of a nullary constructor of this type links to,
    /// or `NONE`: one `simple` row load and one compare. `find_repr`,
    /// compiler/ml/ctype.ml:720. (R3b)
    #[inline]
    pub fn find_repr(&self, type_index: u32) -> Ty {
        todo!("R3b")
    }

    /// Amortized O(1): record `expansion` for constructor node `ty` (slot 0
    /// and the head bit, or the `simple` row). `memorize_abbrev`,
    /// compiler/ml/btype.ml:629. (R3b)
    pub fn memorize(&mut self, ty: Ty, expansion: Ty, private: bool) {
        todo!("R3b")
    }

    /// O(1): drop the memorized expansion of constructor node `ty`.
    /// `forget_abbrev`, compiler/ml/btype.ml:646. (R3b; called by R3c)
    pub fn forget_abbrev(&mut self, ty: Ty) {
        todo!("R3b")
    }

    /// One step of expansion of constructor node `ty` (a representative).
    /// `Ok(NONE)` when it does not expand (`Cannot_expand`). A memo hit is
    /// O(1) plus one [`Checker::lower`] of the expansion to the node's level
    /// (one step when it is already there). A miss is one instance of the
    /// manifest's template at the node's level (O(template)), one link per
    /// parameter, and one `memorize`, written before the body is made
    /// (`subst`, compiler/ml/ctype.ml:1113). An [`ALIAS`] row makes one
    /// constructor node of the target type sharing the argument list.
    /// `expand_abbrev_gen`, compiler/ml/ctype.ml:1187. (R3b)
    pub fn expand_once(&mut self, ty: Ty, mode: ExpandMode) -> Result<Ty, Clash> {
        todo!("R3b")
    }

    /// The head of `ty` after every expansion `mode` allows: a loop of
    /// [`Checker::expand_once`], O(expansions), O(1) machine stack. Returns
    /// the representative it stops at. `try_expand_head`,
    /// compiler/ml/ctype.ml:1267-1325. In `Safe` mode a clash inside one step
    /// is undone with a speculation opened for that step only when the
    /// type's parameters are constrained. (R3b)
    pub fn expand_head(&mut self, ty: Ty, mode: ExpandMode) -> Result<Ty, Clash> {
        todo!("R3b")
    }

    /// An instance of a template, with the copy-time lookup of O11: when
    /// `memo.live` is 0 this is `Graph::instance` and costs it plus one load
    /// and one untaken branch; otherwise one more pass over the new nodes,
    /// one `find_repr` per nullary constructor, each hit rewriting the new
    /// node into a link (`Some ty when repr ty != t -> Tlink ty`,
    /// compiler/ml/ctype.ml:781). (R3b)
    pub fn instance(&mut self, template: Template) -> Ty {
        todo!("R3b")
    }

    /// The general copy with the same lookup: `Graph::copy` when
    /// `memo.live` is 0, otherwise one `find_repr` per copied nullary
    /// constructor. compiler/ml/ctype.ml:744-797. (R3b)
    pub fn copy(&mut self, root: Ty) -> Ty {
        todo!("R3b")
    }

    /// Lower every node reachable from `root` to at most `level`
    /// (`update_level`, compiler/ml/ctype.ml:584-640). When
    /// `types.scoped` is 0 this is `Graph::lower` plus one compare. Otherwise
    /// each constructor node above `level` costs one `TypeInfo` load; a node
    /// whose type's scope is above `level` is replaced by its expansion
    /// (a link, then the walk continues on the expansion) or is a clash.
    /// The walk is tried without expanding constructors that have arguments,
    /// and, after a clash, restored and run again expanding them: the
    /// speculation for that is opened only on this path. Explicit stack. (R3d)
    pub fn lower(&mut self, root: Ty, level: u32) -> Result<(), Clash> {
        todo!("R3d")
    }

    /// `lower_args` of the old checker (types/ctype.rs:11682), the walk an
    /// application runs over the callee's instance: O(nodes above the
    /// current level), expanding a nullary abbreviation it meets so that the
    /// nullary memo names that node. (R3d)
    pub fn lower_args(&mut self, root: Ty) {
        todo!("R3d")
    }
}

/// O(1): a node that is a link to `target`, keeping `node`'s level.
/// Shared by the memo lookups of `instance` and `copy`. (R3b)
pub(crate) fn link_node(node: Node, target: Ty) -> Node {
    todo!("R3b")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<TypeInfo>(), 16);
        assert_eq!(std::mem::size_of::<Manifest>(), 24);
        assert_eq!(std::mem::size_of::<Newtype>(), 8);
        assert_eq!(std::mem::size_of::<SimpleMemo>(), 16);
        assert_eq!(std::mem::size_of::<ExpandMode>(), 1);
    }
}
