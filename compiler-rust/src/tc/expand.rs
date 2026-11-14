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

use super::graph::{NONE, Node, Ty};
use super::segment::{DeclarationKind, PathRow, Segment, SignatureKind};
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
/// `is_instantiable`; compiler/ml/ctype.ml:1862-1880). Read by R3h.
pub const NEWTYPE: u8 = 8;
/// A record, a variant or an open type (`expands_to_datatype`,
/// compiler/ml/ctype.ml:1887). Read by R3h.
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

/// `type_newtype_level` of a locally abstract type (compiler/ml/ctype.ml:562-569).
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
    ///
    /// A `paths` row names one of the unit's own declarations when it is an
    /// identifier whose scope is the `ordered_items` index of a type item
    /// (`IdentRow::scope`; equal stamps, compiler/ext/ident.ml:75). Every
    /// other row (predefined types, other units' types, a path through a
    /// module) is an abstract type here. The scope is 0 for every row: a
    /// segment's types are bound before any level a check reaches.
    pub fn from_segment(segment: &Segment) -> TypeTable {
        let pools = &segment.signature;
        let mut table = TypeTable {
            rows: Vec::with_capacity(pools.paths.len()),
            ..TypeTable::default()
        };
        for path in pools.paths.iter() {
            #[cfg(test)]
            super::steps::tick();
            let row = match own_declaration(segment, *path) {
                Some(declaration) => table.declaration_row(segment, declaration),
                None => ABSTRACT,
            };
            table.rows.push(row);
        }
        table
    }

    /// O(arity): the row of type declaration `declaration` of the segment,
    /// appending its manifest and its parameter roots. A manifest expands
    /// publicly unless the type is private and abstract
    /// (`Env.find_type_expansion`, compiler/ml/env.ml:944-957; a private row
    /// type, `Btype.has_constr_row`, is R3f's).
    fn declaration_row(&mut self, segment: &Segment, declaration: u32) -> TypeInfo {
        let pools = &segment.signature;
        let decl = segment.type_declarations[declaration as usize];
        let mut flags = 0;
        if decl.kind != DeclarationKind::Abstract {
            flags |= DATATYPE;
        }
        let newtype = if decl.flags & DECL_NEWTYPE != 0 {
            let details = pools.type_details[declaration as usize];
            self.newtypes.push(Newtype {
                level: details.newtype_level,
                expansion_level: details.scope_level,
            });
            flags |= NEWTYPE;
            self.newtypes.len() as u32 - 1
        } else {
            NONE
        };
        let manifest = if decl.manifest == NONE {
            NONE
        } else {
            let private = decl.flags & DECL_PRIVATE != 0;
            flags |= if private && decl.kind == DeclarationKind::Abstract {
                PRIVATE
            } else {
                ABBREV
            };
            let body = pools.roots[decl.manifest as usize];
            let params = self.roots.len() as u32;
            for index in 0..u32::from(decl.arity) {
                #[cfg(test)]
                super::steps::tick();
                self.roots.push(pools.roots[(decl.params + index) as usize].ty);
            }
            self.manifests.push(Manifest {
                template: segment.templates[body.template as usize],
                params,
                body: body.ty,
            });
            self.manifests.len() as u32 - 1
        };
        TypeInfo {
            manifest,
            scope: 0,
            newtype,
            arity: decl.arity,
            flags,
            reserved: 0,
        }
    }

    /// O(1): one bounds test and one 16-byte load. (R3b)
    #[inline]
    pub fn info(&self, type_index: u32) -> TypeInfo {
        match self.rows.get(type_index as usize) {
            Some(&row) => row,
            None => ABSTRACT,
        }
    }
}

/// The row of a type with no manifest and no scope.
const ABSTRACT: TypeInfo = TypeInfo {
    manifest: NONE,
    scope: 0,
    newtype: NONE,
    arity: 0,
    flags: 0,
    reserved: 0,
};

/// `TypeDecl::flags` bits (bridge/from_old.rs, "Metadata").
const DECL_PRIVATE: u8 = 1;
const DECL_NEWTYPE: u8 = 8;

/// O(1): the `type_declarations` row a `paths` row names, when it is an
/// identifier bound by a type item of the segment.
fn own_declaration(segment: &Segment, path: PathRow) -> Option<u32> {
    let pools = &segment.signature;
    let PathRow::Ident(ident) = path else {
        return None;
    };
    let scope = pools.identifiers[ident as usize].scope;
    let item = pools.ordered_items.get(scope as usize)?;
    (item.kind == SignatureKind::Type).then_some(item.declaration)
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

    /// An instance of a template that drops variable names, as the old
    /// checker's does (`copy_type_desc`, compiler/ml/btype.ml:510; R3b makes
    /// `Graph::instance` and `Graph::copy` write no name), with the
    /// copy-time lookup of O11: when
    /// `memo.live` is 0 this is `Graph::instance` and costs it plus one load
    /// and one untaken branch; otherwise one more pass over the new nodes,
    /// one `find_repr` per nullary constructor, each hit rewriting the new
    /// node into a link (`Some ty when repr ty != t -> Tlink ty`,
    /// compiler/ml/ctype.ml:782). (R3b)
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

    /// `lower_args` of the old checker (types/ctype.rs:11682; OCaml
    /// compiler/ml/typecore.ml:2335-2342), which an application runs on the
    /// callee's instance: expand the head ([`ExpandMode::Safe`]); while it is
    /// an arrow, lower each parameter to the current level
    /// ([`Checker::lower`]) and go on with the result. O(arrows in the
    /// result chain) expansions plus the lowering. The expansion of a result
    /// that is a nullary abbreviation is what makes that node the nullary
    /// memo's representative (O11). (R3d)
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
    use super::super::segment::{
        IdentRow, ItemStatus, SchemeRoot, SignatureItemRow, SignaturePools, TypeDecl,
    };
    use super::super::steps;
    use super::*;

    const RELATIVE: u32 = 1 << 30;

    /// `from_segment` is one pass: one step per `paths` row and one per
    /// parameter root of a manifest, on 10,000 declarations.
    #[test]
    fn table_from_ten_thousand_declarations_is_one_pass() {
        let n = 10_000u32;
        let (mut identifiers, mut paths, mut items, mut decls, mut roots) =
            (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
        for i in 0..n {
            identifiers.push(IdentRow {
                name: 0,
                stamp: i as i32 + 1,
                flags: 0,
                scope: i,
            });
            paths.push(PathRow::Ident(i));
            items.push(SignatureItemRow {
                ident: i,
                declaration: i,
                kind: SignatureKind::Type,
                status: ItemStatus::Ordinary,
            });
            let params = roots.len() as u32;
            roots.push(SchemeRoot {
                template: 0,
                ty: Ty(RELATIVE | 1),
            });
            roots.push(SchemeRoot {
                template: 0,
                ty: Ty(RELATIVE | 2),
            });
            // Declaration 0 is private and abstract, 1 a private record.
            decls.push(TypeDecl {
                kind: if i == 1 {
                    DeclarationKind::Record
                } else {
                    DeclarationKind::Abstract
                },
                flags: 16 | u8::from(i < 2),
                arity: 1,
                params,
                manifest: params + 1,
                members: 0,
                member_len: 0,
                path: i,
                loc: NONE,
                variance: 0,
            });
        }
        // A path bound outside the segment.
        identifiers.push(IdentRow {
            name: 0,
            stamp: 0,
            flags: 0,
            scope: NONE,
        });
        paths.push(PathRow::Ident(n));
        let template = Template {
            nodes: 0,
            node_len: 3,
            pools: 0,
            list_len: 2,
        };
        let segment = Segment {
            templates: Box::new([template]),
            type_declarations: decls.into(),
            signature: SignaturePools {
                identifiers: identifiers.into(),
                paths: paths.into(),
                ordered_items: items.into(),
                roots: roots.into(),
                ..SignaturePools::default()
            },
            ..Segment::default()
        };
        let mut table = TypeTable::default();
        let count = steps::scope(|| table = TypeTable::from_segment(&segment));
        assert_eq!(count, 2 * u64::from(n) + 1);
        assert_eq!(table.rows.len(), n as usize + 1);
        assert_eq!(table.scoped, 0);
        assert_eq!(
            table.info(5),
            TypeInfo {
                manifest: 5,
                scope: 0,
                newtype: NONE,
                arity: 1,
                flags: ABBREV,
                reserved: 0,
            }
        );
        let manifest = table.manifests[5];
        assert_eq!(table.roots[manifest.params as usize], Ty(RELATIVE | 1));
        assert_eq!(manifest.body, Ty(RELATIVE | 2));
        assert_eq!(table.info(0).flags, PRIVATE);
        assert_eq!(table.info(1).flags, ABBREV | DATATYPE);
        assert_eq!(table.info(n), ABSTRACT);
        assert_eq!(table.info(n + 100), ABSTRACT);
    }

    /// On a compiled program: the paths of the unit's own types carry their
    /// declaration; a predefined type is abstract.
    #[test]
    fn table_from_a_compiled_unit_names_its_declarations() {
        use super::super::differential::{New, Tier, compile};
        let program = compile(
            "type t0\ntype t1<'a>\ntype a0 = int\ntype a1<'a> = ('a, t0)\n\
             type r = {n: int}\n\
             external v: (a0, a1<string>, t1<r>) = \"v\"\n"
                .to_string(),
        );
        let new = New::convert(&program, Tier::Kernel);
        let table = TypeTable::from_segment(&new.segment);
        let pools = &new.segment.signature;
        let mut seen = Vec::new();
        for (index, path) in pools.paths.iter().enumerate() {
            let PathRow::Ident(ident) = *path else { continue };
            let range = pools.strings[pools.identifiers[ident as usize].name as usize];
            let name = &pools.bytes[range.start as usize..(range.start + range.len) as usize];
            let name = std::str::from_utf8(name).unwrap();
            let info = table.info(index as u32);
            let (arity, flags) = (info.arity, info.flags);
            match name {
                "t0" => assert_eq!((arity, flags, info.manifest), (0, 0, NONE)),
                "t1" => assert_eq!((arity, flags, info.manifest), (1, 0, NONE)),
                "a0" => assert_eq!((arity, flags), (0, ABBREV)),
                "a1" => assert_eq!((arity, flags), (1, ABBREV)),
                "r" => assert_eq!((arity, flags), (0, DATATYPE)),
                "int" | "string" => assert_eq!(info, ABSTRACT),
                _ => continue,
            }
            seen.push(name.to_string());
        }
        for name in ["t1", "a0", "a1", "r", "int", "string"] {
            assert!(seen.iter().any(|seen| seen == name), "{name} not in {seen:?}");
        }
        let a1 = pools
            .paths
            .iter()
            .position(|path| match *path {
                PathRow::Ident(ident) => {
                    let range = pools.strings[pools.identifiers[ident as usize].name as usize];
                    &pools.bytes[range.start as usize..(range.start + range.len) as usize] == b"a1"
                }
                _ => false,
            })
            .unwrap();
        let manifest = table.manifests[table.info(a1 as u32).manifest as usize];
        // The parameter and the body are nodes of the item's template.
        assert_ne!(table.roots[manifest.params as usize].0 & RELATIVE, 0);
        assert_ne!(manifest.body.0 & RELATIVE, 0);
    }

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<TypeInfo>(), 16);
        assert_eq!(std::mem::size_of::<Manifest>(), 24);
        assert_eq!(std::mem::size_of::<Newtype>(), 8);
        assert_eq!(std::mem::size_of::<SimpleMemo>(), 16);
        assert_eq!(std::mem::size_of::<ExpandMode>(), 1);
    }
}
