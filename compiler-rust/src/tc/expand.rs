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

use super::graph::{ARROW, CONSTR, GENERIC, LINK, NONE, Node, TUPLE, Ty, VAR};
use super::segment::{DeclarationKind, PathRow, Segment, SignatureKind, UNIT_SCOPE};
use super::template::Template;
use super::unify::{Checker, Clash, Frame, FrameKind};

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
    /// O(paths + type declarations + strings of the segment), no hashing:
    /// one dense row per segment string ([`own_types`]), then one pass with a
    /// row per `paths` row; the rows of the unit's own type declarations
    /// carry their arity, [`ABBREV`]/[`PRIVATE`]/[`DATATYPE`] and a manifest
    /// whose template is the declaration's item template
    /// (bridge/from_old.rs, "Schemes"). Templates stay in the segment's
    /// graph (`Segment::graph`). (R3b)
    ///
    /// A `paths` row names one of the unit's own declarations when it is an
    /// identifier whose scope is the `ordered_items` index of a type item
    /// (`IdentRow::scope`; equal stamps, compiler/ext/ident.ml:75), or a
    /// path through the unit itself (`Case.t`, which is how the published
    /// types of a unit name its own types) whose name is a type item of the
    /// unit's signature. That join is on a string index, so it reads the
    /// dense row per segment string. Every other row (predefined
    /// types, other units' types, a path through a module) is an abstract
    /// type here. The scope is 0 for every row: a segment's types are bound
    /// before any level a check reaches.
    pub fn from_segment(segment: &Segment) -> TypeTable {
        let pools = &segment.signature;
        let mut table = TypeTable {
            rows: Vec::with_capacity(pools.paths.len()),
            ..TypeTable::default()
        };
        let by_name = own_types(segment);
        for path in pools.paths.iter() {
            #[cfg(test)]
            super::steps::tick();
            let row = match own_declaration(segment, &by_name, *path) {
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
/// identifier bound by a type item of the segment, or a path through the
/// unit itself whose name `by_name` maps to a declaration.
fn own_declaration(segment: &Segment, by_name: &[u32], path: PathRow) -> Option<u32> {
    let pools = &segment.signature;
    match path {
        PathRow::Ident(ident) => {
            let scope = pools.identifiers[ident as usize].scope;
            let item = pools.ordered_items.get(scope as usize)?;
            (item.kind == SignatureKind::Type).then_some(item.declaration)
        }
        PathRow::Dot { parent, name, .. } => {
            let PathRow::Ident(unit) = pools.paths[parent as usize] else {
                return None;
            };
            if pools.identifiers[unit as usize].scope != UNIT_SCOPE {
                return None;
            }
            let declaration = *by_name.get(name as usize)?;
            (declaration != NONE).then_some(declaration)
        }
        PathRow::Apply { .. } => None,
    }
}

/// O(strings + items of the unit's signature): the `type_declarations` row
/// of each type item of the unit's own signature, indexed by its name's
/// string, NONE elsewhere. A later item of a name hides an earlier one, as
/// in the export table. Empty for a segment with no signature.
fn own_types(segment: &Segment) -> Vec<u32> {
    let pools = &segment.signature;
    let Some(&items) = pools.signatures.first() else {
        return Vec::new();
    };
    let mut by_name = vec![NONE; pools.strings.len()];
    for item in &pools.ordered_items[items.start as usize..(items.start + items.len) as usize] {
        if item.kind == SignatureKind::Type {
            by_name[pools.identifiers[item.ident as usize].name as usize] = item.declaration;
        }
    }
    by_name
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
    /// (`Btype.memo`, compiler/ml/btype.ml:621), each held as the index of
    /// that slot 0 in the list pool: a node linked since then no longer
    /// holds its list, and a restore can bring the old descriptor back.
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
        if env != self.memo.env {
            self.cleanup_abbrev();
            self.memo.env = env;
        }
    }

    /// O(slot-0 memos written since the last cleanup): clear each, drop the
    /// list, and advance the nullary memo's generation (one store).
    /// `Btype.cleanup_abbrev`, compiler/ml/btype.ml:623. Not logged in the
    /// trail: a restore runs a cleanup (compiler/ml/btype.ml:779). (R3b)
    pub fn cleanup_abbrev(&mut self) {
        for &slot in &self.memo.memorized {
            #[cfg(test)]
            super::steps::tick();
            self.g.lists[slot.0 as usize] = Ty(NONE);
        }
        self.memo.memorized.clear();
        self.memo.generation = self
            .memo
            .generation
            .checked_add(1)
            .expect("memo generation exhausted");
        self.memo.live = 0;
    }

    /// O(1): forget the nullary memo and nothing else: no slot-0 memo is
    /// touched and no row is read. `simple_abbrevs () := Mnil`, the first
    /// step of every generalization (compiler/ml/ctype.ml:519, 543, 668).
    /// The generation advances only when a row is live, so generalizations
    /// that follow no nullary expansion cost one load and one untaken
    /// branch and never exhaust the generation. Not logged in the trail, as
    /// the memo is not. (R3b)
    #[inline]
    pub fn forget_simple_memo(&mut self) {
        if self.memo.live != 0 {
            self.memo.generation = self
                .memo
                .generation
                .checked_add(1)
                .expect("memo generation exhausted");
            self.memo.live = 0;
        }
    }

    /// [`Checker::forget_simple_memo`], then `Graph::generalize`: its cost
    /// plus O(1). `generalize`, compiler/ml/ctype.ml:518-520. Every
    /// generalization of the checker goes through here; `Graph::generalize`
    /// alone is the kernel's walk and forgets nothing. (R3b)
    pub fn generalize(&mut self, root: Ty) {
        self.forget_simple_memo();
        self.g.generalize(root);
    }

    /// [`Checker::forget_simple_memo`], then `Graph::generalize_structure`:
    /// its cost plus O(1). `generalize_structure`,
    /// compiler/ml/ctype.ml:542-544. (R3b)
    pub fn generalize_structure(&mut self, root: Ty, var_level: u32) {
        self.forget_simple_memo();
        self.g.generalize_structure(root, var_level);
    }

    /// O(1): the memorized expansion of constructor node `ty` for a public
    /// (`private == false`) or private lookup, or `NONE`. One node load, then
    /// one list load (arguments) or one `simple` row load (nullary).
    /// `find_expans`, compiler/ml/btype.ml:612. (R3b)
    pub fn find_expansion(&self, ty: Ty, private: bool) -> Ty {
        let node = self.g.nodes[ty.0 as usize];
        if node.arity() == 0 {
            return match self.memo.simple.get(node.a as usize) {
                Some(row) if row.generation == self.memo.generation => {
                    // A private lookup takes the newest entry of either
                    // kind; a public one is newer than a private one, which
                    // is memorized only when no expansion was found.
                    if private && row.expansion.0 == NONE {
                        row.private_expansion
                    } else {
                        row.expansion
                    }
                }
                _ => Ty(NONE),
            };
        }
        let slot = self.g.lists[node.b as usize];
        if private || node.head & MEMO_PRIVATE == 0 {
            slot
        } else {
            Ty(NONE)
        }
    }

    /// O(1): the node a copy of a nullary constructor of this type links to,
    /// or `NONE`: one `simple` row load and one compare. `find_repr`,
    /// compiler/ml/ctype.ml:720. (R3b)
    #[inline]
    pub fn find_repr(&self, type_index: u32) -> Ty {
        match self.memo.simple.get(type_index as usize) {
            Some(row) if row.generation == self.memo.generation => row.node,
            _ => Ty(NONE),
        }
    }

    /// Amortized O(1): record `expansion` for constructor node `ty` (slot 0
    /// and the head bit, or the `simple` row). `memorize_abbrev`,
    /// compiler/ml/btype.ml:629. (R3b)
    pub fn memorize(&mut self, ty: Ty, expansion: Ty, private: bool) {
        let node = self.g.nodes[ty.0 as usize];
        if node.arity() == 0 {
            let index = node.a as usize;
            if index >= self.memo.simple.len() {
                self.memo.simple.resize(index + 1, STALE);
            }
            let row = &mut self.memo.simple[index];
            if row.generation != self.memo.generation {
                *row = SimpleMemo {
                    generation: self.memo.generation,
                    ..STALE
                };
                self.memo.live += 1;
            }
            if private {
                row.private_expansion = expansion;
            } else {
                row.node = ty;
                row.expansion = expansion;
            }
            return;
        }
        // Slot 0 and the head bit are not logged: a restore runs a cleanup
        // (compiler/ml/btype.ml:779), and the bit is read only beside a slot.
        self.g.lists[node.b as usize] = expansion;
        let head = if private {
            node.head | MEMO_PRIVATE
        } else {
            node.head & !MEMO_PRIVATE
        };
        self.g.nodes[ty.0 as usize].head = head;
        self.memo.memorized.push(Ty(node.b));
    }

    /// O(1): drop the memorized expansion of constructor node `ty`.
    /// `forget_abbrev`, compiler/ml/btype.ml:646. (R3b; called by R3c)
    pub fn forget_abbrev(&mut self, ty: Ty) {
        let node = self.g.nodes[ty.0 as usize];
        if node.arity() != 0 {
            self.g.lists[node.b as usize] = Ty(NONE);
            return;
        }
        if let Some(row) = self.memo.simple.get_mut(node.a as usize)
            && row.generation == self.memo.generation
        {
            *row = STALE;
            self.memo.live -= 1;
        }
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
        let node = self.g.nodes[ty.0 as usize];
        if node.tag() != CONSTR {
            return Ok(Ty(NONE));
        }
        let private = matches!(mode, ExpandMode::Opt | ExpandMode::Rigid);
        let memorized = self.find_expansion(ty, private);
        if memorized.0 != NONE {
            // `update_level env level ty'` unless the node is generic; a
            // clash is ignored (compiler/ml/ctype.ml:1196-1201). The test
            // of the level is update_level's own first one (ctype.ml:586).
            let expansion = self.g.repr(memorized);
            if node.level != GENERIC && self.g.nodes[expansion.0 as usize].level > node.level {
                match self.lower(expansion, node.level) {
                    Ok(()) | Err(Clash) => {}
                }
            }
            return Ok(self.g.repr(expansion));
        }
        let info = self.types.info(node.a);
        if info.flags & ALIAS != 0 {
            return Ok(self.expand_alias(ty, node, info.manifest));
        }
        let expands = info.flags & ABBREV != 0 || (private && info.flags & PRIVATE != 0);
        if !expands {
            return Ok(Ty(NONE));
        }
        // `subst` raises `Unify []` on an arity mismatch (ctype.ml:1110).
        if u32::from(info.arity) != node.arity() {
            return Err(Clash);
        }
        self.subst(ty, node, info.manifest, mode)
    }

    /// O(1): the expansion of a path through a module alias, a constructor
    /// node of the target type at the node's level sharing its list (and
    /// with it the memo of a constructor with arguments, as OCaml's
    /// `newty2 level (Tconstr (path', args, abbrev))` shares `abbrev`,
    /// compiler/ml/ctype.ml:1211-1214). The old checker memorizes a nullary
    /// one in the nullary memo (CHECKER_REWRITE 8.6, decision 2), so this
    /// does too; one with arguments is not memorized, as the old checker's
    /// rewrite of a parameterised alias is not (types/ctype.rs, `Rewrite`).
    fn expand_alias(&mut self, ty: Ty, node: Node, target: u32) -> Ty {
        let expansion = self.g.push(Node {
            head: node.head & !MEMO_PRIVATE,
            a: target,
            ..node
        });
        if node.arity() == 0 {
            self.memorize(ty, expansion, false);
        }
        expansion
    }

    /// `subst` (compiler/ml/ctype.ml:1100-1123) for constructor node `ty`
    /// with `manifest`: the memo is written first, naming the body the
    /// instance is about to make; then one instance of the manifest's
    /// template at the node's level, O(template); then each fresh parameter
    /// variable is linked to its argument and the argument lowered to the
    /// node's level (`unify1_var`, ctype.ml:2216): O(arity) and one compare
    /// each. A parameter that is not a fresh variable (a constrained
    /// declaration) is unified with [`Checker::unify`]; in every mode but
    /// `Unif` that runs under a speculation opened at that parameter, and a
    /// clash restores it: `Safe` then does not expand (`try_expand_safe`,
    /// ctype.ml:1251) and `Opt` returns the clash to [`Checker::expand_head`].
    fn subst(&mut self, ty: Ty, node: Node, manifest: u32, mode: ExpandMode) -> Result<Ty, Clash> {
        let manifest = self.types.manifests[manifest as usize];
        let base = self.g.nodes.len() as u32;
        let relocate = |reference: Ty| {
            if reference.0 & RELATIVE != 0 {
                Ty(base + (reference.0 & !RELATIVE))
            } else {
                reference
            }
        };
        let body = relocate(manifest.body);
        let private = matches!(mode, ExpandMode::Opt | ExpandMode::Rigid);
        self.memorize(ty, body, private);
        let level = self.g.level;
        self.g.level = node.level;
        self.instance(manifest.template);
        self.g.level = level;
        let mut speculation = None;
        let mut result = Ok(());
        for index in 0..node.arity() {
            #[cfg(test)]
            super::steps::tick();
            let param = self.g.repr(relocate(self.types.roots[(manifest.params + index) as usize]));
            let argument = self.g.repr(self.g.lists[(node.b + 1 + index) as usize]);
            let fresh = param.0 >= base && self.g.nodes[param.0 as usize].tag() == VAR;
            if fresh {
                self.g.link(param, argument);
                if self.g.nodes[argument.0 as usize].level > node.level {
                    result = self.lower(argument, node.level);
                }
            } else {
                if mode != ExpandMode::Unif && speculation.is_none() {
                    speculation = Some(self.g.speculate());
                }
                result = self.unify(param, argument);
            }
            if result.is_err() {
                break;
            }
        }
        match (result, speculation) {
            (Ok(()), Some(token)) => self.g.keep(token),
            (Err(Clash), Some(token)) => {
                self.restore(token);
                return if mode == ExpandMode::Safe {
                    Ok(Ty(NONE))
                } else {
                    Err(Clash)
                };
            }
            (Ok(()), None) => {}
            (Err(Clash), None) => return Err(Clash),
        }
        Ok(self.g.repr(body))
    }

    /// The head of `ty` after every expansion `mode` allows: a loop of
    /// [`Checker::expand_once`], O(expansions), O(1) machine stack. Returns
    /// the representative it stops at. `try_expand_head`,
    /// compiler/ml/ctype.ml:1267-1325. In `Safe` mode a clash inside one step
    /// is undone with a speculation opened for that step only when the
    /// type's parameters are constrained. (R3b)
    pub fn expand_head(&mut self, ty: Ty, mode: ExpandMode) -> Result<Ty, Clash> {
        let original = self.g.repr(ty);
        let mut head = original;
        loop {
            #[cfg(test)]
            super::steps::tick();
            let next = match self.expand_once(head, mode) {
                Ok(next) => next,
                // `expand_head_opt` backtracks and returns the type it was
                // given (compiler/ml/ctype.ml:1330-1335).
                Err(Clash) if matches!(mode, ExpandMode::Opt | ExpandMode::Rigid) => {
                    return Ok(original);
                }
                // `try_expand_safe` turns a clash into `Cannot_expand`
                // (compiler/ml/ctype.ml:1251-1256).
                Err(Clash) if mode == ExpandMode::Safe => return Ok(head),
                Err(Clash) => return Err(Clash),
            };
            if next.0 == NONE {
                return Ok(head);
            }
            let next = self.g.repr(next);
            // A memo naming the node itself (PR#7324, ctype.ml:1202).
            if next == head {
                return Ok(head);
            }
            head = next;
        }
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
        if self.memo.live == 0 {
            return self.g.instance(template);
        }
        let first = self.g.nodes.len();
        let root = self.g.instance(template);
        self.link_memorized(first);
        root
    }

    /// The general copy with the same lookup: `Graph::copy` when
    /// `memo.live` is 0, otherwise one `find_repr` per copied nullary
    /// constructor. compiler/ml/ctype.ml:744-797. (R3b)
    pub fn copy(&mut self, root: Ty) -> Ty {
        if self.memo.live == 0 {
            return self.g.copy(root);
        }
        let first = self.g.nodes.len();
        let copied = self.g.copy(root);
        self.link_memorized(first);
        copied
    }

    /// O(nodes made since `first`): one step a node, one `find_repr` per
    /// nullary constructor. Each hit becomes a link to the memorized node
    /// (`Some ty when repr ty != t -> Tlink ty`, compiler/ml/ctype.ml:782):
    /// the memorized node is older than every node made since `first`, so
    /// the test against the copy itself always holds. A nullary
    /// constructor has no children, so rewriting it after the copy is the
    /// copy OCaml makes. The nodes are fresh: no trail entry.
    fn link_memorized(&mut self, first: usize) {
        for index in first..self.g.nodes.len() {
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[index];
            if node.tag() != CONSTR || node.arity() != 0 {
                continue;
            }
            let target = self.find_repr(node.a);
            if target.0 != NONE {
                self.g.nodes[index] = link_node(node, target);
            }
        }
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
    #[inline]
    pub fn lower(&mut self, root: Ty, level: u32) -> Result<(), Clash> {
        if self.types.scoped == 0 {
            self.g.lower(root, level);
            return Ok(());
        }
        // The outer `update_level` (compiler/ml/ctype.ml:633-640): nothing
        // to do, and no snapshot, when the root is not above `level`.
        let root = self.g.repr(root);
        if self.g.nodes[root.0 as usize].level <= level {
            return Ok(());
        }
        // First without expanding constructors that have arguments; after a
        // clash, `backtrack snap` (a restore with its memo cleanup) and once
        // more expanding them.
        let token = self.g.speculate();
        if self.lower_scoped(root, level, false).is_ok() {
            self.g.keep(token);
            return Ok(());
        }
        self.restore(token);
        // OCaml runs the second pass outside the snapshot and leaves what a
        // failed one wrote ("Levels should be restored", ctype.ml:599). Here
        // a clash leaves the graph as it was before the call: the writes are
        // undone, the memos are kept as OCaml keeps them (no `backtrack`).
        let token = self.g.speculate();
        let result = self.lower_scoped(root, level, true);
        match result {
            Ok(()) => self.g.keep(token),
            Err(Clash) => self.g.restore(token),
        }
        result
    }

    /// One pass of the inner `update_level env level expand`
    /// (compiler/ml/ctype.ml:584-630) from representative `root`, on
    /// [`Checker::frames`] above the length it finds (an expansion inside
    /// the walk may lower or unify, and those use the stack above it).
    /// Cost: one step and one node load per popped entry, one `TypeInfo`
    /// load per constructor above `level`, one push per child; each
    /// expansion is one [`Checker::expand_once`] and one link. Nodes are
    /// visited in OCaml's order (children pushed last first). On a clash the
    /// stack is cut back to where it was; the caller undoes the writes.
    fn lower_scoped(&mut self, root: Ty, level: u32, expand: bool) -> Result<(), Clash> {
        let base = self.frames.len();
        self.push_lowering(root);
        let result = self.lower_scoped_loop(base, level, expand);
        self.frames.truncate(base);
        result
    }

    /// The loop of [`Checker::lower_scoped`]: pops entries above `base`.
    /// Its cost is the caller's.
    fn lower_scoped_loop(&mut self, base: usize, level: u32, expand: bool) -> Result<(), Clash> {
        while self.frames.len() > base {
            let ty = self.frames.pop().expect("entry above base").left;
            let ty = self.g.repr(ty);
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[ty.0 as usize];
            if node.level <= level {
                continue;
            }
            if node.tag() == CONSTR {
                // `level < get_level env p` (ctype.ml:590).
                let escapes = level < self.types.info(node.a).scope;
                if escapes || (expand && node.arity() != 0) {
                    // `link_type ty (try_expand_once env ty)`, then the walk
                    // goes on from `ty`, now a link to the expansion
                    // (ctype.ml:593-594, 603-604). A `Unify` raised by the
                    // expansion is not caught there: it is this pass's clash.
                    let expansion = self.expand_once(ty, ExpandMode::Unif)?;
                    let expansion = if expansion.0 == NONE {
                        expansion
                    } else {
                        self.g.repr(expansion)
                    };
                    // A memo naming the node itself (PR#7324,
                    // ctype.ml:1202) is no expansion here: linking a node to
                    // itself would make a cycle.
                    if expansion.0 != NONE && expansion != ty {
                        self.g.link(ty, expansion);
                        self.push_lowering(expansion);
                        continue;
                    }
                    // `Cannot_expand`: a constructor below its scope is a
                    // clash (ctype.ml:596-599).
                    if escapes {
                        return Err(Clash);
                    }
                }
            }
            self.g.write(ty, Node { level, ..node });
            self.push_lowering_children(node);
        }
        Ok(())
    }

    /// O(1) amortized: push one node of a lowering walk on [`Checker::frames`].
    #[inline]
    fn push_lowering(&mut self, ty: Ty) {
        self.frames.push(Frame {
            left: ty,
            right: Ty(NONE),
            kind: FrameKind::Pair,
            extra: 0,
        });
    }

    /// O(arity): push the children of `node` last first, so that they are
    /// popped in `iter_type_expr`'s order (compiler/ml/btype.ml:250-257:
    /// an arrow's parameters, then its result). The memo of a constructor
    /// is not a child. An extended node (`TUPLE | EXTENDED`) keeps its
    /// children in its list slots, as a tuple does.
    fn push_lowering_children(&mut self, node: Node) {
        match node.tag() {
            ARROW => {
                self.push_lowering(Ty(node.a));
                for index in (0..node.arity()).rev() {
                    let ty = self.g.params[(node.b + index) as usize].ty;
                    self.push_lowering(ty);
                }
            }
            CONSTR => {
                for index in (0..node.arity()).rev() {
                    let ty = self.g.lists[(node.b + 1 + index) as usize];
                    self.push_lowering(ty);
                }
            }
            TUPLE => {
                for index in (0..node.arity()).rev() {
                    let ty = self.g.lists[(node.b + index) as usize];
                    self.push_lowering(ty);
                }
            }
            VAR => {}
            _ => panic!("expected representative descriptor"),
        }
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
        // `seen` (typecore.ml:2505) as marks of this call's generation: one
        // load and one store per arrow, no list.
        let generation = self.fresh_marks();
        let mut ty = root;
        loop {
            #[cfg(test)]
            super::steps::tick();
            let head = match self.expand_head(ty, ExpandMode::Safe) {
                Ok(head) => head,
                Err(Clash) => unreachable!("a safe expansion does not clash"),
            };
            let index = head.0 as usize;
            if index >= self.marks.len() {
                self.marks.resize(self.g.nodes.len(), 0);
            }
            if self.marks[index] == generation {
                return;
            }
            self.marks[index] = generation;
            let node = self.g.nodes[index];
            if node.tag() != ARROW {
                return;
            }
            // `unify_var env (newvar ()) typ` (typecore.ml:2511): the
            // variable is new, so what remains is the parameter lowered to
            // the current level; OCaml asserts that it cannot fail.
            let level = self.g.level;
            for index in 0..node.arity() {
                let param = self.g.params[(node.b + index) as usize].ty;
                if self.lower(param, level).is_err() {
                    unreachable!("lower_args failed to lower a parameter");
                }
            }
            ty = Ty(node.a);
        }
    }
}

/// O(1): a node that is a link to `target`, keeping `node`'s level.
/// Shared by the memo lookups of `instance` and `copy`. (R3b)
pub(crate) fn link_node(node: Node, target: Ty) -> Node {
    // The form `Graph::link` writes.
    Node {
        head: LINK,
        a: target.0,
        b: 0,
        ..node
    }
}

/// Template reference flag of a node relative to an instance's first node
/// (tc/template.rs, `Template`).
const RELATIVE: u32 = 1 << 30;

/// A row of [`Memo::simple`] that is not live in any generation.
const STALE: SimpleMemo = SimpleMemo {
    node: Ty(NONE),
    expansion: Ty(NONE),
    private_expansion: Ty(NONE),
    generation: 0,
};

#[cfg(test)]
mod tests {
    use super::super::segment::{
        IdentRow, ItemStatus, SchemeRoot, SignatureItemRow, SignaturePools, TypeDecl,
    };
    use super::super::steps;
    use super::*;

    use super::super::graph::{Graph, TUPLE};

    /// A checker at level 1 whose types `0..rows` are abstract.
    fn checker(rows: usize) -> Checker {
        let mut c = Checker::new(Graph::default(), TypeTable::default());
        c.types.rows = vec![ABSTRACT; rows];
        c
    }

    /// A constructor node at `level`.
    fn constr(c: &mut Checker, level: u32, ty: u32, args: &[Ty]) -> Ty {
        let b = c.g.lists.len() as u32;
        c.g.lists.push(Ty(NONE));
        c.g.lists.extend_from_slice(args);
        c.g.push(Node {
            head: CONSTR | (args.len() as u32) << 8,
            level,
            a: ty,
            b,
        })
    }

    /// A variable node at `level`.
    fn var(c: &mut Checker, level: u32) -> Ty {
        c.g.push(Node {
            head: VAR,
            level,
            a: NONE,
            b: 0,
        })
    }

    /// Declare `ty` an abbreviation of `body` over `params`, all generic:
    /// one template of the tuple `(params.., body)`.
    fn abbreviation(c: &mut Checker, ty: u32, params: &[Ty], body: Ty) {
        let b = c.g.lists.len() as u32;
        c.g.lists.extend_from_slice(params);
        c.g.lists.push(body);
        let root = c.g.push(Node {
            head: TUPLE | (params.len() as u32 + 1) << 8,
            level: GENERIC,
            a: 0,
            b,
        });
        let template = c.g.capture(root);
        let first = c.types.roots.len() as u32;
        for &param in params {
            let reference = Ty(c.g.forward[param.0 as usize].target);
            c.types.roots.push(reference);
        }
        c.types.manifests.push(Manifest {
            template,
            params: first,
            body: Ty(c.g.forward[body.0 as usize].target),
        });
        c.types.rows[ty as usize] = TypeInfo {
            manifest: c.types.manifests.len() as u32 - 1,
            arity: params.len() as u16,
            flags: ABBREV,
            ..ABSTRACT
        };
    }

    /// A chain of 10,000 nullary abbreviations (`type t{i} = t{i-1}`):
    /// expanding the last is one loop step and one instance of a two-node
    /// template (the declaration's tuple and the body: two nodes, two list
    /// slots) per abbreviation, and, the nullary memo being live from the
    /// first expansion on, the instance's lookup pass over its two nodes;
    /// again, one step each from the memo, making no node.
    #[test]
    fn expanding_a_chain_of_ten_thousand_abbreviations() {
        let n = 10_000u32;
        let mut c = checker(n as usize + 1);
        for ty in 1..=n {
            let body = constr(&mut c, GENERIC, ty - 1, &[]);
            abbreviation(&mut c, ty, &[], body);
        }
        let last = constr(&mut c, 1, n, &[]);
        let mut head = last;
        let count = steps::scope(|| head = c.expand_head(last, ExpandMode::Safe).unwrap());
        assert!(count <= 7 * u64::from(n) + 1, "{count}");
        assert_eq!(c.g.nodes[head.0 as usize].a, 0);
        assert_eq!(c.memo.live, n);
        let nodes = c.g.nodes.len();
        let count = steps::scope(|| assert_eq!(c.expand_head(last, ExpandMode::Safe).unwrap(), head));
        assert!(count <= u64::from(n) + 1, "{count}");
        assert_eq!(c.g.nodes.len(), nodes);
        // The nullary memo is forgotten in one store.
        assert_eq!(steps::scope(|| c.cleanup_abbrev()), 0);
        assert_eq!(c.memo.live, 0);
        assert_eq!(c.find_repr(n).0, NONE);
    }

    /// 10,000 constructors with an argument, each expanded once: a cleanup
    /// is one step per memorized slot 0, and forgets all of them.
    #[test]
    fn cleanup_of_ten_thousand_memos_is_linear() {
        let mut c = checker(2);
        let param = var(&mut c, GENERIC);
        abbreviation(&mut c, 1, &[param], param);
        let int = constr(&mut c, 1, 0, &[]);
        let nodes: Vec<Ty> = (0..10_000).map(|_| constr(&mut c, 1, 1, &[int])).collect();
        for &node in &nodes {
            assert_eq!(c.expand_head(node, ExpandMode::Safe).unwrap(), int);
            assert_ne!(c.find_expansion(node, false).0, NONE);
        }
        assert_eq!(steps::scope(|| c.cleanup_abbrev()), 10_000);
        assert!(nodes.iter().all(|&node| c.find_expansion(node, true).0 == NONE));
        assert!(c.memo.memorized.is_empty());
    }

    /// A constructor with 10,000 arguments: the instance (one step per
    /// node and per list slot) and one step per parameter link.
    #[test]
    fn expanding_ten_thousand_parameters_is_linear() {
        let n = 10_000u32;
        let mut c = checker(2);
        let params: Vec<Ty> = (0..n).map(|_| var(&mut c, GENERIC)).collect();
        let body = constr(&mut c, GENERIC, 0, &[]);
        abbreviation(&mut c, 1, &params, body);
        let args: Vec<Ty> = (0..n).map(|_| var(&mut c, 1)).collect();
        let node = constr(&mut c, 1, 1, &args);
        let mut expansion = node;
        let count = steps::scope(|| expansion = c.expand_once(node, ExpandMode::Unif).unwrap());
        // Nodes: the tuple, n parameters, the body; slots: the tuple's n + 1
        // and the body's slot 0; then n links.
        assert!(count <= 3 * u64::from(n) + 4, "{count}");
        assert_eq!(c.g.nodes[expansion.0 as usize].a, 0);
        let first = c.g.nodes.len() as u32 - n - 2 + 1;
        for (index, &arg) in args.iter().enumerate() {
            assert_eq!(c.g.repr(Ty(first + index as u32)), arg);
        }
    }

    /// A chain of `n` one-element tuples around a constructor of type `ty`,
    /// every node at `level`.
    fn tuple_chain(c: &mut Checker, n: u32, level: u32, ty: u32) -> Ty {
        let mut node = constr(c, level, ty, &[]);
        for _ in 1..n {
            let b = c.g.lists.len() as u32;
            c.g.lists.push(node);
            node = c.g.push(Node {
                head: TUPLE | 1 << 8,
                level,
                a: 0,
                b,
            });
        }
        node
    }

    /// The scoped walk over a 10,000-deep type on a 2 MB stack: one step a
    /// node when nothing escapes, one speculation, closed. When the bottom
    /// node escapes, two passes and two restores, at most 4 steps a node,
    /// and the graph is as it was before the call.
    #[test]
    fn scoped_lowering_of_ten_thousand_nodes() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let n = 10_000u32;
                let mut c = checker(2);
                c.types.rows[1].scope = 2;
                c.types.scoped = 1;
                let root = tuple_chain(&mut c, n, 3, 0);
                assert_eq!(steps::scope(|| c.lower(root, 1).unwrap()), u64::from(n));
                assert!(c.g.nodes.iter().all(|node| node.level == 1));
                assert!(c.g.trail.is_empty());
                assert_eq!(c.g.speculation_depth, 0);

                let first = c.g.nodes.len();
                let root = tuple_chain(&mut c, n, 3, 1);
                let before = c.g.nodes.clone();
                let count = steps::scope(|| assert!(c.lower(root, 1).is_err()));
                assert!(count <= 4 * u64::from(n), "{count}");
                assert_eq!(c.g.nodes, before);
                assert!(c.g.nodes[first..].iter().all(|node| node.level == 3));
                assert!(c.g.trail.is_empty());
                assert_eq!(c.g.speculation_depth, 0);
                assert!(c.frames.is_empty());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// 10,000 nodes below their scope, each an abbreviation of the next
    /// (`type t{i} = t{i-1}`, all scoped): the walk expands each once, one
    /// loop step and one instance per abbreviation, and ends on type 0.
    #[test]
    fn scoped_lowering_expands_ten_thousand_abbreviations() {
        let n = 10_000u32;
        let mut c = checker(n as usize + 1);
        for ty in 1..=n {
            let body = constr(&mut c, GENERIC, ty - 1, &[]);
            abbreviation(&mut c, ty, &[], body);
            c.types.rows[ty as usize].scope = 2;
        }
        c.types.scoped = n;
        let last = constr(&mut c, 3, n, &[]);
        let count = steps::scope(|| c.lower(last, 1).unwrap());
        assert!(count <= 8 * u64::from(n) + 1, "{count}");
        let head = c.g.repr(last);
        assert_eq!(c.g.nodes[head.0 as usize].a, 0);
        assert_eq!(c.g.nodes[head.0 as usize].level, 1);
        assert!(c.g.trail.is_empty());
    }

    /// The expanding retry: a constructor with an argument whose argument
    /// escapes is a clash without expanding, and is replaced by its
    /// expansion on the second pass (`type phantom<'a> = int`).
    #[test]
    fn the_retry_expands_a_constructor_with_arguments() {
        let mut c = checker(3);
        let param = var(&mut c, GENERIC);
        let body = constr(&mut c, GENERIC, 0, &[]);
        abbreviation(&mut c, 1, &[param], body);
        c.types.rows[2].scope = 2;
        c.types.scoped = 1;
        let escaping = constr(&mut c, 3, 2, &[]);
        let phantom = constr(&mut c, 3, 1, &[escaping]);
        c.lower(phantom, 1).unwrap();
        let head = c.g.repr(phantom);
        assert_eq!(c.g.nodes[head.0 as usize].a, 0);
        assert_eq!(c.g.nodes[head.0 as usize].level, 1);
        // The escaping argument is not reached through the expansion.
        assert_eq!(c.g.nodes[escaping.0 as usize].level, 3);
        assert!(c.g.trail.is_empty());
    }

    /// `lower_args` over a chain of 10,000 arrows: one loop step, one
    /// expansion step and one lowering of the parameter (one step: a
    /// variable one level up) per arrow, at most 4 steps an arrow; a chain
    /// whose result is the arrow itself stops at the second visit.
    #[test]
    fn lower_args_over_ten_thousand_arrows() {
        let n = 10_000u32;
        let mut c = checker(1);
        c.g.begin_def();
        let mut ty = var(&mut c, 2);
        for _ in 0..n {
            let param = var(&mut c, 3);
            let b = c.g.params.len() as u32;
            c.g.params.push(super::super::graph::Param {
                ty: param,
                label: NONE,
                loc: NONE,
            });
            ty = c.g.push(Node {
                head: super::super::graph::ARROW | 1 << 8,
                level: 2,
                a: ty.0,
                b,
            });
        }
        let count = steps::scope(|| c.lower_args(ty));
        assert!(count <= 4 * u64::from(n) + 2, "{count}");
        assert!(
            c.g.nodes
                .iter()
                .filter(|node| node.tag() == VAR)
                .all(|node| node.level == 2)
        );
        // `f: 'a => f`: the result is the arrow itself.
        let param = var(&mut c, 2);
        let b = c.g.params.len() as u32;
        c.g.params.push(super::super::graph::Param {
            ty: param,
            label: NONE,
            loc: NONE,
        });
        let cyclic = Ty(c.g.nodes.len() as u32);
        c.g.push(Node {
            head: super::super::graph::ARROW | 1 << 8,
            level: 2,
            a: cyclic.0,
            b,
        });
        assert!(steps::scope(|| c.lower_args(cyclic)) <= 8);
    }

    /// A restore of 10,000 writes is one step a write plus the cleanup, which
    /// forgets both memos; a restore with nothing written keeps them
    /// (compiler/ml/btype.ml:773-781).
    #[test]
    fn restore_cleans_the_memos_after_a_write() {
        let mut c = checker(3);
        let body = constr(&mut c, GENERIC, 0, &[]);
        abbreviation(&mut c, 1, &[], body);
        let param = var(&mut c, GENERIC);
        abbreviation(&mut c, 2, &[param], param);
        let nullary = constr(&mut c, 1, 1, &[]);
        let int = constr(&mut c, 1, 0, &[]);
        let unary = constr(&mut c, 1, 2, &[int]);
        c.expand_head(nullary, ExpandMode::Safe).unwrap();
        c.expand_head(unary, ExpandMode::Safe).unwrap();
        let token = c.g.speculate();
        assert_eq!(steps::scope(|| c.restore(token)), 0);
        assert_eq!(c.find_repr(1), nullary);
        assert_ne!(c.find_expansion(unary, false).0, NONE);
        let token = c.g.speculate();
        let v = var(&mut c, 1);
        for level in 0..10_000 {
            c.g.write(v, Node { level, ..c.g.nodes[v.0 as usize] });
        }
        // 10,000 restored writes and one memorized slot 0.
        assert_eq!(steps::scope(|| c.restore(token)), 10_001);
        assert_eq!(c.g.nodes[v.0 as usize].level, 1);
        assert_eq!(c.find_repr(1).0, NONE);
        assert_eq!(c.find_expansion(unary, false).0, NONE);
        assert_eq!(c.memo.live, 0);
    }

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

    /// A phantom unary abbreviation over an abstract type of the unit
    /// expands to that type (differential seed 2000018).
    #[test]
    fn a_phantom_abbreviation_of_a_compiled_unit_expands() {
        use super::super::differential::{New, Tier, compile};
        let program = compile(
            "type t0\ntype a2<'a> = t0\nexternal v2: a2<'b> = \"v2\"\n".to_string(),
        );
        let mut new = New::convert(&program, Tier::Expand);
        let ty = new.instance(0);
        let node = new.checker.g.nodes[ty.0 as usize];
        let pools = &new.segment.signature;
        let path = pools.paths[node.a as usize];
        let ident = match path {
            PathRow::Ident(ident) => Some(pools.identifiers[ident as usize]),
            _ => None,
        };
        let item = ident.and_then(|ident| pools.ordered_items.get(ident.scope as usize).copied());
        let info = new.checker.types.info(node.a);
        let manifest = (info.manifest != NONE)
            .then(|| new.checker.types.manifests[info.manifest as usize]);
        let slot = new.checker.g.lists[node.b as usize];
        let report = format!(
            "node {node:?} slot0 {slot:?}\npath {path:?}\nident {ident:?}\nitem {item:?}\ninfo {info:?}\n\
             manifest {manifest:?}\nitems {:?}\ndeclarations {:?}",
            pools.ordered_items, new.segment.type_declarations
        );
        let once = new.checker.expand_once(ty, ExpandMode::Safe);
        let head = new.checker.expand_head(ty, ExpandMode::Safe).unwrap();
        assert_ne!(head, ty, "{report}\nexpand_once {once:?}");
        let head = new.checker.g.nodes[head.0 as usize];
        assert_eq!(head.tag(), CONSTR, "{report}");
        assert_eq!(head.arity(), 0, "{report}");
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
        // The value's type names the unit's own types through the unit
        // (`Case.a0`): those rows carry the declaration too.
        let mut through_unit = 0;
        for (index, path) in pools.paths.iter().enumerate() {
            let PathRow::Dot { name, .. } = *path else { continue };
            let range = pools.strings[name as usize];
            let name = &pools.bytes[range.start as usize..(range.start + range.len) as usize];
            let info = table.info(index as u32);
            match name {
                b"a0" | b"a1" => assert_eq!(info.flags, ABBREV),
                b"r" => assert_eq!(info.flags, DATATYPE),
                b"t0" | b"t1" => assert_eq!(info.flags, 0),
                _ => continue,
            }
            through_unit += 1;
        }
        assert!(through_unit >= 4, "{:?}", pools.paths);
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
