//! Lookups by path, the usage and warnings of a lookup, and the reads of
//! other units (R4e, R4f, R4g). The data is `tc::scope::Scopes`; this file
//! adds the operations that the walk calls when it reaches a use.
//!
//! A use is resolved once, when the walk reaches it (CHECKER_REWRITE 2.4,
//! idea 5), in three calls the walk makes in this order:
//!
//! 1. find: [`Scopes::find`], [`Scopes::candidates`], [`Scopes::lookup_path`]
//!    or [`Scopes::candidates_in`]. Nothing is written: a lookup that is
//!    tried and abandoned (disambiguation, a speculative typing) leaves no
//!    mark and no warning.
//! 2. use: [`Scopes::use_found`] for the item that was chosen, and
//!    [`Scopes::use_modules`] for the modules a path went through. This is
//!    where an open becomes used, a shadowing is reported, a deprecation is
//!    reported and a read of another unit is logged.
//! 3. mark: [`Scopes::mark`] for the binder's used bits, by the rules of the
//!    construct (the walk knows whether a use inside a `let rec` counts).
//!
//! The unused warnings are raised by [`Scopes::finish`] at the end of the
//! unit, in the order the declarations were armed.

use super::name_table::Name;
use super::scope::{
    ARMED_OPEN, Binder, BinderKind, Found, IMPORTED, Key, NONE, Namespace, OPEN_OVERRIDE,
    OPEN_USED, PATTERN, POSITIVE, PRIVATIZE, Resolved, ResolvedKind, Scopes, ShadowNote, TableId,
    UNIT_MASK, USED, UnitSource, Warning, WarningKind,
};
use super::segment::{FUNCTOR_SCOPE, ModuleTypeRow, PathRow, Segment, SignatureKind};

/// What a module is, for a path that goes through it: 8 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleShape {
    /// A structure: its member table.
    Structure(TableId),
    /// A module whose type is a named module type (`module M: S`): the
    /// member table of the module type's signature. The members are the
    /// module type's items; giving their types the module's path
    /// (`Mtype.strengthen`) is R6d's.
    Abstract(TableId),
    /// A functor: it has no members (`Functor_comps`,
    /// compiler/ml/env.ml:966).
    Functor,
}

/// Why a path did not resolve: 4 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PathError {
    pub kind: PathErrorKind,
    /// The index of the component of the path the error is about.
    pub component: u16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PathErrorKind {
    /// The last component is not a member of the module before it, or a
    /// one-component path is not bound.
    Unbound,
    /// A module component is not bound: neither in scope nor a unit
    /// (`Unbound_module`, compiler/ml/typetexp.ml:65-85).
    UnboundModule,
    /// A component before the last is a functor.
    Functor,
    /// A component is a module whose members R4 cannot list: a functor
    /// application in a published path, a module type that is not a
    /// signature or a name of one. The unit is declined by the slice that
    /// owns module types (R6d).
    Unsupported,
}

/// The answer for a module R4 cannot list, about component 0: the caller
/// that knows the component rewrites it.
const UNSUPPORTED: PathError = PathError {
    kind: PathErrorKind::Unsupported,
    component: 0,
};

/// How many components of dependencies' paths [`Scopes::module_shape`]
/// keeps waiting at once: one a `Dot` of an alias or module type name it
/// is inside. A published alias is written as in the source (`module Q =
/// P.A`, one waiting); a module with more is `Unsupported` and the unit is
/// declined.
const PENDING: usize = 16;

/// [`Pending::unit`] bit: the component names a module type.
const PENDING_MODULE_TYPE: u32 = 1 << 31;

/// A component of a dependency's path still to be read: 8 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Pending {
    /// The unit whose string pool holds `name`, with
    /// [`PENDING_MODULE_TYPE`].
    unit: u32,
    /// A string of that unit's segment.
    name: u32,
}

/// Where [`Scopes::module_shape`] is: 12 bytes, its loop variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum At {
    /// A module of this unit, a unit, or an imported member.
    Resolved(Resolved),
    /// A `signature.modules` row of `unit`: a module, or with
    /// `module_type` a module type, declared in the unit's signature.
    Declaration {
        unit: u32,
        row: u32,
        module_type: bool,
    },
    /// A `signature.paths` row of `unit` naming a module, or with
    /// `module_type` a module type.
    Path {
        unit: u32,
        path: u32,
        module_type: bool,
    },
}

/// O(1), no allocation: the text of string `index` of a segment's string
/// pool. Names are written from Rust strings, so the bytes are UTF-8.
fn segment_text(segment: &Segment, index: u32) -> &str {
    let range = segment.signature.strings[index as usize];
    std::str::from_utf8(
        &segment.signature.bytes[range.start as usize..(range.start + range.len) as usize],
    )
    .expect("a segment string is UTF-8")
}

/// O(1): the error `kind` about component `component` (a path longer
/// than `u16::MAX` reports its last representable component).
fn path_error(kind: PathErrorKind, component: usize) -> PathError {
    PathError {
        kind,
        component: component.min(u16::MAX as usize) as u16,
    }
}

/// `Scopes::unit_read` bit: the unit's interface was loaded for this unit
/// (`find_pers_struct`, compiler/ml/env.ml:646).
pub const READ: u8 = 1;
/// `Scopes::unit_read` bit: the unit was named by an alias and not loaded
/// (`check_pers_struct`, compiler/ml/env.ml:666).
pub const READ_WEAK: u8 = 2;

impl Scopes {
    // ----- R4e: paths -----

    /// What `module` is, following aliases: 1 step per alias, one
    /// [`Scopes::import_table`] when it ends at a dependency's module.
    ///
    /// - A [`Binder`]: `Module` gives `Structure(payload)` or `Functor`
    ///   (payload `NONE`); `FunctorParameter` gives `Abstract(payload)`;
    ///   `ModuleAlias` continues with its payload.
    /// - A unit: `Structure` of its export table 0.
    /// - An imported module item: its `modules` row's module type.
    ///   `Signature(s)` gives `Structure` of table `s`; `Alias` continues
    ///   with the path's module (a `PathRow::Ident` whose `IdentRow::scope`
    ///   is an item index names that item of the same unit directly; a
    ///   persistent identifier names a unit, read with `source`; `Dot`
    ///   searches the parent's table); `Ident` (a named module type)
    ///   resolves the module type the same way and gives `Abstract` of its
    ///   signature; `Functor` gives `Functor`.
    ///
    /// Anything else is `PathErrorKind::Unsupported` with component 0.
    /// `Env.find_module_descr` and `normalize_path`,
    /// compiler/ml/env.ml:732-760, 854-880.
    pub fn module_shape(
        &mut self,
        module: Resolved,
        source: &mut dyn UnitSource,
    ) -> Result<ModuleShape, PathError> {
        // The components of the dependencies' paths still to be read, the
        // innermost path's root-most component on top: an alias `A.B.C`
        // pushes `C` then `B` and continues with `A`.
        let mut pending = [Pending { unit: 0, name: 0 }; PENDING];
        let mut depth = 0;
        let mut at = At::Resolved(module);
        loop {
            let shape = match at {
                At::Resolved(resolved) => match resolved.kind() {
                    ResolvedKind::Binder(binder) => {
                        let payload = self.binders.payload[binder.0 as usize];
                        match self.binders.kind[binder.0 as usize] {
                            // A functor's binder has no table (`Functor_comps`,
                            // compiler/ml/env.ml:966).
                            BinderKind::Module if payload == NONE => ModuleShape::Functor,
                            BinderKind::Module => ModuleShape::Structure(TableId(payload)),
                            BinderKind::FunctorParameter => ModuleShape::Abstract(TableId(payload)),
                            // `module N = M`: the alias is followed when its
                            // members are needed (`normalize_path`,
                            // compiler/ml/env.ml:854-880), one step each.
                            BinderKind::ModuleAlias => {
                                #[cfg(test)]
                                super::steps::tick();
                                at = At::Resolved(Resolved(payload));
                                continue;
                            }
                            _ => return Err(UNSUPPORTED),
                        }
                    }
                    ResolvedKind::Unit(unit) => ModuleShape::Structure(self.import_table(unit, 0)),
                    ResolvedKind::Import(row) => {
                        let member = self.imported_members[row as usize];
                        if Key(member.key).namespace() != Namespace::Module as u32 {
                            return Err(UNSUPPORTED);
                        }
                        let unit = member.origin & UNIT_MASK;
                        let item = self.units[unit as usize].segment.items[member.target as usize];
                        at = At::Declaration {
                            unit,
                            row: item.payload,
                            module_type: false,
                        };
                        continue;
                    }
                },
                At::Declaration {
                    unit,
                    row,
                    module_type,
                } => {
                    let pools = &self.units[unit as usize].segment.signature;
                    let declared = pools.modules[row as usize].module_type;
                    if declared == NONE {
                        // An abstract module type has no members.
                        return Err(UNSUPPORTED);
                    }
                    match pools.module_types[declared as usize] {
                        ModuleTypeRow::Signature(signature) => {
                            let table = self.import_table(unit, signature);
                            if module_type {
                                ModuleShape::Abstract(table)
                            } else {
                                ModuleShape::Structure(table)
                            }
                        }
                        ModuleTypeRow::Functor { .. } => ModuleShape::Functor,
                        // `module N = P`, or a module (type) whose type is
                        // the named module type `P`: one step, then `P`.
                        ModuleTypeRow::Alias { path, .. } if !module_type => {
                            #[cfg(test)]
                            super::steps::tick();
                            at = At::Path {
                                unit,
                                path,
                                module_type: false,
                            };
                            continue;
                        }
                        ModuleTypeRow::Ident(path) => {
                            #[cfg(test)]
                            super::steps::tick();
                            at = At::Path {
                                unit,
                                path,
                                module_type: true,
                            };
                            continue;
                        }
                        ModuleTypeRow::Alias { .. } => return Err(UNSUPPORTED),
                    }
                }
                At::Path {
                    unit,
                    path,
                    module_type,
                } => {
                    at =
                        self.path_root(unit, path, module_type, &mut pending, &mut depth, source)?;
                    continue;
                }
            };
            if depth == 0 {
                return Ok(shape);
            }
            // The next component of a dependency's path, read from the
            // module just found: one search.
            depth -= 1;
            at = self.read_component(shape, pending[depth])?;
        }
    }

    /// The start of path `path` of `unit`'s signature: every `Dot` from
    /// the last component up is pushed on `pending` (1 load each, no
    /// step), then the root identifier is read. An identifier whose
    /// `IdentRow::scope` is an item index names that item of the same
    /// unit: its declaration, no name lookup. A persistent identifier
    /// (scope `NONE`, stamp 0) names a unit: one intern of its name and one
    /// [`Scopes::unit_by_name`]. `module_type` says that the path's last
    /// component names a module type. A functor application, a functor's
    /// parameter, the unit itself, an unknown unit, a kind that does not
    /// match and more than [`PENDING`] components waiting are
    /// [`PathErrorKind::Unsupported`].
    fn path_root(
        &mut self,
        unit: u32,
        path: u32,
        mut module_type: bool,
        pending: &mut [Pending; PENDING],
        depth: &mut usize,
        source: &mut dyn UnitSource,
    ) -> Result<At, PathError> {
        let pools = &self.units[unit as usize].segment.signature;
        let mut row = path;
        let ident = loop {
            match pools.paths[row as usize] {
                PathRow::Ident(ident) => break pools.identifiers[ident as usize],
                PathRow::Dot { parent, name, .. } => {
                    if *depth == PENDING {
                        return Err(UNSUPPORTED);
                    }
                    pending[*depth] = Pending {
                        unit: unit | if module_type { PENDING_MODULE_TYPE } else { 0 },
                        name,
                    };
                    *depth += 1;
                    row = parent;
                    module_type = false;
                }
                PathRow::Apply { .. } => return Err(UNSUPPORTED),
            }
        };
        if ident.scope < FUNCTOR_SCOPE {
            let item = pools.ordered_items[ident.scope as usize];
            let kind = if module_type {
                SignatureKind::ModuleType
            } else {
                SignatureKind::Module
            };
            if item.kind != kind {
                return Err(UNSUPPORTED);
            }
            return Ok(At::Declaration {
                unit,
                row: item.declaration,
                module_type,
            });
        }
        if ident.scope != NONE || ident.stamp != 0 || module_type {
            return Err(UNSUPPORTED);
        }
        let Scopes { names, units, .. } = self;
        let name = names.intern(segment_text(&units[unit as usize].segment, ident.name));
        match self.unit_by_name(name, source) {
            Some(unit) => Ok(At::Resolved(Resolved::unit(unit))),
            None => Err(UNSUPPORTED),
        }
    }

    /// One [`Scopes::search`] and one probe of the name table, no
    /// allocation: the member `component` names in the module whose shape
    /// is `shape`. A name the worker never interned is in no table it
    /// imported. A functor, or a name the table does not have, is
    /// [`PathErrorKind::Unsupported`]: a published path names a member.
    fn read_component(&self, shape: ModuleShape, component: Pending) -> Result<At, PathError> {
        let table = match shape {
            ModuleShape::Structure(table) | ModuleShape::Abstract(table) => table,
            ModuleShape::Functor => return Err(UNSUPPORTED),
        };
        let module_type = component.unit & PENDING_MODULE_TYPE != 0;
        let unit = component.unit & !PENDING_MODULE_TYPE;
        let text = segment_text(&self.units[unit as usize].segment, component.name);
        let name = self.names.find(text).ok_or(UNSUPPORTED)?;
        let ns = if module_type {
            Namespace::ModuleType
        } else {
            Namespace::Module
        };
        let row = self.search(table, Key::new(name, ns)).ok_or(UNSUPPORTED)?;
        let item = self.row_item(table, row);
        if !module_type {
            return Ok(At::Resolved(item));
        }
        // A module type is read in its own unit's segment.
        let ResolvedKind::Import(row) = item.kind() else {
            return Err(UNSUPPORTED);
        };
        let member = self.imported_members[row as usize];
        let unit = member.origin & UNIT_MASK;
        Ok(At::Declaration {
            unit,
            row: self.units[unit as usize].segment.items[member.target as usize].payload,
            module_type: true,
        })
    }

    /// Resolve a path of one or more names whose last component is in
    /// namespace `ns` (`Env.lookup` and `lookup_module`,
    /// compiler/ml/env.ml:952-1026). No usage is marked and no warning is
    /// raised; the one log written is the unit read of
    /// [`Scopes::unit_by_name`] (from R4g on), because loading an interface
    /// is a read whether or not the lookup is used.
    ///
    /// One component: [`Scopes::find`]; for `Namespace::Module`, a name with
    /// no binding is a unit ([`Scopes::unit_by_name`]). More: the first
    /// component is a module found the same way; each further component is
    /// one [`Scopes::module_shape`] of the module so far and one
    /// [`Scopes::search`] in its table. `modules` receives the module of
    /// every component before the last, in order (cleared first; no
    /// allocation when it has capacity), for [`Scopes::use_modules`]. The
    /// answer's `layer` is the layer the first component was found through.
    ///
    /// Cost: 1 step a component, plus the searches and the alias steps.
    pub fn lookup_path(
        &mut self,
        ns: Namespace,
        path: &[Name],
        modules: &mut Vec<Found>,
        source: &mut dyn UnitSource,
    ) -> Result<Found, PathError> {
        modules.clear();
        let (&first, rest) = path.split_first().expect("a path has a component");
        #[cfg(test)]
        super::steps::tick();
        // The first component is a name in scope; a module name with no
        // binding is a unit (`lookup_module`, compiler/ml/env.ml:985-1000).
        let first_ns = if rest.is_empty() {
            ns
        } else {
            Namespace::Module
        };
        let mut current = match self.find(Key::new(first, first_ns)) {
            Some(found) => found,
            None if first_ns == Namespace::Module => match self.unit_by_name(first, source) {
                Some(unit) => Found {
                    item: Resolved::unit(unit),
                    layer: NONE,
                },
                None => return Err(path_error(PathErrorKind::UnboundModule, 0)),
            },
            None => return Err(path_error(PathErrorKind::Unbound, 0)),
        };
        let layer = current.layer;
        for (index, &name) in rest.iter().enumerate() {
            #[cfg(test)]
            super::steps::tick();
            modules.push(current);
            // `index` is the component of the module the name is read from.
            let table = match self.module_shape(current.item, source) {
                Ok(ModuleShape::Structure(table) | ModuleShape::Abstract(table)) => table,
                Ok(ModuleShape::Functor) => {
                    return Err(path_error(PathErrorKind::Functor, index));
                }
                Err(error) => return Err(path_error(error.kind, index)),
            };
            let key_ns = if index + 1 == rest.len() {
                ns
            } else {
                Namespace::Module
            };
            current = match self.search(table, Key::new(name, key_ns)) {
                Some(row) => Found {
                    item: self.row_item(table, row),
                    layer: NONE,
                },
                None if key_ns == Namespace::Module => {
                    return Err(path_error(PathErrorKind::UnboundModule, index + 1));
                }
                None => return Err(path_error(PathErrorKind::Unbound, index + 1)),
            };
        }
        Ok(Found {
            item: current.item,
            layer,
        })
    }

    /// Every member of `key` in a module's table, in candidate order,
    /// appended to `out` with `layer` `NONE` (the qualified case of
    /// `lookup_all_simple`, compiler/ml/env.ml:1039-1045): one
    /// [`Scopes::search`] and 1 step a candidate.
    pub fn candidates_in(&self, table: TableId, key: Key, out: &mut Vec<Found>) {
        let Some(first) = self.search(table, key) else {
            return;
        };
        let end = self.table_end(table);
        for row in first..end {
            if self.member(table, row).key != key.0 {
                break;
            }
            #[cfg(test)]
            super::steps::tick();
            out.push(Found {
                item: self.row_item(table, row),
                layer: NONE,
            });
        }
    }

    /// O(1), no step: what row `row` of `table` names, the binder of a
    /// local member or the imported row itself.
    fn row_item(&self, table: TableId, row: u32) -> Resolved {
        if table.0 & IMPORTED != 0 {
            Resolved::import(row)
        } else {
            Resolved::binder(Binder(self.member(table, row).target))
        }
    }

    /// O(1), no step: the row after the last of `table`, in the pool its
    /// rows live in.
    fn table_end(&self, table: TableId) -> u32 {
        let row = if table.0 & IMPORTED != 0 {
            self.imported_tables[(table.0 & !IMPORTED) as usize]
        } else {
            self.tables[table.0 as usize]
        };
        row.first + row.len
    }

    // ----- R4f: usage and the warnings of a lookup -----

    /// O(1): ask for the unused warning of a binder at the end of the unit
    /// (`Env.check_usage`, compiler/ml/env.ml:1562-1576, registers its
    /// delayed check when the declaration enters the environment). The
    /// order of the calls is the order of the warnings.
    pub fn arm(&mut self, binder: Binder) {
        self.armed.push(binder.0);
    }

    /// O(1): the same for an open (`Unused_open`,
    /// compiler/ml/env.ml:1890-1894).
    pub fn arm_open(&mut self, open: u32) {
        // `open!` has no slot (compiler/ml/env.ml:1884, CHECKER_REWRITE 9.7
        // decision 7).
        debug_assert_eq!(self.opens[open as usize].flags & OPEN_OVERRIDE, 0);
        self.armed.push(open | ARMED_OPEN);
    }

    /// O(1): the length of `armed`, for [`Scopes::disarm`].
    pub fn armed_mark(&self) -> u32 {
        self.armed.len() as u32
    }

    /// O(1): forget what was armed since `mark` (a speculative typing that
    /// was undone drops its delayed checks).
    pub fn disarm(&mut self, mark: u32) {
        self.armed.truncate(mark as usize);
    }

    /// 1 step, one load and one store: set used bits of a binder
    /// (`mark_value_used`, `mark_type_used`, `mark_constructor_used`,
    /// compiler/ml/env.ml:1080-1093). `bits` is `USED` or a constructor's
    /// usage.
    pub fn mark(&mut self, binder: Binder, bits: u8) {
        #[cfg(test)]
        super::steps::tick();
        self.binders.used[binder.0 as usize] |= bits;
    }

    /// The walk chose `found` for a use of `key` at `loc`
    /// (`IdTbl.find_name ~mark:true`, compiler/ml/env.ml:279-288, and the
    /// `using` callback of `open_signature`, env.ml:1895-1908).
    ///
    /// - Found through a layer: set `OPEN_USED` on its open. Unless the
    ///   open is `OPEN_OVERRIDE`, and when [`Scopes::find_below`] finds
    ///   something the layer hides, and the open has no [`ShadowNote`] for
    ///   `key` yet: for a value, type, module or module type, add the note
    ///   and push `OpenShadows` at the open's location. For a constructor
    ///   or a label nothing is reported here: the open shadows only when
    ///   the two result types are different type constructors after head
    ///   expansion (`check_shadowing` and `same_constr`,
    ///   compiler/ml/env.ml:415-420), which names cannot see. The hidden
    ///   item is returned; the walk compares the two result types and calls
    ///   [`Scopes::shadows`] when they differ. No note is written until
    ///   then, so a later use asks again, as OCaml does. The note list of
    ///   the open is scanned: O(names this open was reported to shadow), as
    ///   OCaml's `List.mem`.
    /// - A deprecated item (`DEPRECATED` of a binder, `MEMBER_DEPRECATED`
    ///   of an imported member): push `Deprecated` at `loc`
    ///   (compiler/ml/typetexp.ml:98-123).
    /// - From R4g on: an imported member is logged in `read_items`.
    ///
    /// It does not set a binder's used bits: that is [`Scopes::mark`], by
    /// the walk's rules. 1 step, plus `find_below` when the item came
    /// through a layer that can report shadowing.
    ///
    /// Returns `Some(hidden)` only for a constructor or label found through
    /// an open that can still report shadowing of `key` and hides `hidden`;
    /// `None` in every other case.
    pub fn use_found(&mut self, found: Found, key: Key, loc: u32) -> Option<Found> {
        #[cfg(test)]
        super::steps::tick();
        match found.layer {
            NONE => None,
            layer => self.use_open(layer, key),
        }
    }

    /// A use of `key` went through open `layer`: set `OPEN_USED`, and
    /// unless the open is `OPEN_OVERRIDE` or already has a note for `key`,
    /// one [`Scopes::find_below`]. O(names this open was reported to
    /// shadow) for the scan of its notes, plus that `find_below`; no step
    /// of its own, no allocation. The `slot` of `open_signature`
    /// (compiler/ml/env.ml:1895-1908) with `check_shadowing`
    /// (env.ml:415-427): a value, type, module or module type that hides
    /// something is noted and reported here; a constructor or label returns
    /// what it hides and is reported by [`Scopes::shadows`] on the walk's
    /// verdict.
    fn use_open(&mut self, layer: u32, key: Key) -> Option<Found> {
        let open = &mut self.opens[layer as usize];
        open.flags |= OPEN_USED;
        if open.flags & OPEN_OVERRIDE != 0 || self.noted(layer, key) {
            return None;
        }
        let hidden = self.find_below(key, layer)?;
        let ns = key.namespace();
        if ns == Namespace::Constructor as u32 || ns == Namespace::Label as u32 {
            return Some(hidden);
        }
        self.shadows(layer, key);
        None
    }

    /// O(names open `layer` was reported to shadow), no step, no
    /// allocation: whether the open has a [`ShadowNote`] for `key`
    /// (`List.mem (kind, s) !shadowed`, compiler/ml/env.ml:1897). The kind
    /// of OCaml's pair is the key's namespace.
    fn noted(&self, layer: u32, key: Key) -> bool {
        let mut note = self.opens[layer as usize].shadowed;
        while note != NONE {
            let row = self.notes[note as usize];
            if row.key == key.0 {
                return true;
            }
            note = row.next;
        }
        false
    }

    /// O(1), no step: the walk found that the constructor or label `key`
    /// used through open `layer` has another result type than the one it
    /// hides. Adds the open's [`ShadowNote`] for `key` and pushes
    /// `OpenShadows` at the open's location (`Open_shadow_label_constructor`,
    /// compiler/ml/env.ml:1897-1906). Called only with a `layer` and `key`
    /// for which [`Scopes::use_found`] just returned `Some`: the note list
    /// is not scanned again.
    pub fn shadows(&mut self, layer: u32, key: Key) {
        let open = &mut self.opens[layer as usize];
        let note = self.notes.len() as u32;
        self.notes.push(ShadowNote {
            key: key.0,
            next: open.shadowed,
        });
        open.shadowed = note;
        self.warnings.push(Warning {
            kind: WarningKind::OpenShadows,
            loc: open.loc,
            a: key.0,
            b: layer,
        });
    }

    /// The modules a path went through are used at `loc`
    /// (`lookup_module_descr`: `mark_module_used` and `report_deprecated`
    /// for every prefix, compiler/ml/env.ml:968-972): for each, in order,
    /// `USED` on a binder, `OPEN_USED` and the shadowing check for the
    /// first one's layer, `Deprecated` for a deprecated module. 1 step a
    /// module. `names` are the path's components, parallel to `modules`.
    pub fn use_modules(&mut self, modules: &[Found], names: &[Name], loc: u32) {
        todo!("R4f")
    }

    /// End of the unit: 1 step per armed entry, in the order armed. A
    /// binder without `USED` (a constructor: without `POSITIVE`, `PATTERN`
    /// and `PRIVATIZE`) pushes `Unused` at its location; an open without
    /// `OPEN_USED` pushes `UnusedOpen` at its location. Not called when the
    /// unit has an error: the warnings of a failing unit are those raised
    /// before the error (CHECKER_REWRITE 2.1, O15).
    pub fn finish(&mut self) {
        let Scopes {
            binders,
            opens,
            armed,
            warnings,
            ..
        } = self;
        for &entry in armed.iter() {
            #[cfg(test)]
            super::steps::tick();
            let warning = if entry & ARMED_OPEN != 0 {
                let index = entry & !ARMED_OPEN;
                let open = opens[index as usize];
                (open.flags & OPEN_USED == 0).then_some(Warning {
                    kind: WarningKind::UnusedOpen,
                    loc: open.loc,
                    a: index,
                    b: 0,
                })
            } else {
                // A constructor is used by any of its three usages
                // (`constructor_usages`, compiler/ml/env.ml:38-47); every
                // other binder has only `USED`.
                (binders.used[entry as usize] & (USED | POSITIVE | PATTERN | PRIVATIZE) == 0)
                    .then_some(Warning {
                        kind: WarningKind::Unused,
                        loc: binders.loc[entry as usize],
                        a: entry,
                        b: 0,
                    })
            };
            warnings.extend(warning);
        }
    }

    // ----- R4g: reads of other units -----

    /// 1 step: this unit read `unit`'s interface (`READ`) or named it
    /// without loading (`READ_WEAK`). The first read of a unit appends it
    /// to `read_units`; later ones are one load and one compare. R4g calls
    /// it from [`Scopes::unit_by_name`] on every answer that is a unit,
    /// also when the worker knew the unit from an earlier compilation.
    pub fn read_unit(&mut self, unit: u32, bits: u8) {
        todo!("R4g")
    }

    /// 1 step: this unit used the imported member `row`. The first use
    /// appends it to `read_items` and reads its unit; later ones are one
    /// load and one bit test.
    pub fn read_item(&mut self, row: u32) {
        todo!("R4g")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<ModuleShape>(), 8);
        assert_eq!(std::mem::size_of::<PathError>(), 4);
        assert!(std::mem::size_of::<Result<Found, PathError>>() <= 16);
        assert!(std::mem::size_of::<Result<ModuleShape, PathError>>() <= 16);
        assert_eq!(std::mem::size_of::<At>(), 12);
        assert_eq!(std::mem::size_of::<Pending>(), 8);
    }

    use crate::tc::scope::UnitSource;
    use crate::tc::segment::{
        ChildTable, ExportItem, ExportKind, IdentRow, ItemStatus, ModuleRow, Range,
        SignatureItemRow, SignaturePools,
    };
    use std::sync::Arc;

    /// No unit but the one a test adds.
    struct NoUnits;

    impl UnitSource for NoUnits {
        fn segment(&mut self, _: &str) -> Option<Arc<Segment>> {
            None
        }
    }

    /// A segment's string pool of `texts`.
    fn strings(texts: &[String]) -> (Box<[u8]>, Box<[Range]>) {
        let mut bytes = Vec::new();
        let mut ranges = Vec::new();
        for text in texts {
            ranges.push(Range {
                start: bytes.len() as u32,
                len: text.len() as u32,
            });
            bytes.extend_from_slice(text.as_bytes());
        }
        (bytes.into(), ranges.into())
    }

    /// A `modules` row of module type `module_type`.
    fn module_row(module_type: u32) -> ModuleRow {
        ModuleRow {
            module_type,
            attributes: Range::default(),
            loc: 0,
            path: 0,
        }
    }

    /// A unit `Dep` whose signature is `module M0 = {}`, then `module Mi =
    /// M(i-1)` for i up to `n - 1`, every module exported: item `i` of the
    /// signature is `Mi`, its identifier's scope is `i`, `paths[i]` names it.
    fn alias_chain(n: u32) -> Arc<Segment> {
        let (bytes, strings) = strings(&(0..n).map(|i| format!("M{i}")).collect::<Vec<_>>());
        let mut module_types = vec![ModuleTypeRow::Signature(1)];
        module_types.extend((1..n).map(|i| ModuleTypeRow::Alias {
            path: i - 1,
            present: true,
        }));
        Arc::new(Segment {
            items: (0..n)
                .map(|i| ExportItem {
                    name: i,
                    payload: i,
                    kind: ExportKind::Module,
                })
                .collect(),
            children: Box::new([
                ChildTable { start: 0, len: n },
                ChildTable { start: n, len: 0 },
            ]),
            signature: SignaturePools {
                bytes,
                strings,
                identifiers: (0..n)
                    .map(|i| IdentRow {
                        name: i,
                        stamp: i as i32 + 1,
                        flags: 0,
                        scope: i,
                    })
                    .collect(),
                paths: (0..n).map(PathRow::Ident).collect(),
                ordered_items: (0..n)
                    .map(|i| SignatureItemRow {
                        ident: i,
                        declaration: i,
                        kind: SignatureKind::Module,
                        status: ItemStatus::Ordinary,
                    })
                    .collect(),
                modules: (0..n).map(module_row).collect(),
                module_types: module_types.into(),
                ..SignaturePools::default()
            },
            ..Segment::default()
        })
    }

    /// A dependency's chain of 10,000 aliases is 10,000 steps, a loop that
    /// fits a 2 MB stack, and ends at the table of `M0`.
    #[test]
    fn ten_thousand_imported_aliases_are_one_step_each() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut s = Scopes::new();
                let name = s.names.intern("Dep");
                let unit = s.add_unit(name, alias_chain(10_001));
                let table = s.import_table(unit, 0);
                let last = Key::new(s.names.find("M10000").unwrap(), Namespace::Module);
                let row = s.search(table, last).unwrap();
                let mut shape = None;
                let count = super::super::steps::scope(|| {
                    shape = Some(s.module_shape(Resolved::import(row), &mut NoUnits))
                });
                // The last step imports `M0`'s empty table: no member, no step.
                assert_eq!(count, 10_000);
                let first = s.table_index[s.units[unit as usize].tables as usize + 1];
                assert_eq!(
                    shape.unwrap(),
                    Ok(ModuleShape::Structure(TableId(first | IMPORTED)))
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// A unit `Dep` with modules `K0` to `K17`, `Kj+1` the one member of
    /// `Kj`, and `module Ok = K0.K1....K16` (16 components waiting) and
    /// `module Deep = K0.K1....K17` (17).
    fn nested(depth: u32) -> Arc<Segment> {
        let mut texts: Vec<String> = (0..=depth).map(|j| format!("K{j}")).collect();
        texts.extend(["Ok".to_string(), "Deep".to_string()]);
        let (bytes, strings) = strings(&texts);
        let (ok, deep) = (depth + 1, depth + 2);
        // Items 0, 1, 2: K0, Ok, Deep (the unit's table); 2 + j: Kj.
        let mut items = vec![
            ExportItem {
                name: 0,
                payload: 0,
                kind: ExportKind::Module,
            },
            ExportItem {
                name: ok,
                payload: ok,
                kind: ExportKind::Module,
            },
            ExportItem {
                name: deep,
                payload: deep,
                kind: ExportKind::Module,
            },
        ];
        items.extend((1..=depth).map(|j| ExportItem {
            name: j,
            payload: j,
            kind: ExportKind::Module,
        }));
        let mut children = vec![ChildTable { start: 0, len: 3 }];
        children.extend((1..=depth).map(|j| ChildTable {
            start: 2 + j,
            len: 1,
        }));
        children.push(ChildTable {
            start: 3 + depth,
            len: 0,
        });
        let mut module_types: Vec<ModuleTypeRow> = (0..=depth)
            .map(|j| ModuleTypeRow::Signature(j + 1))
            .collect();
        for path in [depth - 1, depth] {
            module_types.push(ModuleTypeRow::Alias {
                path,
                present: true,
            });
        }
        let mut paths = vec![PathRow::Ident(0)];
        paths.extend((1..=depth).map(|j| PathRow::Dot {
            parent: j - 1,
            name: j,
            position: 0,
        }));
        Arc::new(Segment {
            items: items.into(),
            children: children.into(),
            signature: SignaturePools {
                bytes,
                strings,
                identifiers: Box::new([IdentRow {
                    name: 0,
                    stamp: 1,
                    flags: 0,
                    scope: 0,
                }]),
                paths: paths.into(),
                ordered_items: Box::new([SignatureItemRow {
                    ident: 0,
                    declaration: 0,
                    kind: SignatureKind::Module,
                    status: ItemStatus::Ordinary,
                }]),
                modules: (0..=depth + 2).map(module_row).collect(),
                module_types: module_types.into(),
                ..SignaturePools::default()
            },
            ..Segment::default()
        })
    }

    /// An alias of a dependency with 16 components waiting is followed to
    /// the innermost module; with 17 it is `Unsupported`.
    #[test]
    fn a_dependency_path_waits_on_at_most_sixteen_components() {
        let depth = PENDING as u32 + 1;
        let mut s = Scopes::new();
        let name = s.names.intern("Dep");
        let unit = s.add_unit(name, nested(depth));
        let table = s.import_table(unit, 0);
        let shape = |s: &mut Scopes, text: &str| {
            let key = Key::new(s.names.find(text).unwrap(), Namespace::Module);
            let row = s.search(table, key).unwrap();
            s.module_shape(Resolved::import(row), &mut NoUnits)
        };
        // `Ok` is `K16`, whose table holds `K17`.
        let Ok(ModuleShape::Structure(k16)) = shape(&mut s, "Ok") else {
            panic!("Ok is a structure");
        };
        let k17 = Key::new(s.names.find("K17").unwrap(), Namespace::Module);
        assert!(s.search(k16, k17).is_some());
        assert_eq!(shape(&mut s, "Deep"), Err(UNSUPPORTED));
    }

    /// `candidates_in` of a key with 10,000 members, in a table that has
    /// 10,000 more of other keys: one search (at most 15 comparisons) and
    /// one step a candidate, in table order.
    #[test]
    fn ten_thousand_qualified_candidates_are_one_step_each() {
        let mut s = Scopes::new();
        let a = Key::new(s.names.intern("A"), Namespace::Constructor);
        let b = Key::new(s.names.intern("B"), Namespace::Constructor);
        let rows: Vec<(Key, Binder)> = (0..20_000)
            .map(|i| {
                let key = if i % 2 == 0 { a } else { b };
                (key, s.binders.push(key, 0, 0, BinderKind::Constructor))
            })
            .collect();
        let table = s.table_from(&rows);
        let mut out = Vec::with_capacity(10_000);
        let count = super::super::steps::scope(|| s.candidates_in(table, a, &mut out));
        assert!(count <= 10_000 + 15, "{count}");
        assert_eq!(out.len(), 10_000);
        assert!(
            out.iter()
                .zip(rows.iter().step_by(2))
                .all(|(found, &(_, binder))| {
                    *found
                        == Found {
                            item: Resolved::binder(binder),
                            layer: NONE,
                        }
                })
        );
    }
}
