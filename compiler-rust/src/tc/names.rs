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
    Binder, BinderKind, Found, Key, NONE, Namespace, Resolved, ResolvedKind, Scopes, TableId,
    UnitSource,
};

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
        let mut at = module;
        loop {
            match at.kind() {
                ResolvedKind::Binder(binder) => {
                    let payload = self.binders.payload[binder.0 as usize];
                    match self.binders.kind[binder.0 as usize] {
                        // A functor's binder has no table (`Functor_comps`,
                        // compiler/ml/env.ml:966).
                        BinderKind::Module if payload == NONE => return Ok(ModuleShape::Functor),
                        BinderKind::Module => return Ok(ModuleShape::Structure(TableId(payload))),
                        BinderKind::FunctorParameter => {
                            return Ok(ModuleShape::Abstract(TableId(payload)));
                        }
                        // `module N = M`: the alias is followed when its
                        // members are needed (`normalize_path`,
                        // compiler/ml/env.ml:854-880), one step each.
                        BinderKind::ModuleAlias => {
                            #[cfg(test)]
                            super::steps::tick();
                            at = Resolved(payload);
                        }
                        _ => return Err(UNSUPPORTED),
                    }
                }
                ResolvedKind::Unit(unit) => {
                    return Ok(ModuleShape::Structure(self.import_table(unit, 0)));
                }
                ResolvedKind::Import(_) => return Err(UNSUPPORTED),
            }
        }
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
        todo!("R4e")
    }

    /// Every member of `key` in a module's table, in candidate order,
    /// appended to `out` with `layer` `NONE` (the qualified case of
    /// `lookup_all_simple`, compiler/ml/env.ml:1039-1045): one
    /// [`Scopes::search`] and 1 step a candidate.
    pub fn candidates_in(&self, table: TableId, key: Key, out: &mut Vec<Found>) {
        todo!("R4e")
    }

    // ----- R4f: usage and the warnings of a lookup -----

    /// O(1): ask for the unused warning of a binder at the end of the unit
    /// (`Env.check_usage`, compiler/ml/env.ml:1562-1576, registers its
    /// delayed check when the declaration enters the environment). The
    /// order of the calls is the order of the warnings.
    pub fn arm(&mut self, binder: Binder) {
        todo!("R4f")
    }

    /// O(1): the same for an open (`Unused_open`,
    /// compiler/ml/env.ml:1890-1894).
    pub fn arm_open(&mut self, open: u32) {
        todo!("R4f")
    }

    /// O(1): the length of `armed`, for [`Scopes::disarm`].
    pub fn armed_mark(&self) -> u32 {
        self.armed.len() as u32
    }

    /// O(1): forget what was armed since `mark` (a speculative typing that
    /// was undone drops its delayed checks).
    pub fn disarm(&mut self, mark: u32) {
        todo!("R4f")
    }

    /// 1 step, one load and one store: set used bits of a binder
    /// (`mark_value_used`, `mark_type_used`, `mark_constructor_used`,
    /// compiler/ml/env.ml:1080-1093). `bits` is `USED` or a constructor's
    /// usage.
    pub fn mark(&mut self, binder: Binder, bits: u8) {
        todo!("R4f")
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
        todo!("R4f")
    }

    /// O(1), no step: the walk found that the constructor or label `key`
    /// used through open `layer` has another result type than the one it
    /// hides. Adds the open's [`ShadowNote`] for `key` and pushes
    /// `OpenShadows` at the open's location (`Open_shadow_label_constructor`,
    /// compiler/ml/env.ml:1897-1906). Called only with a `layer` and `key`
    /// for which [`Scopes::use_found`] just returned `Some`: the note list
    /// is not scanned again.
    pub fn shadows(&mut self, layer: u32, key: Key) {
        todo!("R4f")
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
        todo!("R4f")
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
    }
}
