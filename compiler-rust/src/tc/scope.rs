//! Binders, scopes, opened layers and member tables (R4).
//!
//! Everything a name can mean while a unit is checked is a row here, and
//! [`Scopes`] is the one mutable structure the walk holds for names. Nothing
//! in it is cloned, shared or reference counted; an environment that has to
//! be remembered is a scope index.
//!
//! - A **binder** is a dense index into parallel arrays ([`Binders`]). It is
//!   never reused within a unit, so a row of the walk can keep it.
//! - The **head table** maps a [`Key`] (interned name and namespace) to the
//!   innermost binder of that key, or [`NONE`]. Binding writes the head and
//!   remembers the binder it hid in `Binders::previous`; the **log** lists the
//!   binders bound in the active scopes so that leaving a scope restores the
//!   heads. A lookup of a local name is one load.
//! - A **member table** is a sorted run of [`Member`] rows: the members of a
//!   module of this unit, or one export table of a dependency's segment
//!   imported into this worker's names. An **opened layer** points at a
//!   member table. Layers are probed only when they are younger than the
//!   head binder (`Layer::mark`).
//!
//! The fields are public inside the crate: `tc::names`, the walk (R5b) and
//! the tests read the rows directly.
//!
//! Step counts (`tc::steps`, test builds): one tick per binder pushed, per
//! binding written, per binding undone, per head load, per comparison of a
//! table search, per member written to a table (local or imported), per
//! log entry `seal` reads, per candidate produced, per alias followed, per
//! component of a path, per answer of `unit_by_name` and of `import_table`
//! that was known before, per `mark`, per `use_found`, per module of
//! `use_modules`, per armed entry `finish` reads, per `read_unit` and
//! `read_item`. `enter`, `open`, `arm` and the other O(1) calls that are
//! in none of these tick nothing.

use std::sync::Arc;

use super::name_table::{Name, NameTable};
use super::segment::{ExportItem, Segment};

pub use super::graph::NONE;

/// The table a name is looked up in (compiler/ml/env.ml:416-431). A unit is
/// not a namespace: units are looked up in `Scopes::unit_heads`. The
/// discriminants are `segment::ExportKind`'s, so an export item's kind is
/// its namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Namespace {
    Value = 0,
    Type = 1,
    Constructor = 2,
    Label = 3,
    Module = 4,
    ModuleType = 5,
}

/// An interned name with its namespace: `name << 3 | namespace`. Indexes the
/// head table and orders a member table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Key(pub u32);

impl Key {
    /// O(1).
    pub const fn new(name: Name, namespace: Namespace) -> Key {
        Key(name.0 << 3 | namespace as u32)
    }

    /// O(1).
    pub const fn name(self) -> Name {
        Name(self.0 >> 3)
    }

    /// O(1): the namespace bits, as [`Namespace`]'s discriminant.
    pub const fn namespace(self) -> u32 {
        self.0 & 7
    }
}

/// Index of a bound name in [`Binders`]. Below 2^30.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Binder(pub u32);

/// What a binder is. It decides the namespace, what `Binders::payload` holds
/// and which unused warning the binder can raise (compiler/ml/warnings.ml:
/// 26 and 27 for a variable, 32 for a value, 34 for a type, 37 for a
/// constructor, 60 for a module).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum BinderKind {
    /// A `let`-bound value. Payload: its type (`Ty`).
    Let,
    /// A function parameter or a pattern variable. Payload: its type.
    Variable,
    /// An `external`. Payload: its type.
    External,
    /// A type declaration. Payload: its index in `expand::TypeTable`.
    Type,
    /// A constructor of a variant. Payload: its member row.
    Constructor,
    /// An extension constructor or exception. Payload: its row.
    Extension,
    /// A record label. Payload: its member row.
    Label,
    /// A module with members. Payload: its [`TableId`], or [`NONE`] for a
    /// functor.
    Module,
    /// `module N = M`. Payload: the [`Resolved`] of `M`.
    ModuleAlias,
    /// A functor's parameter. Payload: its [`TableId`].
    FunctorParameter,
    /// A module type. Payload: its row.
    ModuleType,
}

impl BinderKind {
    /// O(1): the namespace a binder of this kind is bound in.
    pub const fn namespace(self) -> Namespace {
        match self {
            BinderKind::Let | BinderKind::Variable | BinderKind::External => Namespace::Value,
            BinderKind::Type => Namespace::Type,
            BinderKind::Constructor | BinderKind::Extension => Namespace::Constructor,
            BinderKind::Label => Namespace::Label,
            BinderKind::Module | BinderKind::ModuleAlias | BinderKind::FunctorParameter => {
                Namespace::Module
            }
            BinderKind::ModuleType => Namespace::ModuleType,
        }
    }
}

/// `Binders::used` bit: a lookup or an inclusion check used the binder
/// (`Env.mark_value_used`, `mark_type_used`, `mark_module_used`,
/// compiler/ml/env.ml:947-950, 1080-1088).
pub const USED: u8 = 1;
/// `Binders::used` bits of a constructor (`constructor_usages`,
/// compiler/ml/env.ml:38-47): built, matched, exported through a private type.
pub const POSITIVE: u8 = 2;
pub const PATTERN: u8 = 4;
pub const PRIVATIZE: u8 = 8;
/// `Binders::used` bit: the declaration carries `@deprecated`.
pub const DEPRECATED: u8 = 16;

/// The bound names of one unit: parallel arrays indexed by [`Binder`], 18
/// bytes a binder. Append-only while a unit is checked; truncated to the
/// frozen prefix by [`Scopes::reset`].
#[derive(Default)]
pub struct Binders {
    /// The binder's [`Key`].
    pub key: Vec<u32>,
    /// By [`BinderKind`]: a type, a type index, a member row, a table, the
    /// target of an alias. Written by the slice that makes the binder.
    pub payload: Vec<u32>,
    /// The location of the declaration (a `locations` handle of the unit).
    pub loc: Vec<u32>,
    /// The binder of the same key this one hid when it was bound, or
    /// [`NONE`]. Written by [`Scopes::bind`]; it is the undo datum of the
    /// log and the chain [`Scopes::candidates`] follows.
    pub previous: Vec<u32>,
    pub kind: Vec<BinderKind>,
    /// [`USED`], [`POSITIVE`], [`PATTERN`], [`PRIVATIZE`], [`DEPRECATED`].
    pub used: Vec<u8>,
}

impl Binders {
    /// Amortized O(1), 1 step: one row in each array. The binder is not in
    /// scope until [`Scopes::bind`]. `previous` starts at [`NONE`] and
    /// `used` at 0. Panics at 2^30 binders.
    pub fn push(&mut self, key: Key, payload: u32, loc: u32, kind: BinderKind) -> Binder {
        todo!("R4a")
    }

    /// O(1): how many binders exist; the age a layer is compared with.
    pub fn len(&self) -> u32 {
        self.key.len() as u32
    }

    /// O(1).
    pub fn is_empty(&self) -> bool {
        self.key.is_empty()
    }
}

/// One scope: 12 bytes. Scopes are entered and left in stack order; a row
/// stays after its scope is left, so a remembered index stays meaningful
/// (parent chain, first binder, innermost layer), but a lookup by name is
/// only possible in the current scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Scope {
    /// The enclosing scope, or [`NONE`] for scope 0.
    pub parent: u32,
    /// `Binders::len` when the scope was entered.
    pub first_binder: u32,
    /// The innermost opened layer visible in the scope, or [`NONE`].
    pub opens: u32,
}

/// A member table: 4 bytes. Bit 31 set: an imported table (`Scopes::
/// imported_tables`, kept for the worker); clear: a table of this unit
/// (`Scopes::tables`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TableId(pub u32);

/// [`TableId`] bit of an imported table.
pub const IMPORTED: u32 = 1 << 31;

/// A run of [`Member`] rows sorted by key: 12 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Table {
    /// First row, in `Scopes::members` or `Scopes::imported_members`.
    pub first: u32,
    pub len: u32,
    /// The unit an imported table was read from; [`NONE`] for a local one.
    pub unit: u32,
}

/// `Member::origin` of a member of this unit.
pub const LOCAL: u32 = NONE;
/// `Member::origin` bits 0..24 of an imported member: its unit's index.
pub const UNIT_MASK: u32 = (1 << 24) - 1;
/// `Member::origin` bit of an imported member whose declaration carries
/// `@deprecated`.
pub const MEMBER_DEPRECATED: u32 = 1 << 24;

/// One member of a table: 12 bytes. Rows of one table are sorted by `key`;
/// rows of one key (constructors, labels) are in candidate order, the one a
/// lookup finds first coming first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Member {
    /// The member's [`Key`].
    pub key: u32,
    /// Local: the member's [`Binder`]. Imported: the index of its
    /// `ExportItem` in the unit's `Segment::items`.
    pub target: u32,
    /// [`LOCAL`], or the unit index with [`MEMBER_DEPRECATED`].
    pub origin: u32,
}

/// One opened layer: 12 bytes. Layers of a scope chain are a list through
/// `older`, innermost first. Layer `i` belongs to `Scopes::opens[i]`: an
/// open makes one of each.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Layer {
    pub table: TableId,
    /// `Binders::len` when the layer was opened: the layer hides exactly the
    /// binders below it.
    pub mark: u32,
    /// The next older visible layer, or [`NONE`].
    pub older: u32,
}

/// `Open::flags` bit: a lookup went through the layer (the `used_slot` of
/// `Env.open_signature`, compiler/ml/env.ml:1881).
pub const OPEN_USED: u32 = 1;
/// `Open::flags` bit: `open!`; the layer reports no shadowing
/// (compiler/ml/env.ml:1884, `ovf = Fresh`).
pub const OPEN_OVERRIDE: u32 = 2;

/// One `open`: 16 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Open {
    /// The location of the `open`, where its warnings are reported.
    pub loc: u32,
    /// The opened path as the caller names it (a handle the reporter
    /// prints); R4 stores it and never reads it.
    pub root: u32,
    /// First [`ShadowNote`] of this open, or [`NONE`].
    pub shadowed: u32,
    /// [`OPEN_USED`], [`OPEN_OVERRIDE`].
    pub flags: u32,
}

/// One name an open was already reported to shadow: 8 bytes. The list of an
/// open is `shadowed` of compiler/ml/env.ml:1883.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct ShadowNote {
    pub key: u32,
    pub next: u32,
}

/// What a name resolved to: 4 bytes, the value the walk stores in a row
/// (`ExprRow::resolved`). Bits 31..30: `00` a [`Binder`] of this unit; `10`
/// a row of `Scopes::imported_members` (an item of a dependency); `11` a
/// unit as a whole (`Scopes::units`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Resolved(pub u32);

/// What kind of thing a [`Resolved`] names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolvedKind {
    Binder(Binder),
    /// A row of `Scopes::imported_members`.
    Import(u32),
    /// An index of `Scopes::units`.
    Unit(u32),
}

impl Resolved {
    /// O(1).
    pub const fn binder(binder: Binder) -> Resolved {
        Resolved(binder.0)
    }

    /// O(1).
    pub const fn import(row: u32) -> Resolved {
        Resolved(row | 2 << 30)
    }

    /// O(1).
    pub const fn unit(unit: u32) -> Resolved {
        Resolved(unit | 3 << 30)
    }

    /// O(1).
    pub const fn kind(self) -> ResolvedKind {
        match self.0 >> 30 {
            2 => ResolvedKind::Import(self.0 & !(3 << 30)),
            3 => ResolvedKind::Unit(self.0 & !(3 << 30)),
            _ => ResolvedKind::Binder(Binder(self.0)),
        }
    }
}

/// The answer of a lookup by name: 8 bytes. Passed to `Scopes::use_found`,
/// which needs the layer for the open's usage and shadowing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Found {
    pub item: Resolved,
    /// The opened layer the item was found through (also the index of its
    /// open), or [`NONE`].
    pub layer: u32,
}

/// A dependency this worker has read: 16 bytes. Kept for the worker.
pub struct UnitSlot {
    pub segment: Arc<Segment>,
    pub name: Name,
    /// First of the unit's `Segment::children.len()` slots in
    /// `Scopes::table_index`.
    pub tables: u32,
}

/// `Scopes::unit_heads` value of a name no unit has (asked once).
pub const MISSING: u32 = NONE - 1;

/// Where a worker gets a unit it has not read yet. The checker asks once per
/// name and worker; the answer is kept in `Scopes::unit_heads`. R5c
/// implements it over the world with `bridge::from_old::published_segment`;
/// tests implement it over a list.
pub trait UnitSource {
    /// The published segment of the unit `name`, or `None` when there is no
    /// such unit. Not on a per-lookup path.
    fn segment(&mut self, name: &str) -> Option<Arc<Segment>>;
}

/// The lengths that [`Scopes::freeze`] records and [`Scopes::reset`]
/// restores: everything before them is the prefix every unit starts with.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Frozen {
    pub binders: u32,
    pub scopes: u32,
    pub log: u32,
    pub layers: u32,
    pub opens: u32,
    pub tables: u32,
    pub members: u32,
}

/// One warning a lookup raised or the end of the unit found: 16 bytes, in
/// the order raised. Text and printing are the reporter's (R5c).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Warning {
    pub kind: WarningKind,
    /// Where it is reported: the use (deprecation), the `open` (shadowing,
    /// unused open), the declaration (unused binder).
    pub loc: u32,
    /// `Deprecated`: the [`Resolved`] used. `OpenShadows`: the [`Key`]
    /// shadowed. `Unused`: the [`Binder`]. `UnusedOpen`: the open's index.
    pub a: u32,
    /// `OpenShadows`: the open's index. Otherwise 0.
    pub b: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum WarningKind {
    /// Warning 3, raised by `Scopes::deprecated` at the use.
    Deprecated,
    /// Warnings 44 (value, type, module, module type) and 45 (constructor,
    /// label). 44 is raised by `Scopes::use_found` at the first use that
    /// goes through the open and hides something; 45 by `Scopes::shadows`,
    /// when the walk found that the two result types differ.
    OpenShadows,
    /// Warnings 26, 27, 32, 34, 37, 60 by the binder's kind, raised by
    /// `Scopes::finish`.
    Unused,
    /// Warning 33, raised by `Scopes::finish`.
    UnusedOpen,
}

/// `Scopes::armed` bit of an entry that is an open's index, not a binder.
pub const ARMED_OPEN: u32 = 1 << 31;

/// Everything about names for one worker. One value per worker; a unit
/// starts with [`Scopes::reset`].
///
/// Kept for the worker: `names`, `units`, `unit_heads`, `imported_tables`,
/// `imported_members`, `table_index`, and the frozen prefix of the rest.
/// Per unit: everything else.
#[derive(Default)]
pub struct Scopes {
    pub names: NameTable,
    pub binders: Binders,

    /// Every scope of the unit, in the order entered.
    pub scopes: Vec<Scope>,
    /// The current scope; [`NONE`] before scope 0 is entered.
    pub current: u32,
    /// `log.len()` when each active scope was entered, outermost first.
    pub entered: Vec<u32>,
    /// The binders bound in the active scopes, in binding order: 4 bytes a
    /// binding. Leaving a scope pops its part.
    pub log: Vec<u32>,
    /// By [`Key`]: the innermost binder of the key, or [`NONE`]. A key
    /// beyond the end has no binder. Never cleared: leaving every scope
    /// restores it.
    pub heads: Vec<u32>,

    pub layers: Vec<Layer>,
    pub opens: Vec<Open>,
    pub notes: Vec<ShadowNote>,
    /// Member tables of this unit and their rows.
    pub tables: Vec<Table>,
    pub members: Vec<Member>,

    /// The dependencies this worker has read.
    pub units: Vec<UnitSlot>,
    /// By [`Name`]: the unit's index, [`NONE`] when never asked, [`MISSING`].
    pub unit_heads: Vec<u32>,
    pub imported_tables: Vec<Table>,
    pub imported_members: Vec<Member>,
    /// `table_index[unit.tables + s]`: the imported [`TableId`] of export
    /// table `s` of the unit, or [`NONE`] while this worker has not
    /// imported it.
    pub table_index: Vec<u32>,

    /// Binders and opens (with [`ARMED_OPEN`]) whose unused warning is
    /// wanted, in the order armed (`Env.add_delayed_check_forced`).
    pub armed: Vec<u32>,
    /// The warnings raised so far, in order.
    pub warnings: Vec<Warning>,

    /// Units read by this unit, in the order first read.
    pub read_units: Vec<u32>,
    /// By unit index: `READ` or `READ_WEAK` bits of this unit's reads.
    pub unit_read: Vec<u8>,
    /// Rows of `imported_members` read by this unit, in the order first read.
    pub read_items: Vec<u32>,
    /// By row of `imported_members`: one bit, set while the row is in
    /// `read_items`.
    pub item_read: Vec<u64>,

    pub frozen: Frozen,
}

impl Scopes {
    /// O(1): an empty structure with no scope entered. (`Default` would make
    /// scope 0 current before it exists.)
    pub fn new() -> Scopes {
        Scopes {
            current: NONE,
            ..Scopes::default()
        }
    }

    // ----- R4b: scopes, the head table, the undo log -----

    /// O(1), no step: enter a scope inside the current one and make it
    /// current. Its `opens` is the parent's. Returns its index.
    pub fn enter(&mut self) -> u32 {
        todo!("R4b")
    }

    /// O(bindings made in the scope), 1 step a binding: restore the head of
    /// every binding made since the scope was entered, innermost first
    /// (`heads[key] = previous`), pop the log, make the parent current. The
    /// scope's layers stop being visible because `opens` is per scope; no
    /// layer row is touched. Panics when no scope is entered.
    pub fn leave(&mut self) {
        todo!("R4b")
    }

    /// Amortized O(1), 1 step: put a binder in scope. Writes
    /// `previous[binder] = heads[key]`, `heads[key] = binder` and one log
    /// entry; grows `heads` to the name table's size when the key is beyond
    /// it. Ages compare by index: no layer visible now may have a mark above
    /// the binder (a binder is pushed after every open that is to hide
    /// nothing of it), checked by a debug assertion on the innermost layer.
    pub fn bind(&mut self, binder: Binder) {
        todo!("R4b")
    }

    /// 1 step, one load: the innermost binder of `key`, ignoring opened
    /// layers; [`NONE`] when the key has none or is beyond the table.
    pub fn head(&self, key: Key) -> u32 {
        todo!("R4b")
    }

    /// O(1): the length of the log now. Taken when a structure is entered
    /// and given to [`Scopes::seal`] when it ends.
    pub fn log_mark(&self) -> u32 {
        self.log.len() as u32
    }

    /// O(1): record the current lengths as the prefix every unit starts
    /// with (predefined types, the initially opened modules). Called once
    /// per worker, with scope 0 current.
    pub fn freeze(&mut self) {
        todo!("R4b")
    }

    /// O(bindings above the prefix + reads of the last unit): leave every
    /// scope above scope 0, truncate the per-unit arrays to the frozen
    /// lengths, clear `armed`, `warnings` and the read marks by walking
    /// `read_units` and `read_items` (not the whole bit sets). Names, units
    /// and imported tables stay.
    pub fn reset(&mut self) {
        todo!("R4b")
    }

    // ----- R4c: member tables of this unit, opened layers, lookup -----

    /// O(n log n) comparisons, n steps (one a member written): a local
    /// member table of `(key, binder)` pairs. The sort is stable: members
    /// of one key keep the order given, which must be candidate order.
    pub fn table_from(&mut self, members: &[(Key, Binder)]) -> TableId {
        todo!("R4c")
    }

    /// O(n log n) comparisons, n steps for the n log entries since `from`:
    /// the member table of a structure that ends now, from the bindings
    /// made since [`Scopes::log_mark`] returned `from` that are still in
    /// scope. A value, type, module or module type is a member when it is
    /// the head of its key (a later binding of the name replaced it); every
    /// constructor and label is a member, the younger first within a key
    /// (`comp_constrs` and `comp_labels` are lists, compiler/ml/env.ml:
    /// 1480-1500). Must be called before the structure's scopes are left.
    pub fn seal(&mut self, from: u32) -> TableId {
        todo!("R4c")
    }

    /// O(1), no step: open `table` in the current scope. Pushes one
    /// [`Open`] and one [`Layer`] (at the same index) with
    /// `mark = Binders::len()` and makes it the scope's innermost layer.
    /// Returns that index
    /// (compiler/ml/env.ml:1874-1911).
    pub fn open(&mut self, table: TableId, loc: u32, root: u32, flags: u32) -> u32 {
        todo!("R4c")
    }

    /// At most floor(log2 n) + 1 steps (one a comparison) for a table of n
    /// members, no allocation: the first row of `key` in `table`, as an
    /// index into `members` or `imported_members`, or `None`.
    pub fn search(&self, table: TableId, key: Key) -> Option<u32> {
        todo!("R4c")
    }

    /// O(1): the row `search` or a [`Resolved`] names, from the pool
    /// `table` selects.
    pub fn member(&self, table: TableId, row: u32) -> Member {
        todo!("R4c")
    }

    /// The binding a lookup of `key` finds (`IdTbl.find_name`,
    /// compiler/ml/env.ml:272-289): the innermost of the head binder and
    /// the members of the visible layers. 1 step for the head, then one
    /// [`Scopes::search`] per layer younger than the head binder, innermost
    /// first, stopping at the first that has the key. With no head binder
    /// every visible layer is probed. No allocation, no write.
    pub fn find(&self, key: Key) -> Option<Found> {
        todo!("R4c")
    }

    /// What `layer`'s member hides: the lookup of `key` restricted to
    /// everything older than `layer` (`find_name false name next`,
    /// compiler/ml/env.ml:284-287). Same cost as [`Scopes::find`] from the
    /// layer's `older`, with the head binder counted only when below the
    /// layer's mark (else its `previous` chain is followed, 1 step a
    /// binder).
    pub fn find_below(&self, key: Key, layer: u32) -> Option<Found> {
        todo!("R4c")
    }

    /// Every candidate of `key`, innermost first, appended to `out`
    /// (`TycompTbl.find_all`, compiler/ml/env.ml:202-213): the binders of
    /// the key through `previous` and the members of every visible layer,
    /// merged by age (a layer comes before the binders below its mark). 1
    /// step a candidate, plus one [`Scopes::search`] per visible layer. No
    /// allocation when `out` has capacity.
    pub fn candidates(&self, key: Key, out: &mut Vec<Found>) {
        todo!("R4c")
    }

    // ----- R4d: dependencies as member tables -----

    /// Amortized O(1): register a unit this worker has not seen, with
    /// `Segment::children.len()` empty slots in `table_index`, and point
    /// `unit_heads[name]` at it. Returns its index. One `Arc` clone per
    /// worker and unit, never per lookup. Panics at 2^24 units.
    pub fn add_unit(&mut self, name: Name, segment: Arc<Segment>) -> u32 {
        todo!("R4d")
    }

    /// 1 step, one load when the name was asked before (from R4g on, one
    /// more step for the read it logs); otherwise one call
    /// of `source` and [`Scopes::add_unit`], or `MISSING` recorded. `None`
    /// when no unit has the name (`find_pers_struct`, compiler/ml/env.ml:
    /// 646-691).
    pub fn unit_by_name(&mut self, name: Name, source: &mut dyn UnitSource) -> Option<u32> {
        todo!("R4d")
    }

    /// The imported table of export table `signature` of `unit`
    /// (`Segment::children[signature]`). 1 step, one load when this worker
    /// imported it before. The first time: one row per export item, n
    /// steps, n interns of the items' names (one hash each), a stable sort
    /// by key (O(n log n) comparisons), and for each item a scan of its
    /// declaration's attributes for `@deprecated` (`MEMBER_DEPRECATED`).
    /// An item's namespace is its `ExportKind`; items of one key keep the
    /// segment's order.
    pub fn import_table(&mut self, unit: u32, signature: u32) -> TableId {
        todo!("R4d")
    }

    /// O(1), three loads: the segment and export item a row of
    /// `imported_members` names.
    pub fn item(&self, row: u32) -> (&Segment, &ExportItem) {
        todo!("R4d")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        macro_rules! sizes {
            ($($ty:ty => $n:expr),* $(,)?) => { $(assert_eq!(std::mem::size_of::<$ty>(), $n, stringify!($ty));)* };
        }
        sizes!(
            Namespace => 1, Key => 4, Binder => 4, BinderKind => 1, Scope => 12,
            TableId => 4, Table => 12, Member => 12, Layer => 12, Open => 16,
            ShadowNote => 8, Resolved => 4, Found => 8, UnitSlot => 16,
            Warning => 16, WarningKind => 1, Frozen => 28,
        );
        // What the walk passes down or stores per node.
        assert!(std::mem::size_of::<Found>() <= 16);
        assert!(std::mem::size_of::<Option<Found>>() <= 16);
    }

    #[test]
    fn keys_and_resolutions_round_trip() {
        let key = Key::new(Name(12345), Namespace::Label);
        assert_eq!(
            (key.name(), key.namespace()),
            (Name(12345), Namespace::Label as u32)
        );
        assert!(Key::new(Name(1), Namespace::Value) < Key::new(Name(1), Namespace::Type));
        use crate::tc::segment::ExportKind;
        for (ns, kind) in [
            (Namespace::Value, ExportKind::Value),
            (Namespace::Type, ExportKind::Type),
            (Namespace::Constructor, ExportKind::Constructor),
            (Namespace::Label, ExportKind::Label),
            (Namespace::Module, ExportKind::Module),
            (Namespace::ModuleType, ExportKind::ModuleType),
        ] {
            assert_eq!(ns as u8, kind as u8);
        }
        assert!(Key::new(Name(1), Namespace::Label) < Key::new(Name(2), Namespace::Value));
        assert_eq!(
            Resolved::binder(Binder(7)).kind(),
            ResolvedKind::Binder(Binder(7))
        );
        assert_eq!(Resolved::import(7).kind(), ResolvedKind::Import(7));
        assert_eq!(Resolved::unit(7).kind(), ResolvedKind::Unit(7));
        assert_eq!(BinderKind::ModuleAlias.namespace(), Namespace::Module);
    }
}
