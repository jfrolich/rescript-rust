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
        #[cfg(test)]
        super::steps::tick();
        let binder = self.len();
        assert!(binder < 1 << 30, "more than 2^30 binders");
        self.key.push(key.0);
        self.payload.push(payload);
        self.loc.push(loc);
        self.previous.push(NONE);
        self.kind.push(kind);
        self.used.push(0);
        Binder(binder)
    }

    /// O(rows removed): drop every binder from `len` on, in all six arrays.
    fn truncate(&mut self, len: u32) {
        let len = len as usize;
        self.key.truncate(len);
        self.payload.truncate(len);
        self.loc.truncate(len);
        self.previous.truncate(len);
        self.kind.truncate(len);
        self.used.truncate(len);
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
        let index = self.scopes.len() as u32;
        let opens = match self.current {
            NONE => NONE,
            parent => self.scopes[parent as usize].opens,
        };
        self.scopes.push(Scope {
            parent: self.current,
            first_binder: self.binders.len(),
            opens,
        });
        self.entered.push(self.log.len() as u32);
        self.current = index;
        index
    }

    /// O(bindings made in the scope), 1 step a binding: restore the head of
    /// every binding made since the scope was entered, innermost first
    /// (`heads[key] = previous`), pop the log, make the parent current. The
    /// scope's layers stop being visible because `opens` is per scope; no
    /// layer row is touched. Panics when no scope is entered.
    pub fn leave(&mut self) {
        let mark = self.entered.pop().expect("leave with no scope entered");
        self.undo_to(mark);
        self.current = self.scopes[self.current as usize].parent;
    }

    /// O(log entries above `mark`), 1 step an entry: pop the log down to
    /// `mark`, restoring `heads[key] = previous` for each binder popped,
    /// innermost first.
    fn undo_to(&mut self, mark: u32) {
        while self.log.len() as u32 > mark {
            #[cfg(test)]
            super::steps::tick();
            let binder = self.log.pop().expect("the log is above the mark") as usize;
            let key = self.binders.key[binder] as usize;
            self.heads[key] = self.binders.previous[binder];
        }
    }

    /// Amortized O(1), 1 step: put a binder in scope. Writes
    /// `previous[binder] = heads[key]`, `heads[key] = binder` and one log
    /// entry; grows `heads` to the name table's size when the key is beyond
    /// it. Ages compare by index: no layer visible now may have a mark above
    /// the binder (a binder is pushed after every open that is to hide
    /// nothing of it), checked by a debug assertion on the innermost layer.
    pub fn bind(&mut self, binder: Binder) {
        #[cfg(test)]
        super::steps::tick();
        debug_assert!(self.current != NONE, "bind with no scope entered");
        debug_assert!(
            match self.scopes[self.current as usize].opens {
                NONE => true,
                layer => self.layers[layer as usize].mark <= binder.0,
            },
            "a binder older than a visible layer is bound"
        );
        let key = self.binders.key[binder.0 as usize] as usize;
        if key >= self.heads.len() {
            // Every key of a name below `names.len()` is below this.
            self.heads.resize(8 * self.names.len() as usize, NONE);
        }
        self.binders.previous[binder.0 as usize] = self.heads[key];
        self.heads[key] = binder.0;
        self.log.push(binder.0);
    }

    /// 1 step, one load: the innermost binder of `key`, ignoring opened
    /// layers; [`NONE`] when the key has none or is beyond the table.
    pub fn head(&self, key: Key) -> u32 {
        #[cfg(test)]
        super::steps::tick();
        self.heads.get(key.0 as usize).copied().unwrap_or(NONE)
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
        debug_assert_eq!(self.entered.len(), 1, "freeze outside scope 0");
        self.frozen = Frozen {
            binders: self.binders.len(),
            scopes: self.scopes.len() as u32,
            log: self.log.len() as u32,
            layers: self.layers.len() as u32,
            opens: self.opens.len() as u32,
            tables: self.tables.len() as u32,
            members: self.members.len() as u32,
        };
    }

    /// O(bindings above the prefix + reads of the last unit): leave every
    /// scope above scope 0, truncate the per-unit arrays to the frozen
    /// lengths, clear `armed`, `warnings` and the read marks by walking
    /// `read_units` and `read_items` (not the whole bit sets). Names, units
    /// and imported tables stay.
    pub fn reset(&mut self) {
        let frozen = self.frozen;
        while self.entered.len() > 1 {
            self.leave();
        }
        // Bindings made in scope 0 after the freeze.
        self.undo_to(frozen.log);
        // Layers scope 0 opened after the freeze: one load each through
        // `older` (layers are appended, so an older layer has a lower index).
        if self.current != NONE {
            let scope = &mut self.scopes[self.current as usize];
            while scope.opens != NONE && scope.opens >= frozen.layers {
                scope.opens = self.layers[scope.opens as usize].older;
            }
        }
        // The opens of the prefix start the next unit unused and with no
        // name reported: one write per open of the prefix, a per-worker
        // constant. Notes are written by lookups, which come after the
        // freeze, so the prefix has none and `notes` is emptied.
        for open in &mut self.opens[..frozen.opens as usize] {
            open.shadowed = NONE;
            open.flags &= !OPEN_USED;
        }
        self.binders.truncate(frozen.binders);
        self.scopes.truncate(frozen.scopes as usize);
        self.layers.truncate(frozen.layers as usize);
        self.opens.truncate(frozen.opens as usize);
        self.notes.clear();
        self.tables.truncate(frozen.tables as usize);
        self.members.truncate(frozen.members as usize);
        self.armed.clear();
        self.warnings.clear();
        for &unit in &self.read_units {
            self.unit_read[unit as usize] = 0;
        }
        self.read_units.clear();
        for &row in &self.read_items {
            self.item_read[row as usize / 64] &= !(1 << (row % 64));
        }
        self.read_items.clear();
    }

    // ----- R4c: member tables of this unit, opened layers, lookup -----

    /// O(n log n) comparisons, n steps (one a member written): a local
    /// member table of `(key, binder)` pairs. The sort is stable: members
    /// of one key keep the order given, which must be candidate order.
    pub fn table_from(&mut self, members: &[(Key, Binder)]) -> TableId {
        let first = self.members.len() as u32;
        for &(key, binder) in members {
            #[cfg(test)]
            super::steps::tick();
            self.members.push(Member {
                key: key.0,
                target: binder.0,
                origin: LOCAL,
            });
        }
        self.close_table(first)
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
        let first = self.members.len() as u32;
        // Younger first, so that the stable sort leaves the rows of one
        // constructor or label key in candidate order.
        for &binder in self.log[from as usize..].iter().rev() {
            #[cfg(test)]
            super::steps::tick();
            let key = self.binders.key[binder as usize];
            let ns = Key(key).namespace();
            // A value, type, module or module type is a member unless a
            // later binding of its name in the structure replaced it.
            let member = ns == Namespace::Constructor as u32
                || ns == Namespace::Label as u32
                || self.heads[key as usize] == binder;
            if member {
                self.members.push(Member {
                    key,
                    target: binder,
                    origin: LOCAL,
                });
            }
        }
        self.close_table(first)
    }

    /// O(1), no step: open `table` in the current scope. Pushes one
    /// [`Open`] and one [`Layer`] (at the same index) with
    /// `mark = Binders::len()` and makes it the scope's innermost layer.
    /// Returns that index
    /// (compiler/ml/env.ml:1874-1911).
    pub fn open(&mut self, table: TableId, loc: u32, root: u32, flags: u32) -> u32 {
        debug_assert!(self.current != NONE, "open with no scope entered");
        debug_assert_eq!(self.layers.len(), self.opens.len());
        let index = self.layers.len() as u32;
        let scope = &mut self.scopes[self.current as usize];
        self.layers.push(Layer {
            table,
            mark: self.binders.len(),
            older: scope.opens,
        });
        scope.opens = index;
        self.opens.push(Open {
            loc,
            root,
            shadowed: NONE,
            flags,
        });
        index
    }

    /// At most floor(log2 n) + 1 steps (one a comparison) for a table of n
    /// members, no allocation: the first row of `key` in `table`, as an
    /// index into `members` or `imported_members`, or `None`.
    pub fn search(&self, table: TableId, key: Key) -> Option<u32> {
        let (pool, first) = self.rows(table);
        let rows = &pool[first..];
        // The lower bound of `key`: `hi` is always a row whose key is at
        // least `key` (or the end), and `hit` says whether the comparison
        // that last moved `hi` saw `key` itself, so the bound is known to
        // hold the key without one more comparison.
        let (mut lo, mut hi, mut hit) = (0usize, rows.len(), false);
        while lo < hi {
            #[cfg(test)]
            super::steps::tick();
            let mid = lo + (hi - lo) / 2;
            match rows[mid].key.cmp(&key.0) {
                std::cmp::Ordering::Less => lo = mid + 1,
                order => {
                    hi = mid;
                    hit = order == std::cmp::Ordering::Equal;
                }
            }
        }
        hit.then_some((first + lo) as u32)
    }

    /// O(1): the row `search` or a [`Resolved`] names, from the pool
    /// `table` selects.
    pub fn member(&self, table: TableId, row: u32) -> Member {
        if table.0 & IMPORTED != 0 {
            self.imported_members[row as usize]
        } else {
            self.members[row as usize]
        }
    }

    /// The lookup of `key` among the binder `head` (or [`NONE`]) and the
    /// layers from `layer` through `older`: one [`Scopes::search`] per
    /// layer whose mark is above `head` (every layer when `head` is
    /// [`NONE`]), innermost first, stopping at the first that has the key;
    /// no other step, no write. A layer's mark is never above a younger
    /// layer's, so the first layer not above `head` ends the walk
    /// (compiler/ml/env.ml:272-289: `current` before `components` before
    /// `next`).
    fn find_from(&self, key: Key, head: u32, mut layer: u32) -> Option<Found> {
        while layer != NONE {
            let row = self.layers[layer as usize];
            if head != NONE && row.mark <= head {
                break;
            }
            if let Some(member) = self.search(row.table, key) {
                return Some(Found {
                    item: self.resolved(row.table, member),
                    layer,
                });
            }
            layer = row.older;
        }
        (head != NONE).then_some(Found {
            item: Resolved::binder(Binder(head)),
            layer: NONE,
        })
    }

    /// O(1), no step: what row `row` of `table` names: its binder for a
    /// local table, the row itself for an imported one.
    fn resolved(&self, table: TableId, row: u32) -> Resolved {
        if table.0 & IMPORTED != 0 {
            Resolved::import(row)
        } else {
            Resolved::binder(Binder(self.members[row as usize].target))
        }
    }

    /// O(n log n) comparisons for the n rows of `members` from `first` on,
    /// no step: sort that run by key with a stable sort (rows of one key
    /// keep the order they were appended in) and push it as a local
    /// [`Table`].
    fn close_table(&mut self, first: u32) -> TableId {
        self.members[first as usize..].sort_by_key(|member| member.key);
        let id = self.tables.len() as u32;
        debug_assert!(id < IMPORTED, "more than 2^31 local tables");
        self.tables.push(Table {
            first,
            len: self.members.len() as u32 - first,
            unit: NONE,
        });
        TableId(id)
    }

    /// O(1), no step: the pool `table` lives in, cut at the table's last
    /// row, and the index of the table's first row in it.
    fn rows(&self, table: TableId) -> (&[Member], usize) {
        let (pool, row) = if table.0 & IMPORTED != 0 {
            (
                &self.imported_members,
                self.imported_tables[(table.0 & !IMPORTED) as usize],
            )
        } else {
            (&self.members, self.tables[table.0 as usize])
        };
        let first = row.first as usize;
        (&pool[..first + row.len as usize], first)
    }

    /// The binding a lookup of `key` finds (`IdTbl.find_name`,
    /// compiler/ml/env.ml:272-289): the innermost of the head binder and
    /// the members of the visible layers. 1 step for the head, then one
    /// [`Scopes::search`] per layer younger than the head binder, innermost
    /// first, stopping at the first that has the key. With no head binder
    /// every visible layer is probed. No allocation, no write.
    pub fn find(&self, key: Key) -> Option<Found> {
        let head = self.head(key);
        self.find_from(key, head, self.scopes[self.current as usize].opens)
    }

    /// What `layer`'s member hides: the lookup of `key` restricted to
    /// everything older than `layer` (`find_name false name next`,
    /// compiler/ml/env.ml:284-287). Same cost as [`Scopes::find`] from the
    /// layer's `older`, with the head binder counted only when below the
    /// layer's mark (else its `previous` chain is followed, 1 step a
    /// binder).
    pub fn find_below(&self, key: Key, layer: u32) -> Option<Found> {
        let row = self.layers[layer as usize];
        let mut head = self.head(key);
        // The bindings made after the open are `current` of the opened
        // table, not part of `next`.
        while head != NONE && head >= row.mark {
            #[cfg(test)]
            super::steps::tick();
            head = self.binders.previous[head as usize];
        }
        self.find_from(key, head, row.older)
    }

    /// Every candidate of `key`, innermost first, appended to `out`
    /// (`TycompTbl.find_all`, compiler/ml/env.ml:202-213): the binders of
    /// the key through `previous` and the members of every visible layer,
    /// merged by age (a layer comes before the binders below its mark). 1
    /// step a candidate, plus one [`Scopes::search`] per visible layer. No
    /// allocation when `out` has capacity.
    pub fn candidates(&self, key: Key, out: &mut Vec<Found>) {
        // No head step: every binder of the chain is a candidate and counted
        // as one.
        let mut binder = self.heads.get(key.0 as usize).copied().unwrap_or(NONE);
        let mut layer = self.scopes[self.current as usize].opens;
        while binder != NONE || layer != NONE {
            let row = match layer {
                NONE => None,
                layer => Some(self.layers[layer as usize]),
            };
            match row {
                // The layer is younger than the binder: its members first
                // (`components` before `next`, compiler/ml/env.ml:207-213).
                Some(row) if binder == NONE || row.mark > binder => {
                    if let Some(first) = self.search(row.table, key) {
                        let (pool, _) = self.rows(row.table);
                        for member in first..pool.len() as u32 {
                            if pool[member as usize].key != key.0 {
                                break;
                            }
                            #[cfg(test)]
                            super::steps::tick();
                            out.push(Found {
                                item: self.resolved(row.table, member),
                                layer,
                            });
                        }
                    }
                    layer = row.older;
                }
                // `current` before the opened layer: the binder is younger.
                _ => {
                    #[cfg(test)]
                    super::steps::tick();
                    out.push(Found {
                        item: Resolved::binder(Binder(binder)),
                        layer: NONE,
                    });
                    binder = self.binders.previous[binder as usize];
                }
            }
        }
    }

    // ----- R4d: dependencies as member tables -----

    /// Amortized O(1): register a unit this worker has not seen, with
    /// `Segment::children.len()` empty slots in `table_index`, and point
    /// `unit_heads[name]` at it. Returns its index. One `Arc` clone per
    /// worker and unit, never per lookup. Panics at 2^24 units.
    pub fn add_unit(&mut self, name: Name, segment: Arc<Segment>) -> u32 {
        let unit = self.units.len() as u32;
        assert!(unit <= UNIT_MASK, "more than 2^24 units");
        let tables = self.table_index.len() as u32;
        let slots = self.table_index.len() + segment.children.len();
        self.table_index.resize(slots, NONE);
        self.units.push(UnitSlot {
            segment,
            name,
            tables,
        });
        self.grow_unit_heads(name);
        self.unit_heads[name.0 as usize] = unit;
        unit
    }

    /// Amortized O(1), no step: make `unit_heads` cover `name`, growing it
    /// to the name table's size with [`NONE`] (every name is below it).
    fn grow_unit_heads(&mut self, name: Name) {
        if name.0 as usize >= self.unit_heads.len() {
            self.unit_heads.resize(self.names.len() as usize, NONE);
        }
    }

    /// 1 step, one load when the name was asked before (from R4g on, one
    /// more step for the read it logs); otherwise one call
    /// of `source` and [`Scopes::add_unit`], or `MISSING` recorded. `None`
    /// when no unit has the name (`find_pers_struct`, compiler/ml/env.ml:
    /// 646-691).
    pub fn unit_by_name(&mut self, name: Name, source: &mut dyn UnitSource) -> Option<u32> {
        self.grow_unit_heads(name);
        match self.unit_heads[name.0 as usize] {
            NONE => match source.segment(self.names.text(name)) {
                Some(segment) => Some(self.add_unit(name, segment)),
                None => {
                    self.unit_heads[name.0 as usize] = MISSING;
                    None
                }
            },
            known => {
                #[cfg(test)]
                super::steps::tick();
                (known != MISSING).then_some(known)
            }
        }
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
        let slot = (self.units[unit as usize].tables + signature) as usize;
        let known = self.table_index[slot];
        if known != NONE {
            #[cfg(test)]
            super::steps::tick();
            return TableId(known | IMPORTED);
        }
        let Scopes {
            names,
            units,
            imported_tables,
            imported_members,
            table_index,
            ..
        } = self;
        let segment = &*units[unit as usize].segment;
        let range = segment.children[signature as usize];
        let first = imported_members.len() as u32;
        imported_members.reserve(range.len as usize);
        for index in range.start..range.start + range.len {
            #[cfg(test)]
            super::steps::tick();
            let item = segment.items[index as usize];
            let name = names.intern(segment_string(segment, item.name));
            // `ExportKind`'s discriminants are `Namespace`'s.
            imported_members.push(Member {
                key: name.0 << 3 | item.kind as u32,
                target: index,
                origin: unit,
            });
        }
        // Stable: items of one key keep the segment's order.
        imported_members[first as usize..].sort_by_key(|member| member.key);
        let id = imported_tables.len() as u32;
        debug_assert!(id < IMPORTED, "more than 2^31 imported tables");
        imported_tables.push(Table {
            first,
            len: range.len,
            unit,
        });
        table_index[slot] = id;
        TableId(id | IMPORTED)
    }

    /// O(1), three loads: the segment and export item a row of
    /// `imported_members` names.
    pub fn item(&self, row: u32) -> (&Segment, &ExportItem) {
        let member = self.imported_members[row as usize];
        let segment = &*self.units[(member.origin & UNIT_MASK) as usize].segment;
        (segment, &segment.items[member.target as usize])
    }
}

/// O(len), no allocation: the text of string `index` of a segment's string
/// pool. Names are written from Rust strings, so the bytes are UTF-8.
fn segment_string(segment: &Segment, index: u32) -> &str {
    let range = segment.signature.strings[index as usize];
    let bytes = &segment.signature.bytes[range.start as usize..(range.start + range.len) as usize];
    std::str::from_utf8(bytes).expect("a segment string is UTF-8")
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
