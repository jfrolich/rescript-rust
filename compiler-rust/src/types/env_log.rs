//! The environment as a version log (docs/CHECKER_REDESIGN.md H.2.7, as
//! amended by H.2.10). Built beside the persistent tables of `Env` and
//! used as the oracle shadow when `RESCRIPT_ENV_SHADOW=1`.
//!
//! # Shape
//!
//! An [`EnvLog`] is an append-only tree of [`Entry`]s. A version ([`Tip`]) is
//! an entry index; an environment is the entries on the path from its version
//! to the root, then what the log's base environment sees. One path of the
//! tree, the *current path*, is indexed: `visible` holds the innermost entry
//! of every key on it. [`LogEnv`] is the handle with the method signatures of
//! today's `Env`: a reference-counted log and a version.
//!
//! # Ownership (H.2.10, decision 1)
//!
//! Entries and payloads live in [`Pool`]s: append-only, addressed by `u32`,
//! and *address-stable*, so a pushed element never moves. A lookup therefore
//! returns a plain reference that borrows the `LogEnv` it was asked through,
//! exactly as `Env` does today, and stays valid while any other handle of the
//! same log is extended. Only the movable path index sits in a `RefCell`; no
//! reference into it is ever returned.
//!
//! # Costs
//!
//! Every operation states its cost in its doc comment, in the units
//! [`Steps`] counts, and a test pins each. "Probe" is one hash-table probe.
//! A pool read is two dependent loads after an index computation; a pool
//! push is amortised O(1) and allocates only when a chunk fills.
//!
//! No result depends on the iteration order of a hash table built here.
//! `iter_values` yields the names of an *opened* table in that table's own
//! order, as `Env::iter_values` does; its one caller does not read the order.

use super::*;
use std::cell::{Cell, OnceCell};
use std::rc::Weak;

// ============================================================================
// Address-stable pools
// ============================================================================

const POOL_FIRST_BITS: u32 = 6;
const POOL_CHUNKS: usize = 26;

/// An append-only vector whose elements never move: chunk `c` holds
/// `64 << c` elements, so 26 chunks cover every `u32` index.
///
/// `push` takes `&self`, which is what lets a shared log grow while
/// references into it are alive. It is safe Rust: a slot is a `OnceCell`,
/// written once. `OnceCell<Arc<T>>` and `OnceCell<Entry>` use a niche, so a
/// slot is as large as its element.
pub(super) struct Pool<T> {
    chunks: [OnceCell<Box<[OnceCell<T>]>>; POOL_CHUNKS],
    len: Cell<u32>,
}

impl<T> Default for Pool<T> {
    fn default() -> Self {
        Pool {
            chunks: std::array::from_fn(|_| OnceCell::new()),
            len: Cell::new(0),
        }
    }
}

impl<T> Pool<T> {
    #[inline]
    fn locate(index: u32) -> (usize, usize) {
        let n = u64::from(index) + (1 << POOL_FIRST_BITS);
        let chunk = 63 - n.leading_zeros() - POOL_FIRST_BITS;
        (
            chunk as usize,
            (n - (1u64 << (chunk + POOL_FIRST_BITS))) as usize,
        )
    }

    /// Amortised O(1); allocates one chunk when the previous one is full.
    pub(super) fn push(&self, value: T) -> u32 {
        let index = self.len.get();
        let (chunk, offset) = Self::locate(index);
        let slots = self.chunks[chunk].get_or_init(|| {
            (0..(1usize << (chunk as u32 + POOL_FIRST_BITS)))
                .map(|_| OnceCell::new())
                .collect()
        });
        assert!(slots[offset].set(value).is_ok(), "pool slot written twice");
        self.len
            .set(index.checked_add(1).expect("environment pool overflow"));
        index
    }

    /// O(1): an index computation and two dependent loads.
    #[inline]
    pub(super) fn get(&self, index: u32) -> &T {
        let (chunk, offset) = Self::locate(index);
        self.chunks[chunk]
            .get()
            .and_then(|slots| slots[offset].get())
            .expect("environment pool index out of range")
    }

    pub(super) fn len(&self) -> u32 {
        self.len.get()
    }
}

// ============================================================================
// Entries
// ============================================================================

/// A version of an environment: the index of the entry that made it, or
/// [`Tip::ROOT`] for the environment a log starts from. `Copy`: retaining a
/// version costs nothing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Tip(u32);

impl Tip {
    pub(super) const ROOT: Self = Self(0);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Kind {
    Value,
    /// `update_value_type_by_name`: stands in for the binding it replaced.
    ValueOverride,
    Type,
    /// The declaration and the component thunk, at the same payload index.
    Module,
    Modtype,
    Constructor,
    Label,
    /// The label array of a local record type, or its removal.
    Family,
    FunctorArg,
    ImplicitRoot,
    /// Keyed by path, not by name.
    Constraint,
    Open,
    Flags,
    GadtLevel,
}

/// The name spaces of local bindings: what `visible` is keyed by.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
enum Ns {
    Value,
    Type,
    Module,
    Modtype,
    Constructor,
    Label,
    Family,
    FunctorArg,
    ImplicitRoot,
}

impl Ns {
    const COUNT: usize = Ns::ImplicitRoot as usize + 1;
}

impl Kind {
    fn ns(self) -> Option<Ns> {
        Some(match self {
            Kind::Value | Kind::ValueOverride => Ns::Value,
            Kind::Type => Ns::Type,
            Kind::Module => Ns::Module,
            Kind::Modtype => Ns::Modtype,
            Kind::Constructor => Ns::Constructor,
            Kind::Label => Ns::Label,
            Kind::Family => Ns::Family,
            Kind::FunctorArg => Ns::FunctorArg,
            Kind::ImplicitRoot => Ns::ImplicitRoot,
            Kind::Constraint | Kind::Open | Kind::Flags | Kind::GadtLevel => return None,
        })
    }

    /// The kinds whose `Env` operation calls `bump_scope` today.
    fn changes_scope(self) -> bool {
        matches!(
            self,
            Kind::Type
                | Kind::Module
                | Kind::Modtype
                | Kind::ImplicitRoot
                | Kind::Constraint
                | Kind::Open
                | Kind::GadtLevel
        )
    }
}

/// The tables of an opened signature. An open is a layer of a table only
/// when its table is not empty (`IdTbl::add_open_layer_table`); the open's
/// `mask` has the bit of each table that is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Table {
    Values,
    Types,
    Modules,
    Components,
    Modtypes,
    Constructors,
    Labels,
}

impl Table {
    fn bit(self) -> u8 {
        1 << self as u8
    }

    fn ns(self) -> Ns {
        match self {
            Table::Values => Ns::Value,
            Table::Types => Ns::Type,
            // Local modules and their components are one entry.
            Table::Modules | Table::Components => Ns::Module,
            Table::Modtypes => Ns::Modtype,
            Table::Constructors => Ns::Constructor,
            Table::Labels => Ns::Label,
        }
    }
}

const BIT_IN_SIGNATURE: u8 = 1;
const BIT_IMPLICIT_COERCION: u8 = 2;
const BIT_CONSTRAINTS: u8 = 4;

/// One extension of an environment. Never written after it is pushed.
#[derive(Clone, Copy, Debug)]
struct Entry {
    /// The version this entry extends. Always smaller than the entry's own.
    parent: Tip,
    /// The entry `visible` held for this entry's key in `parent`.
    shadows: Tip,
    /// The nearest `Open` entry at or above this one.
    prev_open: Tip,
    /// The nearest scope-changing entry at or above this one.
    scope_ver: Tip,
    /// Index into the payload pool of `kind`.
    item: u32,
    kind: Kind,
    /// `BIT_*`, inherited from `parent`.
    bits: u8,
    id: Ident,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Key {
    name: Name,
    ns: Ns,
}

/// Where a name was found.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum At {
    /// A local binding: the entry.
    Local(Tip),
    /// Through an open: the `Open` entry.
    Open(Tip),
}

struct OpenRec {
    layers: OpenedLayers,
    root: Arc<Path>,
    slot: Option<u32>,
    /// `Table::bit` of each non-empty table.
    mask: u8,
    /// The nearest open above this one.
    older: OpenAt,
}

/// An open: its entry, for comparing positions without a read, and its
/// record in the pool of opens. `at` is `ROOT` for "no open".
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct OpenAt {
    at: Tip,
    rec: u32,
}

impl OpenRec {
    fn has(&self, table: Table, name: Name) -> bool {
        let layers = &self.layers;
        match table {
            Table::Values => layers.values.contains_key(&name),
            Table::Types => layers.types.contains_key(&name),
            Table::Modules => layers.modules.contains_key(&name),
            Table::Components => layers.module_components.contains_key(&name),
            Table::Modtypes => layers.modtypes.contains_key(&name),
            Table::Constructors => layers.constrs.contains_key(&name),
            Table::Labels => layers.labels.contains_key(&name),
        }
    }
}

#[derive(Clone, Copy)]
struct OverrideRec {
    /// The replacing description, in the value pool.
    value: u32,
    /// The log and place of the binding it stands in for.
    target_log: u64,
    target: At,
}

/// The environment a module's components are built in: the version before
/// the module's binding (H.2.10, decision 2). It does not keep its log
/// alive; the log is kept by the `LogEnv` handles of its compilation, or by
/// the component table that started it.
#[derive(Clone, Debug)]
pub(super) struct EnvSeed {
    log: Weak<EnvLog>,
    tip: Tip,
}

impl EnvSeed {
    /// The seed as an environment, or `None` when its log is gone. One
    /// reference-count update; called once per forced thunk.
    pub(super) fn env(&self) -> Option<LogEnv> {
        Some(LogEnv {
            log: self.log.upgrade()?,
            tip: self.tip,
        })
    }
}

/// The component thunk of a local module binding, log-native: what
/// `StoredModuleComponents` holds, with an [`EnvSeed`] where that holds an
/// `Env`.
#[derive(Debug)]
pub(super) struct LogComponents {
    pub(super) seed: EnvSeed,
    pub(super) access_path: Path,
    pub(super) module_decl: ModuleDeclaration,
    pub(super) parent_context: Option<(Path, Arc<Signature>)>,
}

/// Work counters, in the units the cost statements use.
#[derive(Default, Debug)]
pub(super) struct Steps {
    /// Probes of `visible` (or of the constraint index).
    pub(super) probes: Cell<u64>,
    /// `shadows` links followed.
    pub(super) chain: Cell<u64>,
    /// Probes of an opened table.
    pub(super) open_probes: Cell<u64>,
    /// Entries passed walking from a `make_tip` target to the current path.
    pub(super) ancestors: Cell<u64>,
    /// Entries undone or redone by `make_tip`.
    pub(super) moved: Cell<u64>,
    /// `make_tip` calls that moved the path.
    pub(super) moves: Cell<u64>,
    /// Entries pushed.
    pub(super) appended: Cell<u64>,
    /// Entries visited by a walk of a whole path (iteration, folds).
    pub(super) walked: Cell<u64>,
}

thread_local! {
    /// Set by one test to show that the property test catches a wrong
    /// rule: an open then forgets the opens made before it. Read when an
    /// open is added, not on a lookup. Goes away at H.2.8 step 6.
    pub(super) static INJECT_FAULT: Cell<bool> = const { Cell::new(false) };
}

fn bump(counter: &Cell<u64>) {
    counter.set(counter.get() + 1);
}

/// The innermost entry of each key on the current path: one table per name
/// space, keyed by the name alone, whose hash is precomputed.
#[derive(Default)]
struct Visible {
    spaces: [NameTable; Ns::COUNT],
}

/// A name is hashed when it is interned: the table uses that hash as is.
#[derive(Default)]
struct NameHasher(u64);

impl std::hash::Hasher for NameHasher {
    fn write(&mut self, _: &[u8]) {
        unreachable!("a name hashes as one word");
    }

    #[inline]
    fn write_u64(&mut self, hash: u64) {
        self.0 = hash;
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

type NameTable = std::collections::HashMap<Name, Tip, std::hash::BuildHasherDefault<NameHasher>>;

impl Visible {
    #[inline]
    fn get(&self, key: &Key) -> Option<Tip> {
        self.spaces[key.ns as usize].get(&key.name).copied()
    }

    fn insert(&mut self, key: Key, tip: Tip) -> Option<Tip> {
        self.spaces[key.ns as usize].insert(key.name, tip)
    }

    fn remove(&mut self, key: &Key) {
        self.spaces[key.ns as usize].remove(&key.name);
    }

    fn len(&self) -> usize {
        self.spaces.iter().map(|space| space.len()).sum()
    }
}

/// The index of the current path. Nothing here is ever borrowed out.
#[derive(Default)]
struct PathIndex {
    tip: Tip,
    /// The newest open the tip sees: saves reading the tip's entry on
    /// every lookup at the tip.
    tip_open: OpenAt,
    visible: Visible,
    visible_constraints: HashMap<Path, Tip>,
    /// One bit per entry: whether it is on the current path.
    on_path: Vec<u64>,
    scope_caches: HashMap<Tip, Rc<ScopeCaches>>,
}

impl PathIndex {
    #[inline]
    fn is_on_path(&self, tip: Tip) -> bool {
        tip == Tip::ROOT
            || self
                .on_path
                .get((tip.0 >> 6) as usize)
                .is_some_and(|word| word & (1 << (tip.0 & 63)) != 0)
    }

    fn set_on_path(&mut self, tip: Tip, on: bool) {
        let word = (tip.0 >> 6) as usize;
        if word >= self.on_path.len() {
            self.on_path.resize(word + 1, 0);
        }
        if on {
            self.on_path[word] |= 1 << (tip.0 & 63);
        } else {
            self.on_path[word] &= !(1 << (tip.0 & 63));
        }
    }
}

/// An append-only tree of environment versions with one indexed path.
pub(super) struct EnvLog {
    /// Unique per log; half of an environment's identity.
    serial: u64,
    /// What version `ROOT` of this log sees.
    base: Option<LogEnv>,
    /// `BIT_*` of `base`.
    root_bits: u8,
    /// A frozen log is never extended (H.2.9, invariant 8).
    frozen: Cell<bool>,
    index: RefCell<PathIndex>,
    entries: Pool<Entry>,
    values: Pool<Arc<ValueDescription>>,
    overrides: Pool<OverrideRec>,
    types: Pool<Arc<TypeDeclaration>>,
    modules: Pool<Arc<ModuleDeclaration>>,
    /// Parallel to `modules`.
    components: Pool<Rc<LogComponents>>,
    modtypes: Pool<Arc<ModtypeDeclaration>>,
    constrs: Pool<Arc<ConstructorDescription>>,
    labels: Pool<Arc<LabelDescription>>,
    families: Pool<Option<super::super::decl::LabelArrayRef>>,
    constraints: Pool<(Path, Arc<TypeDeclaration>)>,
    opens: Pool<OpenRec>,
    pub(super) steps: Steps,
}

/// Where a name was found, with what is already read of it.
#[derive(Clone, Copy)]
enum Place<'a> {
    Local(Tip, &'a Entry),
    Open(Tip, &'a OpenRec),
}

/// A name found by [`EnvLog::resolve`].
struct Found<'a> {
    log: &'a EnvLog,
    place: Place<'a>,
    /// The description `update_value_type_by_name` put in its place.
    replaced: Option<&'a Arc<ValueDescription>>,
}

/// A table of `IdTbl` shape: one binding per name in an opened table.
trait IdSpace {
    type T;
    const TABLE: Table;
    fn opened(layers: &OpenedLayers) -> &OpenedMap<(Ident, Self::T, i32)>;
    fn local<'a>(log: &'a EnvLog, entry: &Entry) -> &'a Self::T;
    fn replaced<'a>(_found: &Found<'a>) -> Option<&'a Self::T> {
        None
    }
}

struct Values;
struct Types;
struct Modules;
struct Modtypes;

impl IdSpace for Values {
    type T = Arc<ValueDescription>;
    const TABLE: Table = Table::Values;
    fn opened(layers: &OpenedLayers) -> &OpenedMap<(Ident, Self::T, i32)> {
        &layers.values
    }
    fn local<'a>(log: &'a EnvLog, entry: &Entry) -> &'a Self::T {
        match entry.kind {
            Kind::ValueOverride => log.values.get(log.overrides.get(entry.item).value),
            _ => log.values.get(entry.item),
        }
    }
    fn replaced<'a>(found: &Found<'a>) -> Option<&'a Self::T> {
        found.replaced
    }
}

impl IdSpace for Types {
    type T = Arc<TypeDeclaration>;
    const TABLE: Table = Table::Types;
    fn opened(layers: &OpenedLayers) -> &OpenedMap<(Ident, Self::T, i32)> {
        &layers.types
    }
    fn local<'a>(log: &'a EnvLog, entry: &Entry) -> &'a Self::T {
        log.types.get(entry.item)
    }
}

impl IdSpace for Modules {
    type T = Arc<ModuleDeclaration>;
    const TABLE: Table = Table::Modules;
    fn opened(layers: &OpenedLayers) -> &OpenedMap<(Ident, Self::T, i32)> {
        &layers.modules
    }
    fn local<'a>(log: &'a EnvLog, entry: &Entry) -> &'a Self::T {
        log.modules.get(entry.item)
    }
}

impl IdSpace for Modtypes {
    type T = Arc<ModtypeDeclaration>;
    const TABLE: Table = Table::Modtypes;
    fn opened(layers: &OpenedLayers) -> &OpenedMap<(Ident, Self::T, i32)> {
        &layers.modtypes
    }
    fn local<'a>(log: &'a EnvLog, entry: &Entry) -> &'a Self::T {
        log.modtypes.get(entry.item)
    }
}

/// A table of `TycompTbl` shape: every binding of a name is a candidate.
trait CompSpace {
    type T;
    const TABLE: Table;
    fn opened(layers: &OpenedLayers) -> &OpenedMap<Candidates<Self::T>>;
    fn local(log: &EnvLog, item: u32) -> &Arc<Self::T>;
}

struct Constructors;
struct Labels;

impl CompSpace for Constructors {
    type T = ConstructorDescription;
    const TABLE: Table = Table::Constructors;
    fn opened(layers: &OpenedLayers) -> &OpenedMap<Candidates<Self::T>> {
        &layers.constrs
    }
    fn local(log: &EnvLog, item: u32) -> &Arc<Self::T> {
        log.constrs.get(item)
    }
}

impl CompSpace for Labels {
    type T = LabelDescription;
    const TABLE: Table = Table::Labels;
    fn opened(layers: &OpenedLayers) -> &OpenedMap<Candidates<Self::T>> {
        &layers.labels
    }
    fn local(log: &EnvLog, item: u32) -> &Arc<Self::T> {
        log.labels.get(item)
    }
}

/// A name found in a table with payloads: its identifier, its payload and,
/// when it was found through an open, that open and the position.
type Hit<'a, T> = (&'a Ident, &'a T, Option<(&'a OpenRec, i32)>);

/// A candidate block of an open with a slot: `(start, end, slot)`.
type Blocks = smallvec::SmallVec<[(usize, usize, u32); 4]>;

fn ident_matches(bound: &Ident, wanted: &Ident) -> bool {
    // `IdTbl::find_current_by_ident`: a stamp-0 identifier matches a
    // persistent binding of its name. The names are equal: both come from
    // the chain of one key.
    if wanted.stamp() == 0 {
        bound.is_persistent()
    } else {
        bound.same(wanted)
    }
}

impl EnvLog {
    fn new(base: Option<LogEnv>) -> Self {
        let root_bits = base.as_ref().map_or(0, |base| base.log.bits_at(base.tip));
        EnvLog {
            serial: next_env_id(),
            base,
            root_bits,
            frozen: Cell::new(false),
            index: RefCell::default(),
            entries: Pool::default(),
            values: Pool::default(),
            overrides: Pool::default(),
            types: Pool::default(),
            modules: Pool::default(),
            components: Pool::default(),
            modtypes: Pool::default(),
            constrs: Pool::default(),
            labels: Pool::default(),
            families: Pool::default(),
            constraints: Pool::default(),
            opens: Pool::default(),
            steps: Steps::default(),
        }
    }

    #[inline]
    fn entry(&self, tip: Tip) -> &Entry {
        self.entries.get(tip.0 - 1)
    }

    fn bits_at(&self, tip: Tip) -> u8 {
        if tip == Tip::ROOT {
            self.root_bits
        } else {
            self.entry(tip).bits
        }
    }

    /// The newest open `tip` sees, read from the entries.
    fn open_at(&self, tip: Tip) -> OpenAt {
        if tip == Tip::ROOT {
            return OpenAt::default();
        }
        let at = self.entry(tip).prev_open;
        if at == Tip::ROOT {
            return OpenAt::default();
        }
        OpenAt {
            at,
            rec: self.entry(at).item,
        }
    }

    fn open_rec(&self, open: Tip) -> &OpenRec {
        self.opens.get(self.entry(open).item)
    }

    fn base(&self) -> Option<(&EnvLog, Tip)> {
        self.base.as_ref().map(|base| (&*base.log, base.tip))
    }

    /// The key of `entry` in the path index, if it has one.
    fn unindex(&self, index: &mut PathIndex, entry: &Entry) {
        if let Some(ns) = entry.kind.ns() {
            let key = Key {
                name: entry.id.name_atom(),
                ns,
            };
            if entry.shadows == Tip::ROOT {
                index.visible.remove(&key);
            } else {
                index.visible.insert(key, entry.shadows);
            }
        } else if entry.kind == Kind::Constraint {
            let path = self.constraints.get(entry.item).0;
            if entry.shadows == Tip::ROOT {
                index.visible_constraints.remove(&path);
            } else {
                index.visible_constraints.insert(path, entry.shadows);
            }
        }
    }

    fn reindex(&self, index: &mut PathIndex, tip: Tip, entry: &Entry) {
        if let Some(ns) = entry.kind.ns() {
            index.visible.insert(
                Key {
                    name: entry.id.name_atom(),
                    ns,
                },
                tip,
            );
        } else if entry.kind == Kind::Constraint {
            index
                .visible_constraints
                .insert(self.constraints.get(entry.item).0, tip);
        }
    }

    /// Make `target` the tip of the current path.
    ///
    /// Cost: nothing when `target` is the tip. Otherwise `a + u + a` steps,
    /// where `a` is the number of entries from `target` up to the first
    /// entry on the current path (`ancestors`, then redone) and `u` the
    /// number from the old tip up to that entry (undone): the distance
    /// between the two versions through their common ancestor, whatever the
    /// size of the log. An `Open` entry is one step: opened names are not in
    /// the index, so moving across an open of `k` names does not cost `k`.
    fn make_tip(&self, index: &mut PathIndex, target: Tip) {
        if target == index.tip {
            return;
        }
        bump(&self.steps.moves);
        let mut redo: smallvec::SmallVec<[Tip; 16]> = smallvec::SmallVec::new();
        let mut ancestor = target;
        while !index.is_on_path(ancestor) {
            bump(&self.steps.ancestors);
            redo.push(ancestor);
            ancestor = self.entry(ancestor).parent;
        }
        while index.tip != ancestor {
            let old = index.tip;
            let entry = self.entry(old);
            self.unindex(index, entry);
            index.set_on_path(old, false);
            index.tip = entry.parent;
            bump(&self.steps.moved);
        }
        for &tip in redo.iter().rev() {
            self.reindex(index, tip, self.entry(tip));
            index.set_on_path(tip, true);
            bump(&self.steps.moved);
        }
        index.tip = target;
        index.tip_open = self.open_at(target);
        self.check_path(index);
    }

    /// Append an entry to `parent`.
    ///
    /// Cost: `make_tip(parent)`, then one probe for a keyed entry and one
    /// push. At the tip that is one probe: expected O(1), amortised.
    fn push(&self, parent: Tip, kind: Kind, id: Ident, item: u32) -> Tip {
        assert!(
            !self.frozen.get(),
            "a frozen environment log is never extended"
        );
        let mut index = self.index.borrow_mut();
        self.make_tip(&mut index, parent);
        let tip = Tip(self.entries.len() + 1);
        let shadows = if let Some(ns) = kind.ns() {
            bump(&self.steps.probes);
            let key = Key {
                name: id.name_atom(),
                ns,
            };
            index.visible.insert(key, tip)
        } else if kind == Kind::Constraint {
            bump(&self.steps.probes);
            index
                .visible_constraints
                .insert(self.constraints.get(item).0, tip)
        } else {
            None
        }
        .unwrap_or(Tip::ROOT);
        let (mut prev_open, mut scope_ver, mut bits) = if parent == Tip::ROOT {
            (Tip::ROOT, Tip::ROOT, self.root_bits)
        } else {
            let parent = self.entry(parent);
            (parent.prev_open, parent.scope_ver, parent.bits)
        };
        match kind {
            Kind::Open => prev_open = tip,
            Kind::Constraint => bits |= BIT_CONSTRAINTS,
            Kind::Flags => bits |= item as u8,
            _ => {}
        }
        if kind.changes_scope() {
            scope_ver = tip;
        }
        self.entries.push(Entry {
            parent,
            shadows,
            prev_open,
            scope_ver,
            item,
            kind,
            bits,
            id,
        });
        index.set_on_path(tip, true);
        index.tip = tip;
        if kind == Kind::Open {
            index.tip_open = OpenAt { at: tip, rec: item };
        }
        bump(&self.steps.appended);
        self.check_path(&index);
        tip
    }

    /// The innermost local entry of `key` that `tip` sees in this log, and
    /// the newest open `tip` sees.
    ///
    /// Cost: one probe when `tip` is the tip of the current path; one probe
    /// plus one `chain` step per newer binding of the same key when `tip` is
    /// an older version on the path; `make_tip(tip)` plus one probe when it
    /// is off the path. At the tip nothing but the index is read.
    #[inline]
    fn start(&self, tip: Tip, key: Key) -> (Tip, OpenAt) {
        if tip == Tip::ROOT {
            return (Tip::ROOT, OpenAt::default());
        }
        bump(&self.steps.probes);
        let probe = |index: &PathIndex| index.visible.get(&key).unwrap_or(Tip::ROOT);
        let index = self.index.borrow();
        if tip == index.tip {
            return (probe(&index), index.tip_open);
        }
        let mut head = if index.is_on_path(tip) {
            probe(&index)
        } else {
            drop(index);
            let mut index = self.index.borrow_mut();
            self.make_tip(&mut index, tip);
            return (probe(&index), index.tip_open);
        };
        while head > tip {
            bump(&self.steps.chain);
            head = self.entry(head).shadows;
        }
        (head, self.open_at(tip))
    }

    /// `start`, for the keys opens do not bind.
    fn head(&self, tip: Tip, key: Key) -> Tip {
        self.start(tip, key).0
    }

    /// `IdTbl::find_name`: the innermost binding of `name` in `table`, local
    /// or through an open.
    ///
    /// Cost: `start`, plus one `open_probes` step per open that is newer
    /// than the local binding found, has a non-empty `table`, and is passed
    /// before the answer. An open without `table` costs one pool read. When
    /// nothing is found here, the same in the base log.
    fn resolve(&self, tip: Tip, table: Table, name: Name) -> Option<Found<'_>> {
        let (head, mut open) = self.start(
            tip,
            Key {
                name,
                ns: table.ns(),
            },
        );
        while open.at > head {
            let rec = self.opens.get(open.rec);
            if rec.mask & table.bit() != 0 {
                bump(&self.steps.open_probes);
                if rec.has(table, name) {
                    return Some(Found {
                        log: self,
                        place: Place::Open(open.at, rec),
                        replaced: None,
                    });
                }
            }
            open = rec.older;
        }
        if head == Tip::ROOT {
            let (base, base_tip) = self.base()?;
            return base.resolve(base_tip, table, name);
        }
        let entry = self.entry(head);
        if entry.kind == Kind::ValueOverride {
            let over = self.overrides.get(entry.item);
            if let At::Open(open) = over.target {
                // It stands in for a name found through an open: the result
                // is that open's, with the description replaced.
                let replaced = Some(self.values.get(over.value));
                if over.target_log == self.serial {
                    return Some(Found {
                        log: self,
                        place: Place::Open(open, self.open_rec(open)),
                        replaced,
                    });
                }
                let (base, base_tip) = self.base()?;
                let mut found = base.resolve(base_tip, table, name)?;
                found.replaced = replaced;
                return Some(found);
            }
        }
        Some(Found {
            log: self,
            place: Place::Local(head, entry),
            replaced: None,
        })
    }

    /// The identifier, payload and open (root and position) of a found name.
    fn payload<'a, S: IdSpace>(found: &Found<'a>, name: Name) -> Hit<'a, S::T> {
        match found.place {
            Place::Local(_, entry) => (&entry.id, S::local(found.log, entry), None),
            Place::Open(_, rec) => {
                let (id, value, pos) = S::opened(&rec.layers)
                    .get(&name)
                    .expect("a resolved open holds the name");
                (id, S::replaced(found).unwrap_or(value), Some((rec, *pos)))
            }
        }
    }

    /// `resolve` for a table with payloads, returning what was found: the
    /// identifier, the payload and, through an open, the open and the
    /// position. Same cost as `resolve`; the opened table is probed once,
    /// and nothing is built for the result.
    #[inline]
    fn find<S: IdSpace>(&self, tip: Tip, name: Name) -> Option<Hit<'_, S::T>> {
        let (head, mut open) = self.start(
            tip,
            Key {
                name,
                ns: S::TABLE.ns(),
            },
        );
        while open.at > head {
            let rec = self.opens.get(open.rec);
            if rec.mask & S::TABLE.bit() != 0 {
                bump(&self.steps.open_probes);
                if let Some((id, value, pos)) = S::opened(&rec.layers).get(&name) {
                    return Some((id, value, Some((rec, *pos))));
                }
            }
            open = rec.older;
        }
        if head == Tip::ROOT {
            let (base, base_tip) = self.base()?;
            return base.find::<S>(base_tip, name);
        }
        let entry = self.entry(head);
        if entry.kind == Kind::ValueOverride
            && matches!(self.overrides.get(entry.item).target, At::Open(_))
        {
            // A replaced opened name, rare: the general resolution.
            let found = self.resolve(tip, S::TABLE, name)?;
            return Some(Self::payload::<S>(&found, name));
        }
        Some((&entry.id, S::local(self, entry), None))
    }

    /// `find_by_name_with_path`. Cost: `find`, and the path's construction,
    /// as today.
    fn find_name<S: IdSpace>(&self, tip: Tip, name: Name) -> Option<(Path, &Ident, &S::T)> {
        let (id, value, open) = self.find::<S>(tip, name)?;
        let path = match open {
            // env.ml:293: `Pdot (root, name, pos)`.
            Some((rec, pos)) => Path::pdot_pos(*rec.root, name, pos),
            None => Path::pident(*id),
        };
        Some((path, id, value))
    }

    /// `find_by_name`, without building the path. Cost: `find`.
    fn find_name_value<S: IdSpace>(&self, tip: Tip, name: Name) -> Option<(&Ident, &S::T)> {
        let (id, value, _) = self.find::<S>(tip, name)?;
        Some((id, value))
    }

    /// `IdTbl::find_by_ident`: the innermost local binding of exactly `id`;
    /// opens are not consulted (H.2.4, item 3).
    ///
    /// Cost: `head`, then one `chain` step per local binding of the name
    /// examined, in this log and then in its base.
    fn find_ident(&self, tip: Tip, ns: Ns, id: &Ident) -> Option<(&EnvLog, &Entry)> {
        let mut head = self.head(
            tip,
            Key {
                name: id.name_atom(),
                ns,
            },
        );
        while head != Tip::ROOT {
            bump(&self.steps.chain);
            let entry = self.entry(head);
            let stands_for_open = entry.kind == Kind::ValueOverride
                && matches!(self.overrides.get(entry.item).target, At::Open(_));
            if !stands_for_open && ident_matches(&entry.id, id) {
                return Some((self, entry));
            }
            head = entry.shadows;
        }
        let (base, base_tip) = self.base()?;
        base.find_ident(base_tip, ns, id)
    }

    /// `TycompTbl::find_all`: every candidate of `name`, newest first; an
    /// open contributes its bucket in stored order.
    ///
    /// Cost: one probe, then one step per candidate and one `open_probes`
    /// step per open with a non-empty table that `tip` sees.
    fn candidates<'a, S: CompSpace>(
        &'a self,
        tip: Tip,
        name: Name,
        items: &mut Vec<(&'a S::T, OpenSlotMark<'a, S::T>)>,
        blocks: &mut Blocks,
    ) {
        let (mut head, mut open) = self.start(
            tip,
            Key {
                name,
                ns: S::TABLE.ns(),
            },
        );
        loop {
            if open.at > head {
                let rec = self.opens.get(open.rec);
                if rec.mask & S::TABLE.bit() != 0 {
                    bump(&self.steps.open_probes);
                    if let Some(bucket) = S::opened(&rec.layers).get(&name) {
                        let start = items.len();
                        items.extend(bucket.iter().map(|(_, value)| (value.as_ref(), None)));
                        if let Some(slot) = rec.slot {
                            blocks.push((start, items.len(), slot));
                        }
                    }
                }
                open = rec.older;
            } else if head != Tip::ROOT {
                bump(&self.steps.chain);
                let entry = self.entry(head);
                items.push((S::local(self, entry.item).as_ref(), None));
                head = entry.shadows;
            } else {
                break;
            }
        }
        if let Some((base, base_tip)) = self.base() {
            base.candidates::<S>(base_tip, name, items, blocks);
        }
    }

    fn all_candidates<S: CompSpace>(
        &self,
        tip: Tip,
        name: Name,
    ) -> Vec<(&S::T, OpenSlotMark<'_, S::T>)> {
        let mut items = Vec::new();
        let mut blocks = Blocks::new();
        self.candidates::<S>(tip, name, &mut items, &mut blocks);
        // An open's candidates hide the first candidate after their block.
        for (start, end, slot) in blocks {
            let hidden = items.get(end).map(|(value, _)| *value);
            for item in &mut items[start..end] {
                item.1 = Some((slot, hidden));
            }
        }
        items
    }

    /// `TycompTbl::find_by_name`: the first candidate, without collecting
    /// the others. Cost: one probe, plus one `open_probes` step per open
    /// with a non-empty table that is newer than the local binding and
    /// passed before the answer.
    fn first_candidate<S: CompSpace>(&self, tip: Tip, name: Name) -> Option<&S::T> {
        let (head, mut open) = self.start(
            tip,
            Key {
                name,
                ns: S::TABLE.ns(),
            },
        );
        while open.at > head {
            let rec = self.opens.get(open.rec);
            if rec.mask & S::TABLE.bit() != 0 {
                bump(&self.steps.open_probes);
                if let Some((_, value)) = S::opened(&rec.layers)
                    .get(&name)
                    .and_then(|bucket| bucket.first())
                {
                    return Some(value.as_ref());
                }
            }
            open = rec.older;
        }
        if head != Tip::ROOT {
            return Some(S::local(self, self.entry(head).item).as_ref());
        }
        let (base, base_tip) = self.base()?;
        base.first_candidate::<S>(base_tip, name)
    }

    /// Visit the entries of the path from `tip` to the root, newest first,
    /// then the base's; stop when `visit` returns `false`. One `walked` step
    /// per entry visited.
    fn walk<'a>(&'a self, tip: Tip, visit: &mut impl FnMut(&'a EnvLog, Tip, &'a Entry) -> bool) {
        let mut at = tip;
        while at != Tip::ROOT {
            bump(&self.steps.walked);
            let entry = self.entry(at);
            if !visit(self, at, entry) {
                return;
            }
            at = entry.parent;
        }
        if let Some((base, base_tip)) = self.base() {
            base.walk(base_tip, visit);
        }
    }

    /// H.2.9, invariant 2, recomputed from parent links for small logs.
    fn check_path(&self, index: &PathIndex) {
        if !cfg!(debug_assertions) || self.entries.len() > 96 {
            return;
        }
        let mut visible: HashMap<Key, Tip> = HashMap::default();
        let mut constraints: HashMap<Path, Tip> = HashMap::default();
        let mut on_path = vec![false; self.entries.len() as usize + 1];
        let mut tip = index.tip;
        while tip != Tip::ROOT {
            let entry = self.entry(tip);
            assert!(entry.parent < tip, "indices grow along a path");
            on_path[tip.0 as usize] = true;
            if let Some(ns) = entry.kind.ns() {
                let key = Key {
                    name: entry.id.name_atom(),
                    ns,
                };
                visible.entry(key).or_insert(tip);
            } else if entry.kind == Kind::Constraint {
                constraints
                    .entry(self.constraints.get(entry.item).0)
                    .or_insert(tip);
            }
            tip = entry.parent;
        }
        for at in 1..=self.entries.len() {
            assert_eq!(index.is_on_path(Tip(at)), on_path[at as usize]);
        }
        assert_eq!(visible.len(), index.visible.len());
        for (key, tip) in visible.iter() {
            assert_eq!(index.visible.get(key), Some(*tip));
        }
        assert_eq!(constraints.len(), index.visible_constraints.len());
        for (path, tip) in constraints.iter() {
            assert_eq!(index.visible_constraints.get(path), Some(tip));
        }
    }
}

// ============================================================================
// The environment handle
// ============================================================================

/// Identity of an environment version of a log.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct LogEnvId(u64, Tip);

/// Identity of the bindings module-path resolution reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct LogScopeId(u64, Tip);

/// An environment: a version of a shared log. The receiver for `Env`'s
/// callers (H.2.8, steps 5 and 6): same method names, same signatures, same
/// borrowed results.
///
/// `Clone` copies the version and updates one reference count, as cloning
/// an `Env` does today; it visits and allocates nothing. The count goes away
/// with H.2.8 step 9, when the checker context owns the log and an
/// environment is the [`Tip`] alone.
#[derive(Clone)]
pub(super) struct LogEnv {
    log: Rc<EnvLog>,
    tip: Tip,
}

impl std::fmt::Debug for LogEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LogEnv({}@{})", self.log.serial, self.tip.0)
    }
}

impl Default for LogEnv {
    fn default() -> Self {
        Self::empty()
    }
}

impl LogEnv {
    /// The empty environment: the root of one frozen log per thread.
    pub(super) fn empty() -> Self {
        thread_local! {
            static EMPTY: LogEnv = {
                let log = EnvLog::new(None);
                log.frozen.set(true);
                LogEnv { log: Rc::new(log), tip: Tip::ROOT }
            };
        }
        EMPTY.with(LogEnv::clone)
    }

    /// Freeze this environment's log: every later extension of one of its
    /// environments starts a new log based on that environment. Lookups
    /// still work, and may move the frozen log's current path.
    ///
    /// A log that binds modules is not frozen: a component table forced
    /// from a frozen log owns the log it starts, and would own its own
    /// thunk's log through the base (H.2.10, decision 2).
    pub(super) fn freeze(&self) {
        assert_eq!(
            self.log.modules.len(),
            0,
            "a log that binds modules is not frozen"
        );
        self.log.frozen.set(true);
    }

    #[cfg(test)]
    pub(super) fn log(&self) -> &EnvLog {
        &self.log
    }

    #[cfg(test)]
    pub(super) fn same_log(&self, other: &LogEnv) -> bool {
        Rc::ptr_eq(&self.log, &other.log)
    }

    /// A seed naming this environment without owning its log.
    pub(super) fn seed(&self) -> EnvSeed {
        EnvSeed {
            log: Rc::downgrade(&self.log),
            tip: self.tip,
        }
    }

    /// The environment a component table extends while it is built from
    /// `seed`, and the log the table must own to keep its children's seeds
    /// alive: `Some` exactly when extending the seed starts a new log.
    #[cfg(test)]
    pub(super) fn component_working_env(seed: &LogEnv) -> (LogEnv, Option<Rc<EnvLog>>) {
        let mut working = seed.clone();
        if seed.log.frozen.get() {
            working.start_log();
            let owned = working.log.clone();
            (working, Some(owned))
        } else {
            (working, None)
        }
    }

    fn start_log(&mut self) {
        let log = EnvLog::new(Some(self.clone()));
        self.log = Rc::new(log);
        self.tip = Tip::ROOT;
    }

    /// The log to extend: this one, or a new one when this one is frozen.
    fn writable(&mut self) {
        if self.log.frozen.get() {
            self.start_log();
        }
    }

    fn add(&mut self, kind: Kind, id: Ident, item: impl FnOnce(&EnvLog) -> u32) {
        self.writable();
        let item = item(&self.log);
        let tip = self.log.push(self.tip, kind, id, item);
        self.tip = tip;
    }

    fn no_ident() -> Ident {
        thread_local! {
            static NO_IDENT: Ident = Ident::create_persistent("");
        }
        NO_IDENT.with(|id| *id)
    }

    // ------------------------------------------------------------------
    // Identity and flags
    // ------------------------------------------------------------------

    /// Identity of this version. O(1). Equal exactly for clones of one
    /// version.
    pub(super) fn id(&self) -> LogEnvId {
        match (&self.log.base, self.tip) {
            (Some(base), Tip::ROOT) => base.id(),
            _ => LogEnvId(self.log.serial, self.tip),
        }
    }

    /// Identity of the module-level bindings: the nearest scope-changing
    /// entry. O(1) (one hop per log whose path has no such entry).
    pub(super) fn scope_id(&self) -> LogScopeId {
        let scope_ver = if self.tip == Tip::ROOT {
            Tip::ROOT
        } else {
            self.log.entry(self.tip).scope_ver
        };
        match (&self.log.base, scope_ver) {
            (Some(base), Tip::ROOT) => base.scope_id(),
            _ => LogScopeId(self.log.serial, scope_ver),
        }
    }

    /// `Env.implicit_coercion`. One entry.
    pub(super) fn implicit_coercion(&self) -> LogEnv {
        let mut env = self.clone();
        env.add(Kind::Flags, Self::no_ident(), |_| {
            u32::from(BIT_IMPLICIT_COERCION)
        });
        env
    }

    /// O(1): a field of the version's entry.
    pub(super) fn is_in_signature(&self) -> bool {
        self.log.bits_at(self.tip) & BIT_IN_SIGNATURE != 0
    }

    /// O(1).
    pub(super) fn is_implicit_coercion(&self) -> bool {
        self.log.bits_at(self.tip) & BIT_IMPLICIT_COERCION != 0
    }

    // ------------------------------------------------------------------
    // Values
    // ------------------------------------------------------------------

    /// One entry: `EnvLog::push`.
    pub(super) fn add_value(&mut self, id: Ident, desc: ValueDescription) {
        self.add(Kind::Value, id, |log| log.values.push(Arc::new(desc)));
    }

    /// `EnvLog::resolve`.
    pub(super) fn find_value(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<&ValueDescription> {
        self.find_value_with_id(name).map(|(_, desc)| desc)
    }

    /// `EnvLog::resolve`.
    pub(super) fn find_value_with_id(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(&Ident, &ValueDescription)> {
        name.name_key()
            .and_then(|key| self.log.find_name_value::<Values>(self.tip, key))
            .map(|(id, desc)| (id, desc.as_ref()))
            .ok_or_else(|| EnvError::ValueNotFound(name.text().into()))
    }

    /// `EnvLog::resolve` and the path's construction.
    pub(super) fn find_value_arc_with_path(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(Path, &Arc<ValueDescription>)> {
        name.name_key()
            .and_then(|key| self.log.find_name::<Values>(self.tip, key))
            .map(|(path, _, desc)| (path, desc))
            .ok_or_else(|| EnvError::ValueNotFound(name.text().into()))
    }

    /// Every value binding this environment holds, shadowed ones included,
    /// newest first; a replaced binding appears once, with its replacement.
    /// Cost: the length of the path plus the opened value names.
    pub(super) fn iter_values(&self) -> impl Iterator<Item = (&Ident, &ValueDescription)> {
        let mut items: Vec<(&Ident, &ValueDescription)> = Vec::new();
        // What a newer `ValueOverride` already stands in for.
        let mut replaced: HashSet<(u64, At, Option<Name>)> = HashSet::default();
        self.log.walk(self.tip, &mut |log, tip, entry| {
            match entry.kind {
                Kind::Value => {
                    if !replaced.contains(&(log.serial, At::Local(tip), None)) {
                        items.push((&entry.id, log.values.get(entry.item).as_ref()));
                    }
                }
                Kind::ValueOverride => {
                    let over = log.overrides.get(entry.item);
                    let name = match over.target {
                        At::Local(_) => None,
                        At::Open(_) => Some(entry.id.name_atom()),
                    };
                    if replaced.insert((over.target_log, over.target, name)) {
                        items.push((&entry.id, log.values.get(over.value).as_ref()));
                    }
                }
                Kind::Open => {
                    let rec = log.opens.get(entry.item);
                    for (name, (id, desc, _)) in rec.layers.values.iter() {
                        if !replaced.contains(&(log.serial, At::Open(tip), Some(*name))) {
                            items.push((id, desc.as_ref()));
                        }
                    }
                }
                _ => {}
            }
            true
        });
        items.into_iter()
    }

    /// Replace the description of the innermost binding of `name`, keeping
    /// its identifier, path and open slot (H.2.4, item 7): one `resolve` and
    /// one entry. Versions taken before keep the old description.
    pub(super) fn update_value_type_by_name(&mut self, name: &str, new_type: TypeExprRef) -> bool {
        let Some(key) = Name::lookup(name) else {
            return false;
        };
        let Some(found) = self.log.resolve(self.tip, Table::Values, key) else {
            return false;
        };
        let (id, desc, _) = EnvLog::payload::<Values>(&found, key);
        let id = *id;
        let mut updated = (**desc).clone();
        updated.val_type = new_type;
        // A replacement of a replacement stands in for the original binding.
        let (target_log, target) = match found.place {
            Place::Local(_, entry) if entry.kind == Kind::ValueOverride => {
                let over = found.log.overrides.get(entry.item);
                (over.target_log, over.target)
            }
            Place::Local(tip, _) => (found.log.serial, At::Local(tip)),
            Place::Open(open, _) => (found.log.serial, At::Open(open)),
        };
        self.add(Kind::ValueOverride, id, |log| {
            let value = log.values.push(Arc::new(updated));
            log.overrides.push(OverrideRec {
                value,
                target_log,
                target,
            })
        });
        true
    }

    /// `Pident`: `EnvLog::find_ident`. `Pdot`: `find_value` of the last name.
    pub(super) fn lookup_value(&self, path: &Path) -> EnvResult<&ValueDescription> {
        match path.view() {
            PathView::Pident(id) => self
                .log
                .find_ident(self.tip, Ns::Value, id)
                .map(|(log, entry)| Values::local(log, entry).as_ref())
                .ok_or_else(|| EnvError::ValueNotFound(id.name().into())),
            PathView::Pdot(_, name, _) => self.find_value(name),
            PathView::Papply(_, _) => Err(EnvError::ValueNotFound("(functor application)".into())),
        }
    }

    // ------------------------------------------------------------------
    // Types
    // ------------------------------------------------------------------

    /// One entry, after one lookup of the identifier's label family; a
    /// second entry removes that family when there is one (H.2.4, item 8).
    pub(super) fn add_type(&mut self, id: Ident, decl: impl Into<Arc<TypeDeclaration>>) {
        let decl = decl.into();
        let had_family = self.type_label_family(&id).is_some();
        self.add(Kind::Type, id, |log| log.types.push(decl));
        if had_family {
            self.add(Kind::Family, id, |log| log.families.push(None));
        }
    }

    /// `Env.add_type` (env.ml:1561-1569): `add_type`, then for a record its
    /// label family and one label entry per field, last field first.
    #[cfg(test)]
    pub(super) fn store_type(
        &mut self,
        ctx: &TypeContext,
        id: Ident,
        decl: impl Into<Arc<TypeDeclaration>>,
    ) {
        let decl = decl.into();
        self.add_type(id, decl.clone());
        if let TypeKind::TypeRecord(labels, _) = &decl.type_kind
            && !labels.is_empty()
        {
            let res_ty = ctx.new_generic_constr(Path::pident(id), decl.type_params.clone());
            let descs =
                crate::types::env_lazy::label_descrs(res_ty, &decl, decl.type_private, ctx, |_| {});
            self.add_type_label_family(id, descs[0].lbl_all);
            for (ld, desc) in labels.iter().zip(descs).rev() {
                self.add_label(ld.ld_id, desc);
            }
        }
    }

    /// One `find_ident` and one entry for the same identifier; the label
    /// family stays.
    pub(super) fn update_type_variance(
        &mut self,
        id: Ident,
        variance: Vec<super::super::variance::Variance>,
    ) -> Option<Arc<TypeDeclaration>> {
        let mut decl = self.find_type_arc_by_ident(&id)?.as_ref().clone();
        decl.type_variance = variance;
        let decl = Arc::new(decl);
        let stored = decl.clone();
        self.add(Kind::Type, id, |log| log.types.push(stored));
        Some(decl)
    }

    /// `EnvLog::resolve`.
    pub(super) fn find_type(&self, name: impl crate::name::NameKey) -> EnvResult<&TypeDeclaration> {
        name.name_key()
            .and_then(|key| self.log.find_name_value::<Types>(self.tip, key))
            .map(|(_, decl)| decl.as_ref())
            .ok_or_else(|| EnvError::TypeNotFound(name.text().into()))
    }

    /// `EnvLog::resolve` and the path's construction.
    pub(super) fn find_type_with_path(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(Path, &TypeDeclaration)> {
        self.find_type_arc_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
    }

    /// `EnvLog::resolve` and the path's construction.
    pub(super) fn find_type_arc_with_path(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(Path, &Arc<TypeDeclaration>)> {
        name.name_key()
            .and_then(|key| self.log.find_name::<Types>(self.tip, key))
            .map(|(path, _, decl)| (path, decl))
            .ok_or_else(|| EnvError::TypeNotFound(name.text().into()))
    }

    /// `EnvLog::find_ident`.
    pub(super) fn find_type_by_ident(&self, id: &Ident) -> EnvResult<&TypeDeclaration> {
        self.find_type_arc_by_ident(id)
            .map(|decl| decl.as_ref())
            .ok_or_else(|| EnvError::TypeNotFound(id.name().into()))
    }

    /// `EnvLog::find_ident`.
    pub(super) fn find_type_arc_by_ident(&self, id: &Ident) -> Option<&Arc<TypeDeclaration>> {
        self.log
            .find_ident(self.tip, Ns::Type, id)
            .map(|(log, entry)| log.types.get(entry.item))
    }

    /// `find_ident`, then `resolve` of the identifier's name (the documented
    /// recovery of `Env::lookup_type`).
    pub(super) fn lookup_type_arc_by_ident(&self, id: &Ident) -> Option<&Arc<TypeDeclaration>> {
        self.find_type_arc_by_ident(id).or_else(|| {
            self.log
                .find_name_value::<Types>(self.tip, id.name_atom())
                .map(|(_, decl)| decl)
        })
    }

    /// `Env::lookup_type`: by identifier then name for `Pident`; through the
    /// parent module's signature, then by name, for `Pdot`.
    pub(super) fn lookup_type(&self, path: &Path) -> EnvResult<&TypeDeclaration> {
        fn find_type_in_module_type<'a>(
            env: &'a LogEnv,
            mty: &'a ModuleType,
            name: &str,
            depth: usize,
        ) -> Option<&'a TypeDeclaration> {
            if depth > 10 {
                return None;
            }
            match mty {
                ModuleType::MtySignature(sig) => sig.iter().find_map(|item| match item {
                    SignatureItem::SigType(id, decl, _) if id.name() == name => Some(&**decl),
                    _ => None,
                }),
                ModuleType::MtyIdent(_) | ModuleType::MtyAlias(..) => {
                    let type_path = mty.ident_or_alias_path().unwrap();
                    if let Ok(mtd) = env.lookup_modtype(type_path)
                        && let Some(resolved) = &mtd.mtd_type
                    {
                        return find_type_in_module_type(env, resolved, name, depth + 1);
                    }
                    if let Ok(md) = env.lookup_module(type_path) {
                        return find_type_in_module_type(env, &md.md_type, name, depth + 1);
                    }
                    None
                }
                _ => None,
            }
        }
        match path.view() {
            PathView::Pident(id) => self
                .lookup_type_arc_by_ident(id)
                .map(|decl| decl.as_ref())
                .ok_or_else(|| EnvError::TypeNotFound(id.name().into())),
            PathView::Pdot(parent, name, _) => {
                if let Ok(parent_md) = self.lookup_module(parent)
                    && let Some(decl) = find_type_in_module_type(self, &parent_md.md_type, name, 0)
                {
                    return Ok(decl);
                }
                self.find_type(name)
            }
            PathView::Papply(_, _) => Err(EnvError::TypeNotFound("(functor application)".into())),
        }
    }

    // ------------------------------------------------------------------
    // Constructors and labels
    // ------------------------------------------------------------------

    /// One entry.
    pub(super) fn add_constructor(&mut self, id: Ident, desc: ConstructorDescription) {
        self.add(Kind::Constructor, id, |log| {
            log.constrs.push(Arc::new(desc))
        });
    }

    /// `EnvLog::first_candidate`.
    pub(super) fn find_constructor(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<&ConstructorDescription> {
        name.name_key()
            .and_then(|key| self.log.first_candidate::<Constructors>(self.tip, key))
            .ok_or_else(|| EnvError::ConstructorNotFound(name.text().into()))
    }

    /// `EnvLog::candidates`.
    pub(super) fn find_all_constructors(
        &self,
        name: impl crate::name::NameKey,
    ) -> Vec<&ConstructorDescription> {
        self.find_all_constructors_marking(name)
            .into_iter()
            .map(|(desc, _)| desc)
            .collect()
    }

    /// `EnvLog::candidates`, each candidate of an open with its slot and the
    /// first candidate the open hides.
    pub(super) fn find_all_constructors_marking(
        &self,
        name: impl crate::name::NameKey,
    ) -> Vec<(
        &ConstructorDescription,
        OpenSlotMark<'_, ConstructorDescription>,
    )> {
        match name.name_key() {
            Some(key) => self.log.all_candidates::<Constructors>(self.tip, key),
            None => Vec::new(),
        }
    }

    /// One entry.
    pub(super) fn add_label(&mut self, id: Ident, desc: LabelDescription) {
        self.add(Kind::Label, id, |log| log.labels.push(Arc::new(desc)));
    }

    /// One entry keyed by the type's identifier.
    pub(super) fn add_type_label_family(
        &mut self,
        id: Ident,
        lbl_all: super::super::decl::LabelArrayRef,
    ) {
        self.add(Kind::Family, id, |log| log.families.push(Some(lbl_all)));
    }

    /// The innermost family entry of exactly `id`: one probe and one `chain`
    /// step per family entry of the name examined.
    pub(super) fn type_label_family(
        &self,
        id: &Ident,
    ) -> Option<super::super::decl::LabelArrayRef> {
        let mut log = &*self.log;
        let mut tip = self.tip;
        loop {
            let mut head = log.head(
                tip,
                Key {
                    name: id.name_atom(),
                    ns: Ns::Family,
                },
            );
            while head != Tip::ROOT {
                bump(&log.steps.chain);
                let entry = log.entry(head);
                if entry.id == *id {
                    return *log.families.get(entry.item);
                }
                head = entry.shadows;
            }
            (log, tip) = log.base()?;
        }
    }

    /// `EnvLog::first_candidate`.
    pub(super) fn find_label(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<&LabelDescription> {
        name.name_key()
            .and_then(|key| self.log.first_candidate::<Labels>(self.tip, key))
            .ok_or_else(|| EnvError::LabelNotFound(name.text().into()))
    }

    /// `EnvLog::candidates`.
    pub(super) fn find_all_labels(
        &self,
        name: impl crate::name::NameKey,
    ) -> Vec<&LabelDescription> {
        self.find_all_labels_marking(name)
            .into_iter()
            .map(|(desc, _)| desc)
            .collect()
    }

    /// `EnvLog::candidates`, with marking.
    pub(super) fn find_all_labels_marking(
        &self,
        name: impl crate::name::NameKey,
    ) -> Vec<(&LabelDescription, OpenSlotMark<'_, LabelDescription>)> {
        match name.name_key() {
            Some(key) => self.log.all_candidates::<Labels>(self.tip, key),
            None => Vec::new(),
        }
    }

    // ------------------------------------------------------------------
    // Modules
    // ------------------------------------------------------------------

    #[cfg(test)]
    pub(super) fn add_module_with_component_path(
        &mut self,
        id: Ident,
        decl: ModuleDeclaration,
        component_path: Path,
    ) {
        self.add_module_with_component_context(id, decl.clone(), decl, component_path, None);
    }

    /// One entry holding the declaration and the component thunk. The
    /// thunk's seed is the version before the binding, named without owning
    /// the log: no allocation beyond the thunk itself.
    pub(super) fn add_module_with_component_context(
        &mut self,
        id: Ident,
        decl: ModuleDeclaration,
        component_decl: ModuleDeclaration,
        component_path: Path,
        parent_context: Option<(Path, Arc<Signature>)>,
    ) {
        self.writable();
        let components = Rc::new(LogComponents {
            seed: self.seed(),
            access_path: component_path,
            module_decl: component_decl,
            parent_context,
        });
        self.add(Kind::Module, id, |log| {
            let item = log.modules.push(Arc::new(decl));
            let same = log.components.push(components);
            debug_assert_eq!(item, same);
            item
        });
    }

    /// `add_module_with_component_context` with the module's own path.
    #[cfg(test)]
    pub(super) fn add_module(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.add_module_with_component_path(id, decl, Path::pident(id));
    }

    /// `add_module` and one marker entry.
    #[cfg(test)]
    pub(super) fn add_module_arg(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.add_module(id, decl);
        self.mark_functor_arg(id);
    }

    pub(super) fn mark_functor_arg(&mut self, id: Ident) {
        self.add(Kind::FunctorArg, id, |_| 0);
    }

    /// For `Pident`: one probe and one `chain` step per marker of the name.
    pub(super) fn is_functor_arg_path(&self, path: &Path) -> bool {
        match path.view() {
            PathView::Pident(id) => {
                let mut log = &*self.log;
                let mut tip = self.tip;
                loop {
                    let mut head = log.head(
                        tip,
                        Key {
                            name: id.name_atom(),
                            ns: Ns::FunctorArg,
                        },
                    );
                    while head != Tip::ROOT {
                        bump(&log.steps.chain);
                        let entry = log.entry(head);
                        if entry.id == *id {
                            return true;
                        }
                        head = entry.shadows;
                    }
                    match log.base() {
                        Some(base) => (log, tip) = base,
                        None => return false,
                    }
                }
            }
            PathView::Pdot(parent, _, _) => self.is_functor_arg_path(parent),
            PathView::Papply(_, _) => true,
        }
    }

    /// Open the tables of one signature under `root`: one entry, whatever
    /// the number of names (the tables are shared, not copied or indexed).
    /// No entry when every table is empty.
    pub(super) fn add_prebuilt_open_layers(
        &mut self,
        root: Path,
        layers: &OpenedLayers,
        slot: Option<u32>,
    ) {
        if layers.is_empty() {
            return;
        }
        let mut mask = 0;
        for (table, empty) in [
            (Table::Values, layers.values.is_empty()),
            (Table::Types, layers.types.is_empty()),
            (Table::Modules, layers.modules.is_empty()),
            (Table::Components, layers.module_components.is_empty()),
            (Table::Modtypes, layers.modtypes.is_empty()),
            (Table::Constructors, layers.constrs.is_empty()),
            (Table::Labels, layers.labels.is_empty()),
        ] {
            if !empty {
                mask |= table.bit();
            }
        }
        let tip = self.tip;
        self.add(Kind::Open, Self::no_ident(), |log| {
            log.opens.push(OpenRec {
                layers: OpenedLayers {
                    values: layers.values.clone(),
                    types: layers.types.clone(),
                    constrs: layers.constrs.clone(),
                    labels: layers.labels.clone(),
                    modules: layers.modules.clone(),
                    module_components: layers.module_components.clone(),
                    modtypes: layers.modtypes.clone(),
                },
                root: Arc::new(root),
                slot,
                mask,
                // `tip` is in `log` unless `log` was just started. With the
                // injected fault, an open forgets the opens before it.
                older: if log.entries.len() == 0 || INJECT_FAULT.get() {
                    OpenAt::default()
                } else {
                    log.open_at(tip)
                },
            })
        });
    }

    /// The slot of the open an unqualified name resolves through, and
    /// whether that open hides an earlier binding: `resolve`, and for a name
    /// found through an open a second `resolve` at the version before it.
    pub(super) fn open_slot_use(
        &self,
        kind: OpenLookupKind,
        name: impl crate::name::NameKey,
    ) -> Option<OpenSlotUse> {
        let name = name.name_key()?;
        let table = match kind {
            OpenLookupKind::Value => Table::Values,
            OpenLookupKind::Type => Table::Types,
            OpenLookupKind::Module => Table::Modules,
            OpenLookupKind::Component => Table::Components,
            OpenLookupKind::Modtype => Table::Modtypes,
        };
        let found = self.log.resolve(self.tip, table, name)?;
        let Place::Open(open, rec) = found.place else {
            return None;
        };
        let slot = rec.slot?;
        let before = found.log.entry(open).parent;
        Some(OpenSlotUse {
            slot,
            shadowed: found.log.resolve(before, table, name).is_some(),
        })
    }

    /// `EnvLog::resolve`.
    pub(super) fn find_module(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<&ModuleDeclaration> {
        self.find_module_with_id(name).map(|(_, decl)| decl)
    }

    /// `EnvLog::resolve`.
    pub(super) fn find_module_with_id(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(&Ident, &ModuleDeclaration)> {
        name.name_key()
            .and_then(|key| self.log.find_name_value::<Modules>(self.tip, key))
            .map(|(id, decl)| (id, decl.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.text().into()))
    }

    /// `EnvLog::resolve` and the path's construction.
    pub(super) fn find_module_with_path(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(Path, &ModuleDeclaration)> {
        name.name_key()
            .and_then(|key| self.log.find_name::<Modules>(self.tip, key))
            .map(|(path, _, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.text().into()))
    }

    /// `find_module_with_path` of the path's first dotted component.
    pub(super) fn path_starts_with_opened_component(&self, path: &Path) -> bool {
        let Some(component_path) = Env::first_dotted_component_path(path) else {
            return false;
        };
        self.find_module_with_path(component_path.last())
            .ok()
            .is_some_and(|(selected_path, _)| selected_path.same(&component_path))
    }

    /// One entry.
    pub(super) fn mark_implicit_open_root(&mut self, name: &str) {
        let id = Ident::create_persistent(name);
        self.add(Kind::ImplicitRoot, id, |_| 0);
    }

    /// One probe, then `path_starts_with_opened_component`.
    pub(super) fn path_starts_with_implicit_opened_component(&self, path: &Path) -> bool {
        let Some(component_path) = Env::first_dotted_component_path(path) else {
            return false;
        };
        let Some(name) = Name::lookup(component_path.head().name()) else {
            return false;
        };
        let key = Key {
            name,
            ns: Ns::ImplicitRoot,
        };
        let mut log = &*self.log;
        let mut tip = self.tip;
        loop {
            if log.head(tip, key) != Tip::ROOT {
                return self.path_starts_with_opened_component(path);
            }
            match log.base() {
                Some(base) => (log, tip) = base,
                None => return false,
            }
        }
    }

    /// `EnvLog::find_ident`.
    pub(super) fn has_module_ident(&self, id: &Ident) -> bool {
        self.log.find_ident(self.tip, Ns::Module, id).is_some()
    }

    /// `EnvLog::find_ident`.
    pub(super) fn lookup_module_ident_exact(&self, id: &Ident) -> EnvResult<&ModuleDeclaration> {
        self.log
            .find_ident(self.tip, Ns::Module, id)
            .map(|(log, entry)| log.modules.get(entry.item).as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(id.name().into()))
    }

    /// `EnvLog::find_ident`.
    pub(super) fn find_module_same(&self, id: &Ident) -> EnvResult<&ModuleDeclaration> {
        self.lookup_module_ident_exact(id)
    }

    /// `EnvLog::find_ident`.
    pub(super) fn with_local_module_components<R>(
        &self,
        path: &Path,
        f: impl FnOnce(&LogComponents) -> R,
    ) -> Option<R> {
        let PathView::Pident(id) = path.view() else {
            return None;
        };
        let (log, entry) = self.log.find_ident(self.tip, Ns::Module, id)?;
        Some(f(log.components.get(entry.item)))
    }

    /// `EnvLog::find_ident` and one reference-count update: the thunk is
    /// shared, not copied.
    pub(super) fn local_module_components_shared(&self, path: &Path) -> Option<Rc<LogComponents>> {
        let PathView::Pident(id) = path.view() else {
            return None;
        };
        let (log, entry) = self.log.find_ident(self.tip, Ns::Module, id)?;
        Some(log.components.get(entry.item).clone())
    }

    /// `Env::lookup_module`: by identifier then name for the head, then
    /// through signatures.
    pub(super) fn lookup_module(&self, path: &Path) -> EnvResult<&ModuleDeclaration> {
        fn lookup_submodule_in_module_type<'a>(
            env: &'a LogEnv,
            mty: &'a ModuleType,
            name: &str,
            visiting: &mut smallvec::SmallVec<[Path; 4]>,
        ) -> Option<&'a ModuleDeclaration> {
            match mty {
                ModuleType::MtySignature(sig) => sig.iter().find_map(|item| match item {
                    SignatureItem::SigModule(id, md, _) if id.name() == name => Some(md),
                    _ => None,
                }),
                ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
                    let alias_path = mty.ident_or_alias_path().unwrap();
                    let md = lookup_module_inner(env, alias_path, visiting).ok()?;
                    lookup_submodule_in_module_type(env, &md.md_type, name, visiting)
                }
                ModuleType::MtyFunctor { .. } => None,
            }
        }

        fn lookup_module_inner<'a>(
            env: &'a LogEnv,
            path: &Path,
            visiting: &mut smallvec::SmallVec<[Path; 4]>,
        ) -> EnvResult<&'a ModuleDeclaration> {
            if visiting.contains(path) {
                return Err(EnvError::ModuleNotFound(path.name().into()));
            }
            visiting.push(*path);
            match path.view() {
                PathView::Pident(id) => env
                    .lookup_module_ident_exact(id)
                    .or_else(|_| env.find_module(id.name_atom())),
                PathView::Pdot(parent, name, _) => {
                    let parent_md = lookup_module_inner(env, parent, visiting)?;
                    lookup_submodule_in_module_type(env, &parent_md.md_type, name, visiting)
                        .ok_or_else(|| EnvError::ModuleNotFound((*name).into()))
                }
                PathView::Papply(_, _) => {
                    Err(EnvError::ModuleNotFound("(functor application)".into()))
                }
            }
        }

        let mut visiting = smallvec::SmallVec::new();
        lookup_module_inner(self, path, &mut visiting)
    }

    /// `Env.normalize_path` (env.ml:868-888), on `lookup_module`.
    pub(super) fn normalize_path(&self, ctx: &TypeContext, path: &Path) -> Path {
        *self.normalize_shared_path(ctx, &Arc::new(*path), 0)
    }

    /// `Env.normalize_path_prefix` (env.ml:898-902).
    pub(super) fn normalize_path_prefix(&self, ctx: &TypeContext, path: &Path) -> Path {
        match path.view() {
            PathView::Pdot(..) => {
                ctx.rebuild_dotted(path, |prefix| self.normalize_shared_path(ctx, prefix, 0))
            }
            PathView::Pident(_) => *path,
            PathView::Papply(_, _) => panic!("normalize_path_prefix called on Papply"),
        }
    }

    fn normalize_shared_path(
        &self,
        ctx: &TypeContext,
        path: &Arc<Path>,
        depth: usize,
    ) -> Arc<Path> {
        if depth > 20 {
            return path.clone();
        }
        let path = match path.view() {
            PathView::Pdot(..) => Arc::new(ctx.rebuild_dotted(path, |prefix| {
                self.normalize_shared_path(ctx, prefix, depth + 1)
            })),
            _ => path.clone(),
        };
        if let Ok(md) = self.lookup_module(&path)
            && let ModuleType::MtyAlias(_, alias_path) = &md.md_type
        {
            return self.normalize_shared_path(ctx, alias_path, depth + 1);
        }
        path
    }

    /// The local module aliases no later binding or open hides, computed
    /// once per scope version by a walk of the path.
    pub(super) fn with_current_local_module_aliases<R>(
        &self,
        f: impl FnOnce(&[(Ident, Path)]) -> R,
    ) -> R {
        let caches = self.scope_caches();
        if caches.local_module_aliases.borrow().is_none() {
            let mut seen: HashSet<Name> = HashSet::default();
            let mut opens: Vec<&OpenRec> = Vec::new();
            let mut aliases: Vec<(Ident, Path)> = Vec::new();
            self.log.walk(self.tip, &mut |log, _, entry| {
                match entry.kind {
                    Kind::Open => {
                        let rec = log.opens.get(entry.item);
                        if rec.mask & Table::Modules.bit() != 0 {
                            opens.push(rec);
                        }
                    }
                    Kind::Module => {
                        let name = entry.id.name_atom();
                        if !opens.iter().any(|rec| rec.has(Table::Modules, name))
                            && seen.insert(name)
                        {
                            let decl = log.modules.get(entry.item);
                            if let ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) =
                                &decl.md_type
                            {
                                let target = decl.md_type.ident_or_alias_path().unwrap();
                                aliases.push((entry.id, *target));
                            }
                        }
                    }
                    _ => {}
                }
                true
            });
            aliases.sort_by(|(left_id, left_target), (right_id, right_target)| {
                right_target
                    .name()
                    .len()
                    .cmp(&left_target.name().len())
                    .then_with(|| right_target.name().cmp(&left_target.name()))
                    .then_with(|| right_id.stamp().cmp(&left_id.stamp()))
            });
            *caches.local_module_aliases.borrow_mut() = Some(aliases);
        }
        let cache = caches.local_module_aliases.borrow();
        f(cache.as_deref().unwrap_or(&[]))
    }

    /// The memo tables of this version's scope: one probe.
    fn scope_caches(&self) -> Rc<ScopeCaches> {
        let scope_ver = if self.tip == Tip::ROOT {
            Tip::ROOT
        } else {
            self.log.entry(self.tip).scope_ver
        };
        self.log
            .index
            .borrow_mut()
            .scope_caches
            .entry(scope_ver)
            .or_default()
            .clone()
    }

    /// `Env::module_path_requires_env_scoped_cache`, memoised per scope.
    pub(super) fn module_path_requires_env_scoped_cache(&self, module_path: &Path) -> bool {
        if module_path.head().is_persistent() {
            return false;
        }
        let Some(cache_key) = Env::module_path_scope_cache_key(module_path) else {
            return false;
        };
        let caches = self.scope_caches();
        if let Some(cached) = caches
            .module_path_requires_env_scoped
            .borrow()
            .get(&cache_key)
            .copied()
        {
            return cached;
        }
        let requires = self.with_current_local_module_aliases(|aliases| {
            aliases.iter().any(|(_, target_path)| {
                self.has_module_ident(target_path.head())
                    && Env::path_has_prefix(module_path, target_path)
            })
        });
        caches
            .module_path_requires_env_scoped
            .borrow_mut()
            .insert(cache_key, requires);
        requires
    }

    // ------------------------------------------------------------------
    // Module types
    // ------------------------------------------------------------------

    /// One entry.
    pub(super) fn add_modtype(&mut self, id: Ident, decl: ModtypeDeclaration) {
        self.add(Kind::Modtype, id, |log| log.modtypes.push(Arc::new(decl)));
    }

    /// `EnvLog::resolve`.
    pub(super) fn find_modtype(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<&ModtypeDeclaration> {
        name.name_key()
            .and_then(|key| self.log.find_name_value::<Modtypes>(self.tip, key))
            .map(|(_, decl)| decl.as_ref())
            .ok_or_else(|| EnvError::ModtypeNotFound(name.text().into()))
    }

    /// `EnvLog::resolve` and the path's construction.
    pub(super) fn find_modtype_with_path(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(Path, &ModtypeDeclaration)> {
        name.name_key()
            .and_then(|key| self.log.find_name::<Modtypes>(self.tip, key))
            .map(|(path, _, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::ModtypeNotFound(name.text().into()))
    }

    /// `Env::lookup_modtype`: `find_ident` for `Pident`; the parent module's
    /// signature for `Pdot`.
    pub(super) fn lookup_modtype(&self, path: &Path) -> EnvResult<&ModtypeDeclaration> {
        match path.view() {
            PathView::Pident(id) => self
                .log
                .find_ident(self.tip, Ns::Modtype, id)
                .map(|(log, entry)| log.modtypes.get(entry.item).as_ref())
                .ok_or_else(|| EnvError::ModtypeNotFound(id.name().into())),
            PathView::Pdot(parent, name, _) => {
                let parent_md = self
                    .lookup_module(parent)
                    .or_else(|_| self.find_module(parent.last()));
                if let Ok(parent_md) = parent_md
                    && let ModuleType::MtySignature(sig) = &parent_md.md_type
                {
                    for item in sig.iter() {
                        if let SignatureItem::SigModtype(id, decl) = item
                            && id.name() == name
                        {
                            return Ok(decl);
                        }
                    }
                }
                Err(EnvError::ModtypeNotFound((*name).into()))
            }
            PathView::Papply(_, _) => {
                Err(EnvError::ModtypeNotFound("(functor application)".into()))
            }
        }
    }

    /// `Env.fold_modtypes` with no module prefix (env.ml:2003): the names in
    /// OCaml's visit order, per layer. A layer boundary is an open whose
    /// module-type table is not empty. Cost: the length of the path plus the
    /// names visited.
    pub(super) fn fold_modtype_names(&self) -> Vec<String> {
        fn flush<'a>(layer: &mut Vec<(&'a str, i32)>, names: &mut Vec<&'a str>) {
            names.extend(ident_tbl_fold_name_order(layer.drain(..)));
        }
        let mut names: Vec<&str> = Vec::new();
        // Each name of the layer with the stamp of its first binding there.
        let mut layer: Vec<(&str, i32)> = Vec::new();
        self.log.walk(self.tip, &mut |log, _, entry| {
            match entry.kind {
                Kind::Modtype => {
                    let name = entry.id.name_atom().as_str();
                    // Newest first: an older binding of the name replaces
                    // the stamp recorded for it.
                    match layer
                        .iter_mut()
                        .find(|(bound, _)| std::ptr::eq(*bound, name))
                    {
                        Some(bound) => bound.1 = entry.id.stamp(),
                        None => layer.push((name, entry.id.stamp())),
                    }
                }
                Kind::Open => {
                    let rec = log.opens.get(entry.item);
                    if rec.mask & Table::Modtypes.bit() != 0 {
                        flush(&mut layer, &mut names);
                        let mut opened: Vec<&str> = rec
                            .layers
                            .modtypes
                            .keys()
                            .map(|name| name.as_str())
                            .collect();
                        opened.sort_unstable();
                        names.extend(opened);
                    }
                }
                _ => {}
            }
            true
        });
        flush(&mut layer, &mut names);
        fold_names_list(names)
    }

    // ------------------------------------------------------------------
    // Local constraints
    // ------------------------------------------------------------------

    /// O(1): a bit of the version's entry (H.2.4, item 12).
    #[inline]
    pub(super) fn has_local_constraints(&self) -> bool {
        self.log.bits_at(self.tip) & BIT_CONSTRAINTS != 0
    }

    /// One entry keyed by the path.
    pub(super) fn add_local_constraint(&mut self, path: Path, decl: TypeDeclaration) {
        self.add(Kind::Constraint, Self::no_ident(), |log| {
            log.constraints.push((path, Arc::new(decl)))
        });
    }

    /// The bit test when there is no constraint; otherwise one probe of the
    /// constraint index, plus the `chain` steps of an older version.
    pub(super) fn find_local_constraint(&self, path: &Path) -> Option<&TypeDeclaration> {
        let mut log = &*self.log;
        let mut tip = self.tip;
        while log.bits_at(tip) & BIT_CONSTRAINTS != 0 {
            if tip != Tip::ROOT {
                let on_path = log.index.borrow().is_on_path(tip);
                if !on_path {
                    log.make_tip(&mut log.index.borrow_mut(), tip);
                }
                bump(&log.steps.probes);
                let mut head = log
                    .index
                    .borrow()
                    .visible_constraints
                    .get(path)
                    .copied()
                    .unwrap_or(Tip::ROOT);
                while head > tip {
                    bump(&log.steps.chain);
                    head = log.entry(head).shadows;
                }
                if head != Tip::ROOT {
                    return Some(log.constraints.get(log.entry(head).item).1.as_ref());
                }
            }
            (log, tip) = log.base()?;
        }
        None
    }

    /// Every visible constraint, newest first. Cost: the entries from this
    /// version up to the oldest constraint it sees.
    pub(super) fn iter_local_constraints(&self) -> impl Iterator<Item = (&Path, &TypeDeclaration)> {
        let mut items: Vec<(&Path, &TypeDeclaration)> = Vec::new();
        let mut seen: HashSet<Path> = HashSet::default();
        self.log.walk(self.tip, &mut |log, _, entry| {
            if entry.bits & BIT_CONSTRAINTS == 0 {
                return false;
            }
            if entry.kind == Kind::Constraint {
                let (path, decl) = log.constraints.get(entry.item);
                if seen.insert(*path) {
                    items.push((path, decl.as_ref()));
                }
            }
            true
        });
        items.into_iter()
    }

    /// One entry with no payload.
    pub(super) fn add_gadt_instance_level(&mut self) {
        self.add(Kind::GadtLevel, Self::no_ident(), |_| 0);
    }
}

#[cfg(test)]
#[path = "env_log_tests.rs"]
mod tests;
