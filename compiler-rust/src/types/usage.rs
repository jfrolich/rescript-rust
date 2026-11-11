//! The usage tables of OCaml `Env` (compiler/ml/env.ml:27-53).
//!
//! A declaration is identified by its name and location. `Env.check_usage`
//! (env.ml:1562-1576) registers a callback for it when the declaration enters
//! the environment with `~check:true`; lookups (`Env.lookup_type`,
//! `Env.lookup_module`, ...) and inclusion tests (`Includemod`) call the
//! callback through `Env.mark_*_used`. The unused warnings are delayed checks
//! reading the flag the callback sets.
//!
//! Callbacks are closures in OCaml; here they are the closed set of shapes the
//! type checker installs.


use crate::name::{Name, NameKey};

use crate::location::Location;

/// A `used` flag (`let used = ref false`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UsedCell(u32);

/// A recursive-definition slot (`let slot = ref []`, typedecl.ml:1486).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeSlot(u32);

/// The `current_slot`/`rec_needed` refs of one `Typecore.type_let`
/// (typecore.ml:4572-4573).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LetGroup(u32);

/// A binding's `slot` in `Typecore.type_let` (typecore.ml:4605).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LetSlot(u32);

/// An entry of `Env.used_constructors` (`constructor_usages`, env.ml:40-47).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstructorUsageCell(u32);

/// `Env.constructor_usage` (env.ml:38).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstructorUsage {
    /// The constructor is used to build a value.
    Positive,
    /// The constructor is matched in a pattern.
    Pattern,
    /// The constructor is exported through a private type.
    Privatize,
}

/// `Env.constructor_usages` (env.ml:39-43).
#[derive(Debug, Clone, Copy, Default)]
pub struct ConstructorUsages {
    /// Whether the constructor is used to build a value.
    pub cu_positive: bool,
    /// Whether it is matched in a pattern.
    pub cu_pattern: bool,
    /// Whether it is exported through a private type.
    pub cu_privatize: bool,
}

#[derive(Debug, Clone)]
enum TypeCallback {
    /// `fun () -> used := true` (env.ml:1568).
    SetUsed(UsedCell),
    /// The callback `Typedecl.transl_type_decl` installs for a recursive
    /// definition (typedecl.ml:1489-1496): while a declaration of the group
    /// is translated, uses are recorded in its slot; afterwards a use marks
    /// the recorded declarations and runs the previous callback.
    RecSlot {
        name: Name,
        loc: Location,
        slot: TypeSlot,
        old: Box<TypeCallback>,
    },
}

#[derive(Debug, Clone)]
enum ValueCallback {
    /// `fun () -> used := true` (env.ml:1568).
    SetUsed(UsedCell),
    /// The callback `Typecore.type_let` installs for a let-bound identifier
    /// (typecore.ml:4619-4628): while a binding of a recursive group is
    /// typed, record the identifier in its slot; otherwise mark the recorded
    /// identifiers and the identifier used.
    LetSlot {
        name: Name,
        loc: Location,
        group: LetGroup,
        slot: LetSlot,
        used: UsedCell,
        some_used: UsedCell,
    },
}

#[derive(Debug, Default, Clone, Copy)]
struct LetGroupState {
    current_slot: Option<LetSlot>,
    rec_needed: bool,
}

type HashMap<K, V> = hashbrown::HashMap<K, V, crate::fast_hash::FastState>;

/// The interned name of a name being registered.
fn intern(name: impl NameKey) -> Name {
    name.name_key().unwrap_or_else(|| Name::new(name.text()))
}

/// The usage-tracking state of one compilation: OCaml's `Env` usage
/// callback tables (env.ml:1146-1200) and the `ref` cells their callbacks
/// set.
#[derive(Debug, Default)]
pub struct UsageTables {
    /// `Env.value_declarations`; a key's callbacks run in registration order
    /// (`set_value_used_callback` chains `old (); callback ()`).
    value_declarations: HashMap<(Name, Location), Vec<ValueCallback>>,
    let_groups: Vec<LetGroupState>,
    let_slots: Vec<Vec<(Name, Location)>>,
    type_declarations: HashMap<(Name, Location), TypeCallback>,
    module_declarations: HashMap<(Name, Location), UsedCell>,
    used_constructors: HashMap<(Name, Location, Name), ConstructorUsageCell>,
    cells: Vec<bool>,
    constructor_usages: Vec<ConstructorUsages>,
    type_slots: Vec<Vec<(Name, Location)>>,
    /// `current_slot` of `Typedecl.transl_type_decl` (typedecl.ml:1479).
    current_type_slot: Option<TypeSlot>,
}

/// Whether `check_usage` registers a delayed warning for `name`
/// (env.ml:1569).
pub fn warns_for_name(name: &str) -> bool {
    !(name.is_empty() || name.starts_with('_') || name.starts_with('#'))
}

impl UsageTables {
    /// A new usage cell, initially unused.
    pub fn new_cell(&mut self) -> UsedCell {
        self.cells.push(false);
        UsedCell(self.cells.len() as u32 - 1)
    }

    /// `check_usage loc id warn value_declarations` (env.ml:1562-1576) once the
    /// ghost/active guard passed.
    pub fn check_value_usage(&mut self, name: impl NameKey, loc: Location) -> Option<UsedCell> {
        let name = intern(name);
        if self.value_declarations.contains_key(&(name, loc)) {
            return None;
        }
        let cell = self.new_cell();
        self.value_declarations
            .insert((name, loc), vec![ValueCallback::SetUsed(cell)]);
        Some(cell)
    }

    /// Drop a registration whose delayed check was rolled back with a
    /// speculative typing attempt.
    pub fn unregister_value_usage(&mut self, name: impl NameKey, loc: Location, cell: UsedCell) {
        let Some(name) = name.name_key() else {
            return;
        };
        let key = (name, loc);
        if let Some(callbacks) = self.value_declarations.get_mut(&key) {
            callbacks.retain(|cb| !matches!(cb, ValueCallback::SetUsed(c) if *c == cell));
            if callbacks.is_empty() {
                self.value_declarations.remove(&key);
            }
        }
    }

    /// `Env.mark_value_used` (env.ml:1125-1128) without the
    /// implicit-coercion guard.
    pub fn mark_value_used(&mut self, name: impl NameKey, loc: Location) {
        let Some(name) = name.name_key() else {
            return;
        };
        let Some(callbacks) = self.value_declarations.get(&(name, loc)) else {
            return;
        };
        // Slots whose recorded identifiers are marked once the callback list
        // is no longer borrowed; the callbacks only set flags and record
        // names, so running those marks last leaves the same state.
        let mut released: smallvec::SmallVec<[(LetSlot, UsedCell, UsedCell); 2]> =
            smallvec::SmallVec::new();
        for callback in callbacks {
            match callback {
                ValueCallback::SetUsed(cell) => self.cells[cell.0 as usize] = true,
                ValueCallback::LetSlot {
                    name,
                    loc,
                    group,
                    slot,
                    used,
                    some_used,
                } => {
                    let state = &mut self.let_groups[group.0 as usize];
                    match state.current_slot {
                        Some(current) => {
                            state.rec_needed = true;
                            self.let_slots[current.0 as usize].push((*name, *loc));
                        }
                        None => released.push((*slot, *used, *some_used)),
                    }
                }
            }
        }
        for (slot, used, some_used) in released {
            let recorded = std::mem::take(&mut self.let_slots[slot.0 as usize]);
            for (name, loc) in recorded {
                self.mark_value_used(name, loc);
            }
            self.cells[used.0 as usize] = true;
            self.cells[some_used.0 as usize] = true;
        }
    }

    /// A new `type_let` (`current_slot`, `rec_needed`).
    pub fn new_let_group(&mut self) -> LetGroup {
        self.let_groups.push(LetGroupState::default());
        LetGroup(self.let_groups.len() as u32 - 1)
    }

    /// A new slot of a `let` group, collecting the names bound in one binding.
    pub fn new_let_slot(&mut self) -> LetSlot {
        self.let_slots.push(Vec::new());
        LetSlot(self.let_slots.len() as u32 - 1)
    }

    /// `current_slot := slot`.
    pub fn set_let_current_slot(&mut self, group: LetGroup, slot: Option<LetSlot>) {
        self.let_groups[group.0 as usize].current_slot = slot;
    }

    /// Whether the group's bindings use one another (`rec_needed`), so `rec`
    /// is needed.
    pub fn let_rec_needed(&self, group: LetGroup) -> bool {
        self.let_groups[group.0 as usize].rec_needed
    }

    /// `Env.set_value_used_callback name vd callback` (env.ml:1146-1157)
    /// with the callback of typecore.ml:4619-4628.
    pub fn set_let_value_used_callback(
        &mut self,
        name: impl NameKey,
        loc: Location,
        group: LetGroup,
        slot: LetSlot,
        used: UsedCell,
        some_used: UsedCell,
    ) {
        let name = intern(name);
        self.value_declarations
            .entry((name, loc))
            .or_default()
            .push(ValueCallback::LetSlot {
                name,
                loc,
                group,
                slot,
                used,
                some_used,
            });
    }

    /// Whether the cell has been marked used.
    pub fn is_used(&self, cell: UsedCell) -> bool {
        self.cells[cell.0 as usize]
    }

    /// How the constructor of `cell` has been used.
    pub fn constructor_usages(&self, cell: ConstructorUsageCell) -> ConstructorUsages {
        self.constructor_usages[cell.0 as usize]
    }

    /// `check_usage loc id warn type_declarations` (env.ml:1562-1576) once the
    /// ghost/active guard passed: registers `(name, loc)` unless present.
    /// Returns the flag of a new registration.
    pub fn check_type_usage(&mut self, name: impl NameKey, loc: Location) -> Option<UsedCell> {
        let name = intern(name);
        if self.type_declarations.contains_key(&(name, loc)) {
            return None;
        }
        let cell = self.new_cell();
        self.type_declarations
            .insert((name, loc), TypeCallback::SetUsed(cell));
        Some(cell)
    }

    /// `check_usage loc id warn module_declarations`.
    pub fn check_module_usage(&mut self, name: impl NameKey, loc: Location) -> Option<UsedCell> {
        let name = intern(name);
        if self.module_declarations.contains_key(&(name, loc)) {
            return None;
        }
        let cell = self.new_cell();
        self.module_declarations
            .insert((name, loc), cell);
        Some(cell)
    }

    /// The constructor registration of `store_type`/`store_extension`
    /// (env.ml:1606-1620, 1650-1665).
    pub fn check_constructor_usage(
        &mut self,
        ty_name: impl NameKey,
        loc: Location,
        cstr_name: impl NameKey,
    ) -> Option<ConstructorUsageCell> {
        let ty_name = intern(ty_name);
        let cstr_name = intern(cstr_name);
        if self
            .used_constructors
            .contains_key(&(ty_name, loc, cstr_name))
        {
            return None;
        }
        self.constructor_usages.push(ConstructorUsages::default());
        let cell = ConstructorUsageCell(self.constructor_usages.len() as u32 - 1);
        self.used_constructors
            .insert((ty_name, loc, cstr_name), cell);
        Some(cell)
    }

    /// `Env.mark_type_used` (env.ml:1130-1133) without the implicit-coercion
    /// guard, which callers apply.
    pub fn mark_type_used(&mut self, name: impl NameKey, loc: Location) {
        let Some(name) = name.name_key() else {
            return;
        };
        let callback = match self.type_declarations.get(&(name, loc)) {
            None => return,
            // The common case needs only the cell; avoid cloning the chain.
            Some(TypeCallback::SetUsed(cell)) => {
                self.cells[cell.0 as usize] = true;
                return;
            }
            Some(callback) => callback.clone(),
        };
        self.run_type_callback(callback);
    }

    fn run_type_callback(&mut self, callback: TypeCallback) {
        match callback {
            TypeCallback::SetUsed(cell) => self.cells[cell.0 as usize] = true,
            TypeCallback::RecSlot {
                name,
                loc,
                slot,
                old,
            } => match self.current_type_slot {
                Some(current) => self.type_slots[current.0 as usize].push((name, loc)),
                None => {
                    // `List.iter mark_type_used (get_ref slot); old_callback ()`.
                    let recorded = std::mem::take(&mut self.type_slots[slot.0 as usize]);
                    for (name, loc) in recorded {
                        self.mark_type_used(name, loc);
                    }
                    self.run_type_callback(*old);
                }
            },
        }
    }

    /// `Env.set_type_used_callback name td` with the recursive-slot callback
    /// of typedecl.ml:1489-1496. Returns the new slot.
    pub fn set_type_rec_slot_callback(&mut self, name: impl NameKey, loc: Location) -> Option<TypeSlot> {
        let name = intern(name);
        if loc.loc_ghost {
            return None;
        }
        let key = (name, loc);
        let old = self.type_declarations.get(&key).cloned()?;
        self.type_slots.push(Vec::new());
        let slot = TypeSlot(self.type_slots.len() as u32 - 1);
        self.type_declarations.insert(
            key,
            TypeCallback::RecSlot {
                name,
                loc,
                slot,
                old: Box::new(old),
            },
        );
        Some(slot)
    }

    /// `current_slot := slot` in `Typedecl.transl_type_decl`.
    pub fn set_current_type_slot(&mut self, slot: Option<TypeSlot>) {
        self.current_type_slot = slot;
    }

    /// `Env.mark_module_used` (env.ml:996-998) without the implicit-coercion
    /// guard.
    pub fn mark_module_used(&mut self, name: impl NameKey, loc: Location) {
        let Some(name) = name.name_key() else {
            return;
        };
        if let Some(cell) = self.module_declarations.get(&(name, loc)) {
            self.cells[cell.0 as usize] = true;
        }
    }

    /// `Env.mark_constructor_used`/`mark_extension_used` (env.ml:1135-1144)
    /// without the implicit-coercion guard.
    pub fn mark_constructor_used(
        &mut self,
        usage: ConstructorUsage,
        ty_name: impl NameKey,
        loc: Location,
        cstr_name: impl NameKey,
    ) {
        let (Some(ty_name), Some(cstr_name)) = (ty_name.name_key(), cstr_name.name_key()) else {
            return;
        };
        if let Some(cell) = self
            .used_constructors
            .get(&(ty_name, loc, cstr_name))
        {
            let cu = &mut self.constructor_usages[cell.0 as usize];
            match usage {
                ConstructorUsage::Positive => cu.cu_positive = true,
                ConstructorUsage::Pattern => cu.cu_pattern = true,
                ConstructorUsage::Privatize => cu.cu_privatize = true,
            }
        }
    }
}
