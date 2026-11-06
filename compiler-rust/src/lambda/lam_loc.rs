//! Compact source-location handles for raw Lambda, Lambda and JS IR.
//!
//! OCaml stores a full `Location.t` in `lfunction.loc`, `ap_info.ap_loc`,
//! `Lprim.loc` (compiler/ml/lambda.mli:374-379, compiler/core/lam.mli) and
//! `J.expression.loc`/`J.statement.loc`, read by source maps
//! (compiler/core/lam_compile.ml:436, 1829) and backend diagnostics
//! (`Location.raise_errorf ~loc`). Rust keeps a 4-byte [`LamLoc`] handle in
//! those nodes and the coordinates in one per-compilation [`LamLocTable`]
//! that is owned explicitly by whoever owns the IR (the raw converter, the
//! pre-JS result, the JS backend, or an exported lambda collection).
//!
//! A location-free compilation uses an opaque table: every handle is
//! [`LamLoc::NONE`] and the table has no coordinate rows. Consumers that need
//! real coordinates ([`LamLocTable::get`] returns `None`) must request the
//! existing location-enabled retry instead of reporting a zero range.

use std::collections::HashMap;
use std::num::NonZeroU32;
use std::sync::Arc;

use ahash::AHashMap;

use crate::intern::StrIdx;
use crate::lambda::Lambda;
use crate::location::Location;

/// A location handle; resolve it through the [`LamLocTable`] that owns the
/// IR it appears in. `Option<LamLoc>` is four bytes as well.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct LamLoc {
    raw: NonZeroU32,
}

impl LamLoc {
    /// `Location.none`: no source position. Valid in every table.
    pub const NONE: LamLoc = LamLoc {
        raw: NonZeroU32::MIN,
    };

    /// Whether this is [`LamLoc::NONE`].
    #[inline]
    pub fn is_none(self) -> bool {
        self == Self::NONE
    }

    #[inline]
    fn row(self) -> Option<usize> {
        (self.raw.get() as usize).checked_sub(2)
    }

    #[inline]
    fn from_row(row: usize) -> Self {
        let raw = u32::try_from(row + 2).expect("Lambda location table overflow");
        LamLoc {
            raw: NonZeroU32::new(raw).expect("row handles are at least two"),
        }
    }

    /// A distinct handle for unit tests that only check handle propagation.
    #[cfg(test)]
    pub fn for_test(n: u32) -> Self {
        Self::from_row(n as usize)
    }
}

impl Default for LamLoc {
    fn default() -> Self {
        Self::NONE
    }
}

/// File names of imported rows live above this index so they never collide
/// with the recipient arena's own `StrIdx` values.
const IMPORTED_FILE_BASE: u32 = 0xC000_0000;

/// Per-compilation location side table for Lambda and JS IR handles.
#[derive(Clone, Debug, Default)]
pub struct LamLocTable {
    located: bool,
    rows: Vec<Location>,
    index: AHashMap<Location, LamLoc>,
    /// Source file names of the arena that produced the rows.
    file_names: Arc<HashMap<StrIdx, String>>,
    /// File names of rows rebased from another table, at
    /// `IMPORTED_FILE_BASE + i`.
    imported_files: Vec<String>,
    imported_file_index: AHashMap<String, StrIdx>,
}

impl LamLocTable {
    /// A table for a location-free compilation: it never stores coordinates
    /// and every handle it hands out is [`LamLoc::NONE`].
    pub fn opaque() -> Self {
        Self::default()
    }

    /// A table that stores full locations (diagnostic/tooling mode).
    pub fn located(file_names: Arc<HashMap<StrIdx, String>>) -> Self {
        Self {
            located: true,
            file_names,
            ..Self::default()
        }
    }

    /// Whether this table resolves handles to source coordinates.
    pub fn is_located(&self) -> bool {
        self.located
    }

    /// Number of coordinate rows (zero for an opaque table).
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Install the producing arena's source file names (located tables).
    pub fn set_file_names(&mut self, file_names: Arc<HashMap<StrIdx, String>>) {
        if self.located {
            self.file_names = file_names;
        }
    }

    /// Store `loc`, sharing the handle with an equal location already stored.
    pub fn intern(&mut self, loc: Location) -> LamLoc {
        if !self.located || loc == Location::none() {
            return LamLoc::NONE;
        }
        if let Some(&handle) = self.index.get(&loc) {
            return handle;
        }
        let handle = LamLoc::from_row(self.rows.len());
        self.rows.push(loc);
        self.index.insert(loc, handle);
        handle
    }

    /// The location of `handle`, or `None` when this table does not store
    /// coordinates (the caller must fall back to a located compilation).
    pub fn get(&self, handle: LamLoc) -> Option<Location> {
        if !self.located {
            return None;
        }
        Some(match handle.row() {
            None => Location::none(),
            Some(row) => self.rows[row],
        })
    }

    /// The source file name of a location resolved through this table.
    pub fn file_name(&self, idx: StrIdx) -> Option<&str> {
        if idx.0 >= IMPORTED_FILE_BASE {
            return self
                .imported_files
                .get((idx.0 - IMPORTED_FILE_BASE) as usize)
                .map(String::as_str);
        }
        self.file_names.get(&idx).map(String::as_str)
    }

    fn import_file(&mut self, src: &LamLocTable, idx: StrIdx) -> StrIdx {
        if idx == StrIdx::default() {
            return idx;
        }
        let Some(name) = src.file_name(idx) else {
            return StrIdx::default();
        };
        if let Some(&local) = self.imported_file_index.get(name) {
            return local;
        }
        let local = StrIdx(IMPORTED_FILE_BASE + self.imported_files.len() as u32);
        self.imported_files.push(name.to_string());
        self.imported_file_index.insert(name.to_string(), local);
        local
    }

    /// Rebase one handle of `src` into this table.
    pub fn import(&mut self, src: &LamLocTable, handle: LamLoc) -> LamLoc {
        let Some(mut loc) = src.get(handle) else {
            return LamLoc::NONE;
        };
        if !self.located || handle.is_none() {
            return LamLoc::NONE;
        }
        loc.loc_start.file_name = self.import_file(src, loc.loc_start.file_name);
        loc.loc_end.file_name = self.import_file(src, loc.loc_end.file_name);
        self.intern(loc)
    }

    /// Rebase every handle in `lam` (owned by `src`) into this table, so an
    /// imported lambda keeps its source locations after inlining.
    pub fn import_lambda(&mut self, src: &LamLocTable, lam: &mut Lambda) {
        if src.rows.is_empty() {
            // Every handle of a row-less table is `NONE`, valid everywhere.
            return;
        }
        for_each_loc_mut(lam, &mut |loc| *loc = self.import(src, *loc));
    }

    /// A compact table holding only the rows `lams` reference, with their
    /// handles rewritten into it: an exported lambda collection keeps its
    /// source locations without retaining the whole module's table.
    pub fn export_lambdas<'l>(&self, lams: impl IntoIterator<Item = &'l mut Lambda>) -> Self {
        if self.rows.is_empty() {
            return Self {
                located: self.located,
                ..Self::default()
            };
        }
        let mut out = Self::located(Arc::new(HashMap::new()));
        for lam in lams {
            for_each_loc_mut(lam, &mut |loc| *loc = out.import(self, *loc));
        }
        out
    }
}

/// The closed-lambda `.cmj` exports of one module (`persistent_closed_lambda`,
/// compiler/core/js_cmj_format.ml:112-121) with the table their location
/// handles resolve in. Read access derefs to the export map; inline through
/// [`CmjExportLambdas::import`] so the recipient owns the locations it keeps.
#[derive(Clone, Debug, Default)]
pub struct CmjExportLambdas {
    lambdas: AHashMap<String, Lambda>,
    locs: LamLocTable,
}

impl CmjExportLambdas {
    /// Pair exported lambdas with the table their handles resolve in.
    pub fn new(lambdas: AHashMap<String, Lambda>, locs: LamLocTable) -> Self {
        Self { lambdas, locs }
    }

    /// Exports whose handles are all [`LamLoc::NONE`] (decoded `.cmj`
    /// lambdas, location-free compilations).
    pub fn without_locations(lambdas: AHashMap<String, Lambda>) -> Self {
        Self::new(lambdas, LamLocTable::opaque())
    }

    /// Compact `lambdas` (whose handles resolve in `locs`) into an export
    /// collection that owns only the rows they reference.
    pub fn export(mut lambdas: AHashMap<String, Lambda>, locs: &LamLocTable) -> Self {
        let mut names: Vec<&String> = lambdas.keys().collect();
        names.sort();
        let names: Vec<String> = names.into_iter().cloned().collect();
        let mut ordered: Vec<(String, Lambda)> = names
            .into_iter()
            .map(|name| {
                let lam = lambdas.remove(&name).expect("export name");
                (name, lam)
            })
            .collect();
        let table = locs.export_lambdas(ordered.iter_mut().map(|(_, lam)| lam));
        Self::new(ordered.into_iter().collect(), table)
    }

    /// The table the exported handles resolve in.
    pub fn locs(&self) -> &LamLocTable {
        &self.locs
    }

    pub fn into_parts(self) -> (AHashMap<String, Lambda>, LamLocTable) {
        (self.lambdas, self.locs)
    }

    /// A copy of export `name` with its handles rebased into `into`.
    pub fn import(&self, name: &str, into: &mut LamLocTable) -> Option<Lambda> {
        let mut lam = self.lambdas.get(name)?.clone();
        into.import_lambda(&self.locs, &mut lam);
        Some(lam)
    }
}

impl std::ops::Deref for CmjExportLambdas {
    type Target = AHashMap<String, Lambda>;

    fn deref(&self) -> &Self::Target {
        &self.lambdas
    }
}

impl FromIterator<(String, Lambda)> for CmjExportLambdas {
    fn from_iter<I: IntoIterator<Item = (String, Lambda)>>(iter: I) -> Self {
        Self::without_locations(iter.into_iter().collect())
    }
}

/// Persistent form of a [`LamLocTable`] (stored closed-lambda metadata keeps
/// its locations). Entries are in a canonical order so equal tables encode
/// identically.
#[derive(serde::Serialize, serde::Deserialize)]
struct StoredLamLocTable {
    located: bool,
    rows: Vec<Location>,
    file_names: Vec<(StrIdx, String)>,
    imported_files: Vec<String>,
}

impl serde::Serialize for LamLocTable {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut file_names: Vec<(StrIdx, String)> = self
            .file_names
            .iter()
            .map(|(idx, name)| (*idx, name.clone()))
            .collect();
        file_names.sort_unstable_by_key(|(idx, _)| idx.0);
        StoredLamLocTable {
            located: self.located,
            rows: self.rows.clone(),
            file_names,
            imported_files: self.imported_files.clone(),
        }
        .serialize(serializer)
    }
}

impl<'de> serde::Deserialize<'de> for LamLocTable {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let stored = StoredLamLocTable::deserialize(deserializer)?;
        let index = stored
            .rows
            .iter()
            .enumerate()
            .map(|(row, loc)| (*loc, LamLoc::from_row(row)))
            .collect();
        let imported_file_index = stored
            .imported_files
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), StrIdx(IMPORTED_FILE_BASE + i as u32)))
            .collect();
        Ok(Self {
            located: stored.located,
            rows: stored.rows,
            index,
            file_names: Arc::new(stored.file_names.into_iter().collect()),
            imported_files: stored.imported_files,
            imported_file_index,
        })
    }
}

impl serde::Serialize for CmjExportLambdas {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut entries: Vec<(&String, &Lambda)> = self.lambdas.iter().collect();
        entries.sort_unstable_by(|a, b| a.0.cmp(b.0));
        let mut out = serializer.serialize_struct("CmjExportLambdas", 2)?;
        out.serialize_field("lambdas", &entries)?;
        out.serialize_field("locs", &self.locs)?;
        out.end()
    }
}

impl<'de> serde::Deserialize<'de> for CmjExportLambdas {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(serde::Deserialize)]
        struct Stored {
            lambdas: Vec<(String, Lambda)>,
            locs: LamLocTable,
        }
        let stored = Stored::deserialize(deserializer)?;
        Ok(Self::new(stored.lambdas.into_iter().collect(), stored.locs))
    }
}

/// Visit every location handle stored in `lam`.
pub fn for_each_loc_mut(lam: &mut Lambda, f: &mut impl FnMut(&mut LamLoc)) {
    match lam {
        Lambda::Lvar(_)
        | Lambda::LglobalModule(_)
        | Lambda::Lconst(_)
        | Lambda::Lbreak
        | Lambda::Lcontinue => {}
        Lambda::Lapply(ap) => {
            f(&mut ap.ap_info.loc);
            for_each_loc_mut(&mut ap.ap_func, f);
            for arg in &mut ap.ap_args {
                for_each_loc_mut(arg, f);
            }
        }
        Lambda::Lfunction(func) => {
            f(&mut func.loc);
            for_each_loc_mut(&mut func.body, f);
        }
        Lambda::Llet(_, _, arg, body) => {
            for_each_loc_mut(arg, f);
            for_each_loc_mut(body, f);
        }
        Lambda::Lletrec(decl, body) => {
            for (_, e) in decl {
                for_each_loc_mut(e, f);
            }
            for_each_loc_mut(body, f);
        }
        Lambda::Lprim(prim) => {
            f(&mut prim.loc);
            for arg in &mut prim.args {
                for_each_loc_mut(arg, f);
            }
        }
        Lambda::Lswitch(arg, sw) => {
            for_each_loc_mut(arg, f);
            for (_, e) in &mut sw.sw_consts {
                for_each_loc_mut(e, f);
            }
            for (_, e) in &mut sw.sw_blocks {
                for_each_loc_mut(e, f);
            }
            if let Some(e) = &mut sw.sw_failaction {
                for_each_loc_mut(e, f);
            }
        }
        Lambda::LstringSwitch(arg, cases, default) => {
            for_each_loc_mut(arg, f);
            for (_, e) in cases {
                for_each_loc_mut(e, f);
            }
            if let Some(e) = default {
                for_each_loc_mut(e, f);
            }
        }
        Lambda::LstaticRaise(_, args) => {
            for e in args {
                for_each_loc_mut(e, f);
            }
        }
        Lambda::LstaticCatch(e1, _, e2)
        | Lambda::LtryWith(e1, _, e2)
        | Lambda::LtryFinally(e1, e2)
        | Lambda::Lsequence(e1, e2)
        | Lambda::Lwhile(e1, e2)
        | Lambda::Lfor_of(_, e1, e2)
        | Lambda::Lfor_await_of(_, e1, e2) => {
            for_each_loc_mut(e1, f);
            for_each_loc_mut(e2, f);
        }
        Lambda::LifThenElse(e1, e2, e3) | Lambda::Lfor(_, e1, e2, _, e3) => {
            for_each_loc_mut(e1, f);
            for_each_loc_mut(e2, f);
            for_each_loc_mut(e3, f);
        }
        Lambda::Lassign(_, e) => for_each_loc_mut(e, f),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::location::Position;

    fn loc(file: u32, line: i32) -> Location {
        Location::from_positions(
            Position::new(StrIdx(file), line, 0, 4),
            Position::new(StrIdx(file), line, 0, 9),
        )
    }

    #[test]
    fn handles_are_four_bytes() {
        assert_eq!(std::mem::size_of::<LamLoc>(), 4);
        assert_eq!(std::mem::size_of::<Option<LamLoc>>(), 4);
    }

    #[test]
    fn opaque_tables_store_no_coordinates() {
        let mut table = LamLocTable::opaque();
        assert_eq!(table.intern(loc(3, 7)), LamLoc::NONE);
        assert!(table.is_empty());
        assert_eq!(table.get(LamLoc::NONE), None);
    }

    #[test]
    fn located_tables_dedup_and_resolve() {
        let mut table = LamLocTable::located(Arc::new(HashMap::new()));
        let a = table.intern(loc(3, 7));
        assert_eq!(table.intern(loc(3, 7)), a);
        let b = table.intern(loc(3, 8));
        assert_ne!(a, b);
        assert_eq!(table.intern(Location::none()), LamLoc::NONE);
        assert_eq!(table.len(), 2);
        assert_eq!(table.get(a), Some(loc(3, 7)));
        assert_eq!(table.get(LamLoc::NONE), Some(Location::none()));
    }

    #[test]
    fn imports_rebase_rows_and_file_names() {
        let mut exporter =
            LamLocTable::located(Arc::new(HashMap::from([(StrIdx(3), "A.res".to_string())])));
        let mut lam = Lambda::prim(
            crate::lambda::Primitive::Praise,
            vec![Lambda::var(crate::ident::Ident::create_local("x"))],
            exporter.intern(loc(3, 7)),
        );
        // Exporting compacts the table; the exporter's own table can go away.
        let exported = exporter.export_lambdas([&mut lam]);
        drop(exporter);
        assert_eq!(exported.len(), 1);

        let mut recipient =
            LamLocTable::located(Arc::new(HashMap::from([(StrIdx(3), "B.res".to_string())])));
        let own = recipient.intern(loc(3, 1));
        recipient.import_lambda(&exported, &mut lam);
        let Lambda::Lprim(info) = &lam else {
            panic!("expected a primitive");
        };
        assert_ne!(info.loc, own);
        let resolved = recipient.get(info.loc).expect("located");
        assert_eq!(resolved.loc_start.line, 7);
        assert_eq!(recipient.file_name(resolved.file_name_idx()), Some("A.res"));
        assert_eq!(recipient.file_name(StrIdx(3)), Some("B.res"));

        // A location-free recipient keeps no rows.
        let mut opaque = LamLocTable::opaque();
        let mut copy = lam.clone();
        opaque.import_lambda(&recipient, &mut copy);
        assert!(opaque.is_empty());
    }
}
