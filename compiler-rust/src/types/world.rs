//! The world of one build: everything every worker of the build reads and
//! none of them writes (docs/CHECKER_REDESIGN.md, J.3).
//!
//! OCaml keeps one `persistent_structures` table per process
//! (`compiler/ml/env.ml:669-678`). An in-process build checks many units on
//! several threads, so what OCaml keeps in that table lives here, once per
//! build generation:
//!
//! - the frozen pool (`types/shared_store.rs`): immutable type graphs, each
//!   complete before its pages are published;
//! - the unit table: one slot per dependency unit, holding the unit's
//!   internalized signature and the name index of that signature.
//!
//! Every cross-thread write is a `OnceLock::set` of a complete value or a
//! short `Mutex` section around a hash table.

use super::decl::Signature;
use super::env_lazy::SignatureIndex;
use super::shared_store::SharedTypePool;
use crate::cmi::persistent_env::PersStruct;
use crate::cmi::portable_types::PortablePersStruct;
use crate::fast_hash::AHashMap;
use std::sync::{Arc, Mutex, OnceLock};

/// One unit of the build, internalized into the frozen pool.
pub(crate) struct UnitSlot {
    /// Keeps the portable struct alive so its address cannot be reused as a
    /// key for another unit.
    _owner: Arc<PortablePersStruct>,
    /// `None` when the unit's graph could not be placed in the pool.
    ps: OnceLock<Option<Arc<PersStruct>>>,
    /// Name index of `ps.ps_sig`, built by the first worker that asks.
    index: OnceLock<Arc<SignatureIndex>>,
}

/// One per build generation; workers and contexts hold `Arc<World>`.
pub(crate) struct World {
    generation: u64,
    pool: SharedTypePool,
    /// Units internalized in this build, by the identity of their stored
    /// form.
    units: Mutex<AHashMap<usize, Arc<UnitSlot>>>,
    /// The same slots by the address of the internalized signature (kept
    /// alive by the slot), for a reader that holds only the signature.
    unit_signatures: Mutex<AHashMap<usize, Arc<UnitSlot>>>,
}

const fn assert_send_sync<T: Send + Sync>() {}
const _: () = assert_send_sync::<World>();

static CURRENT: Mutex<Option<Arc<World>>> = Mutex::new(None);

#[cfg(test)]
thread_local! {
    /// Hash probes of the unit table made by this thread.
    static UNIT_TABLE_PROBES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[inline]
fn count_unit_probe() {
    #[cfg(test)]
    UNIT_TABLE_PROBES.with(|probes| probes.set(probes.get() + 1));
}

impl World {
    fn new(generation: u64) -> Self {
        World {
            generation,
            pool: SharedTypePool::new(),
            units: Mutex::new(AHashMap::new()),
            unit_signatures: Mutex::new(AHashMap::new()),
        }
    }

    /// The world of the current build generation
    /// (`thread_store::build_generation`). The world of an earlier build is
    /// replaced, and freed once the last worker holding it lets go.
    pub(crate) fn current() -> Arc<World> {
        let generation = super::thread_store::build_generation();
        let mut slot = CURRENT.lock().unwrap();
        match &*slot {
            Some(world) if world.generation == generation => world.clone(),
            _ => {
                let world = Arc::new(World::new(generation));
                *slot = Some(world.clone());
                world
            }
        }
    }

    /// The frozen pool.
    #[inline]
    pub(crate) fn pool(&self) -> &SharedTypePool {
        &self.pool
    }

    /// The internalization of unit `pps`, built with `build` the first time
    /// any worker asks. Concurrent requests for one unit wait for the first
    /// builder. `None` when `build` could not place the graph in the pool.
    ///
    /// One hash probe, whatever the number of units.
    pub(crate) fn unit(
        &self,
        pps: &Arc<PortablePersStruct>,
        build: impl FnOnce() -> Option<Arc<PersStruct>>,
    ) -> Option<Arc<PersStruct>> {
        count_unit_probe();
        let slot = self
            .units
            .lock()
            .unwrap()
            .entry(Arc::as_ptr(pps) as usize)
            .or_insert_with(|| {
                Arc::new(UnitSlot {
                    _owner: pps.clone(),
                    ps: OnceLock::new(),
                    index: OnceLock::new(),
                })
            })
            .clone();
        slot.ps
            .get_or_init(|| {
                let ps = build()?;
                self.unit_signatures
                    .lock()
                    .unwrap()
                    .insert(Arc::as_ptr(&ps.ps_sig) as usize, slot.clone());
                Some(ps)
            })
            .clone()
    }

    fn unit_of_signature(&self, sig: &Arc<Signature>) -> Option<Arc<UnitSlot>> {
        count_unit_probe();
        self.unit_signatures
            .lock()
            .unwrap()
            .get(&(Arc::as_ptr(sig) as usize))
            .cloned()
    }

    /// Whether `sig` is the signature of a unit of this world: its items are
    /// frozen and keep one address for the whole build.
    pub(crate) fn is_unit_signature(&self, sig: &Arc<Signature>) -> bool {
        self.unit_of_signature(sig).is_some()
    }

    /// The name index of a unit's signature, built once per build; `None`
    /// when `sig` is no unit's signature. One hash probe, whatever the number
    /// of units.
    pub(crate) fn unit_signature_index(&self, sig: &Arc<Signature>) -> Option<Arc<SignatureIndex>> {
        let slot = self.unit_of_signature(sig)?;
        Some(
            slot.index
                .get_or_init(|| Arc::new(SignatureIndex::build(sig)))
                .clone(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::types::context::TypeContext;
    use std::sync::atomic::{AtomicUsize, Ordering};

    fn unit_probes() -> u64 {
        UNIT_TABLE_PROBES.with(|probes| probes.get())
    }

    fn pers_struct(name: &str) -> PersStruct {
        PersStruct {
            ps_name: name.into(),
            ps_sig: Arc::new(vec![]),
            ps_filename: format!("{name}.res"),
            ps_deprecated: None,
            ps_crcs: vec![],
            ps_alias_rewrites: Default::default(),
        }
    }

    /// `count` units registered in a fresh world, with their signatures.
    fn world_with_units(
        ctx: &TypeContext,
        count: usize,
    ) -> (World, Vec<(Arc<PortablePersStruct>, Arc<Signature>)>) {
        let world = World::new(u64::MAX);
        let units = (0..count)
            .map(|i| {
                let ps = pers_struct(&format!("Unit{i}"));
                let pps = Arc::new(crate::cmi::portable_types::serialize_pers_struct(
                    &ps, ctx, None,
                ));
                let ps = world.unit(&pps, || Some(Arc::new(ps))).unwrap();
                (pps, ps.ps_sig.clone())
            })
            .collect();
        (world, units)
    }

    #[test]
    fn unit_is_internalized_once_for_all_threads() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let world = Arc::new(World::new(u64::MAX));
        let pps = Arc::new(crate::cmi::portable_types::serialize_pers_struct(
            &pers_struct("Shared"),
            &ctx,
            None,
        ));
        let builds = Arc::new(AtomicUsize::new(0));
        let barrier = Arc::new(std::sync::Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let (world, pps, builds, barrier) =
                    (world.clone(), pps.clone(), builds.clone(), barrier.clone());
                std::thread::spawn(move || {
                    barrier.wait();
                    world
                        .unit(&pps, || {
                            builds.fetch_add(1, Ordering::SeqCst);
                            Some(Arc::new(pers_struct("Shared")))
                        })
                        .unwrap()
                })
            })
            .collect();
        let units: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        assert_eq!(builds.load(Ordering::SeqCst), 1);
        for unit in &units {
            assert!(Arc::ptr_eq(unit, &units[0]));
            assert!(world.is_unit_signature(&unit.ps_sig));
        }
        let index = world.unit_signature_index(&units[0].ps_sig).unwrap();
        assert!(Arc::ptr_eq(
            &index,
            &world.unit_signature_index(&units[0].ps_sig).unwrap()
        ));
        assert!(
            world
                .unit_signature_index(&Arc::new(Signature::new()))
                .is_none()
        );
    }

    /// Step count: a unit lookup is one hash probe whether the world holds
    /// ten units or five thousand.
    #[test]
    fn unit_lookups_cost_one_probe_whatever_the_number_of_units() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let mut steps = Vec::new();
        for count in [10, 5_000] {
            let (world, units) = world_with_units(&ctx, count);
            let (pps, sig) = &units[count / 2];
            let before = unit_probes();
            world
                .unit(pps, || panic!("the unit is already internalized"))
                .unwrap();
            let by_unit = unit_probes() - before;
            let before = unit_probes();
            world.unit_signature_index(sig).unwrap();
            let by_signature = unit_probes() - before;
            let before = unit_probes();
            assert!(!world.is_unit_signature(&Arc::new(Signature::new())));
            let miss = unit_probes() - before;
            steps.push((by_unit, by_signature, miss));
        }
        assert_eq!(steps, [(1, 1, 1), (1, 1, 1)]);
    }

    /// Step count: a compilation asks the world for a signature's index
    /// once; later requests do not reach the unit table.
    #[test]
    fn a_compilation_reads_a_unit_index_from_the_world_once() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let ps = pers_struct("Indexed");
        let pps = Arc::new(crate::cmi::portable_types::serialize_pers_struct(
            &ps, &ctx, None,
        ));
        let ps = ctx.world().unit(&pps, || Some(Arc::new(ps))).unwrap();
        let before = unit_probes();
        let first = ctx.signature_index(&ps.ps_sig);
        assert_eq!(unit_probes() - before, 1);
        let before = unit_probes();
        for _ in 0..100 {
            assert!(Arc::ptr_eq(&first, &ctx.signature_index(&ps.ps_sig)));
        }
        assert_eq!(unit_probes() - before, 0);
        assert!(Arc::ptr_eq(
            &first,
            &ctx.world().unit_signature_index(&ps.ps_sig).unwrap()
        ));
    }
}
