//! Tests of the environment log: the cost of every operation in counted
//! steps, the module seam, and the property test against today's `Env`
//! (docs/CHECKER_REDESIGN.md F.8 and H.2.8 step 4).

use super::*;
use crate::context::IdGenerator;
use crate::ident::IdentFlags;
use crate::types::decl::{AliasPresence, LabelArrayRef, RecStatus, ValueKind};
use crate::types::env_lazy::StoredModuleComponents;
use crate::types::variance::Variance;

// ============================================================================
// Payloads, told apart by a number
// ============================================================================

fn value(n: u32) -> ValueDescription {
    ValueDescription {
        val_type: TypeExprRef(n),
        val_kind: ValueKind::ValReg,
        val_loc: crate::types::DeclLoc::none(),
        val_attributes: Default::default(),
        val_path: None,
    }
}

fn type_decl(n: u32) -> TypeDeclaration {
    TypeDeclaration {
        type_params: vec![],
        type_arity: n as i32,
        type_kind: TypeKind::TypeAbstract,
        type_private: PrivateFlag::Public,
        type_manifest: None,
        type_variance: vec![],
        type_newtype_level: None,
        type_loc: crate::types::DeclLoc::none(),
        type_attributes: vec![],
        type_immediate: false,
        type_representation: crate::types::TypeRepresentation::Boxed,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path: None,
    }
}

fn module_of(md_type: ModuleType) -> ModuleDeclaration {
    ModuleDeclaration {
        md_type,
        md_attributes: vec![],
        md_loc: crate::types::DeclLoc::none(),
        md_path: None,
    }
}

fn modtype(n: u32) -> ModtypeDeclaration {
    ModtypeDeclaration {
        mtd_type: Some(ModuleType::MtySignature(Arc::new(vec![
            SignatureItem::SigType(
                Ident::new("t", 900, IdentFlags::NONE),
                Arc::new(type_decl(n)),
                RecStatus::TrecNot,
            ),
        ]))),
        mtd_attributes: vec![],
        mtd_loc: crate::types::DeclLoc::none(),
    }
}

/// A signature with a type `a`, a submodule `B` and a module type `C`, so
/// that dotted paths have something to find.
fn signature(n: u32) -> ModuleType {
    ModuleType::MtySignature(Arc::new(vec![
        SignatureItem::SigType(
            Ident::new("a", 901, IdentFlags::NONE),
            Arc::new(type_decl(n)),
            RecStatus::TrecNot,
        ),
        SignatureItem::SigModule(
            Ident::new("B", 902, IdentFlags::NONE),
            module_of(ModuleType::MtySignature(Arc::new(vec![
                SignatureItem::SigType(
                    Ident::new("a", 903, IdentFlags::NONE),
                    Arc::new(type_decl(n + 1)),
                    RecStatus::TrecNot,
                ),
            ]))),
            RecStatus::TrecNot,
        ),
        SignatureItem::SigModtype(Ident::new("C", 904, IdentFlags::NONE), modtype(n)),
    ]))
}

// ============================================================================
// Costs, in counted steps
// ============================================================================

fn local(name: &str, stamp: i32) -> Ident {
    Ident::new(name, stamp, IdentFlags::NONE)
}

/// The counters of one log, read in one go.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
struct Counted {
    probes: u64,
    chain: u64,
    open_probes: u64,
    ancestors: u64,
    moved: u64,
    moves: u64,
    appended: u64,
    walked: u64,
}

fn counted(env: &LogEnv) -> Counted {
    let steps = &env.log().steps;
    Counted {
        probes: steps.probes.get(),
        chain: steps.chain.get(),
        open_probes: steps.open_probes.get(),
        ancestors: steps.ancestors.get(),
        moved: steps.moved.get(),
        moves: steps.moves.get(),
        appended: steps.appended.get(),
        walked: steps.walked.get(),
    }
}

/// The steps `work` adds to the log of `env`.
fn cost(env: &LogEnv, work: impl FnOnce()) -> Counted {
    let before = counted(env);
    work();
    let after = counted(env);
    Counted {
        probes: after.probes - before.probes,
        chain: after.chain - before.chain,
        open_probes: after.open_probes - before.open_probes,
        ancestors: after.ancestors - before.ancestors,
        moved: after.moved - before.moved,
        moves: after.moves - before.moves,
        appended: after.appended - before.appended,
        walked: after.walked - before.walked,
    }
}

/// A log of its own with `count` values `v0`, `v1`, ... bound in a row.
fn chain_of_values(count: u32) -> LogEnv {
    let mut env = LogEnv::empty();
    for n in 0..count {
        env.add_value(local(&format!("v{n}"), n as i32 + 1), value(n));
    }
    env
}

fn opened_values(prefix: &str, count: u32) -> OpenedLayers {
    OpenedLayers::build(
        (0..count)
            .map(|n| {
                (
                    local(&format!("{prefix}{n}"), 5_000 + n as i32),
                    value(n),
                    n as i32,
                )
            })
            .collect(),
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
    )
}

fn root(name: &str) -> Path {
    Path::pident(Ident::create_persistent(name))
}

#[test]
fn bind_is_one_probe_and_one_push_whatever_the_size() {
    let env = chain_of_values(100_000);
    assert_eq!(
        counted(&env),
        Counted {
            probes: 100_000,
            appended: 100_000,
            ..Counted::default()
        }
    );
}

#[test]
fn lookup_at_the_tip_is_one_probe() {
    let env = chain_of_values(100_000);
    let names: Vec<Name> = (0..1_000)
        .map(|n| Name::new(&format!("v{}", n * 100)))
        .collect();
    let used = cost(&env, || {
        for _ in 0..100 {
            for name in &names {
                assert!(env.find_value(*name).is_ok());
            }
        }
        assert!(env.find_value("never bound").is_err());
        assert!(env.find_value(Name::new("unbound")).is_err());
    });
    // A name that was never interned is in no table: no probe at all.
    assert_eq!(
        used,
        Counted {
            probes: 100_001,
            ..Counted::default()
        }
    );
}

#[test]
fn lookup_at_an_older_version_on_the_path_skips_the_newer_bindings_of_the_name() {
    let mut env = LogEnv::empty();
    env.add_value(local("x", 1), value(1));
    let old = env.clone();
    for n in 2..=100 {
        env.add_value(local("x", n), value(n as u32));
        env.add_value(local("y", 1_000 + n), value(0));
    }
    let used = cost(&env, || {
        assert_eq!(old.find_value("x").unwrap().val_type, TypeExprRef(1));
    });
    assert_eq!(
        used,
        Counted {
            probes: 1,
            chain: 99,
            ..Counted::default()
        }
    );
    // By identifier: one step per binding of the name examined.
    let used = cost(&env, || {
        assert_eq!(
            env.lookup_value(&Path::pident(local("x", 1)))
                .unwrap()
                .val_type,
            TypeExprRef(1)
        );
    });
    assert_eq!(
        used,
        Counted {
            probes: 1,
            chain: 100,
            ..Counted::default()
        }
    );
}

#[test]
fn moving_the_path_costs_the_distance_through_the_common_ancestor() {
    let mut main = chain_of_values(100_000);
    let fork = main.clone();
    for n in 0..10 {
        main.add_value(local("m", 200_000 + n), value(1));
    }
    // Extending the fork undoes the ten entries above it: nothing else.
    let mut side = fork.clone();
    let used = cost(&main, || side.add_value(local("s", 300_000), value(2)));
    assert_eq!(
        used,
        Counted {
            probes: 1,
            moved: 10,
            moves: 1,
            appended: 1,
            ..Counted::default()
        }
    );
    for n in 1..7 {
        side.add_value(local("s", 300_000 + n), value(2));
    }
    // Back to the main branch: 7 undone, 10 passed and redone.
    let used = cost(&main, || {
        assert_eq!(main.find_value("m").unwrap().val_type, TypeExprRef(1));
    });
    assert_eq!(
        used,
        Counted {
            probes: 1,
            ancestors: 10,
            moved: 17,
            moves: 1,
            ..Counted::default()
        }
    );
    // The fork is on the path of both branches: no move.
    let used = cost(&main, || {
        assert!(fork.find_value("s").is_err());
        assert!(fork.find_value("v99999").is_ok());
    });
    assert_eq!(
        used,
        Counted {
            probes: 2,
            chain: 0,
            ..Counted::default()
        }
    );
}

#[test]
fn a_clone_costs_no_step_and_keeps_its_version() {
    let mut env = chain_of_values(1_000);
    let used = cost(&env, || {
        let clones: Vec<LogEnv> = (0..10_000).map(|_| env.clone()).collect();
        assert!(clones.iter().all(|clone| clone.id() == env.id()));
    });
    assert_eq!(used, Counted::default());
    let retained = env.clone();
    env.add_value(local("v0", 9_000), value(77));
    assert_eq!(retained.find_value("v0").unwrap().val_type, TypeExprRef(0));
    assert_eq!(env.find_value("v0").unwrap().val_type, TypeExprRef(77));
    assert_ne!(retained.id(), env.id());
    assert_eq!(retained.scope_id(), env.scope_id());
}

#[test]
fn an_open_is_one_entry_and_one_step_to_cross_whatever_its_size() {
    let layers = opened_values("o", 1_000);
    let mut env = chain_of_values(10);
    let before = env.clone();
    let used = cost(&env.clone(), || {
        env.add_prebuilt_open_layers(root("M"), &layers, Some(3))
    });
    assert_eq!(
        used,
        Counted {
            appended: 1,
            ..Counted::default()
        }
    );
    // Through the open: the probe that misses locally, and one of the open.
    let used = cost(&env, || {
        let (path, desc) = env.find_value_arc_with_path("o999").unwrap();
        assert_eq!(path, Path::pdot_pos(root("M"), "o999", 999));
        assert_eq!(desc.val_type, TypeExprRef(999));
    });
    assert_eq!(
        used,
        Counted {
            probes: 1,
            open_probes: 1,
            ..Counted::default()
        }
    );
    // A local binding made after the open: the open is not consulted.
    env.add_value(local("o999", 7_000), value(5));
    let used = cost(&env, || {
        assert_eq!(env.find_value("o999").unwrap().val_type, TypeExprRef(5));
    });
    assert_eq!(
        used,
        Counted {
            probes: 1,
            ..Counted::default()
        }
    );
    // Switching to the version before the open undoes two entries, not 1,000
    // names; switching back redoes two.
    let mut branch = before.clone();
    let used = cost(&env, || branch.add_value(local("b", 7_001), value(6)));
    assert_eq!(
        used,
        Counted {
            probes: 1,
            moved: 2,
            moves: 1,
            appended: 1,
            ..Counted::default()
        }
    );
    let used = cost(&env, || assert!(env.find_value("o1").is_ok()));
    assert_eq!(
        used,
        Counted {
            probes: 1,
            open_probes: 1,
            ancestors: 2,
            moved: 3,
            moves: 1,
            ..Counted::default()
        }
    );
}

#[test]
fn a_lookup_probes_only_the_opens_newer_than_the_binding_that_have_the_table() {
    let mut env = LogEnv::empty();
    env.add_value(local("early", 1), value(1));
    // Five opens with values, five with types only.
    for n in 0..5 {
        env.add_prebuilt_open_layers(root("M"), &opened_values(&format!("m{n}_"), 3), None);
        let types = OpenedLayers::build(
            vec![],
            vec![(local("t", 50 + n), Arc::new(type_decl(n as u32)))],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
        );
        env.add_prebuilt_open_layers(root("T"), &types, None);
    }
    env.add_value(local("late", 2), value(2));
    let used = cost(&env, || assert!(env.find_value("late").is_ok()));
    assert_eq!(
        used,
        Counted {
            probes: 1,
            ..Counted::default()
        }
    );
    let used = cost(&env, || assert!(env.find_value("early").is_ok()));
    assert_eq!(
        used,
        Counted {
            probes: 1,
            open_probes: 5,
            ..Counted::default()
        }
    );
    // All candidates: one step per candidate and per open with the table.
    let used = cost(&env, || assert!(env.find_all_labels("early").is_empty()));
    assert_eq!(
        used,
        Counted {
            probes: 1,
            ..Counted::default()
        }
    );
}

#[test]
fn the_other_operations_cost_what_they_say() {
    let mut env = chain_of_values(1_000);
    let id = local("t", 5_000);
    // A type binding: the family lookup, then the entry.
    let used = cost(&env.clone(), || env.add_type(id, type_decl(1)));
    assert_eq!(
        used,
        Counted {
            probes: 2,
            appended: 1,
            ..Counted::default()
        }
    );
    let used = cost(&env.clone(), || {
        env.add_type_label_family(id, LabelArrayRef(4))
    });
    assert_eq!(
        used,
        Counted {
            probes: 1,
            appended: 1,
            ..Counted::default()
        }
    );
    // Re-binding the type removes the family with a second entry.
    let used = cost(&env.clone(), || env.add_type(id, type_decl(2)));
    assert_eq!(
        used,
        Counted {
            probes: 3,
            chain: 1,
            appended: 2,
            ..Counted::default()
        }
    );
    assert_eq!(env.type_label_family(&id), None);
    // Replacing a value: one resolution and one entry.
    let used = cost(&env.clone(), || {
        assert!(env.update_value_type_by_name("v7", TypeExprRef(70)))
    });
    assert_eq!(
        used,
        Counted {
            probes: 2,
            appended: 1,
            ..Counted::default()
        }
    );
    // Scope identity and flags are fields: no step.
    let used = cost(&env, || {
        let _ = (
            env.scope_id(),
            env.id(),
            env.has_local_constraints(),
            env.is_implicit_coercion(),
        );
        assert!(env.find_local_constraint(&Path::pident(id)).is_none());
    });
    assert_eq!(used, Counted::default());
    // A module: one entry.
    let used = cost(&env.clone(), || {
        env.add_module(local("M", 5_001), module_of(signature(1)))
    });
    assert_eq!(
        used,
        Counted {
            probes: 1,
            appended: 1,
            ..Counted::default()
        }
    );
    // Iteration walks the path once.
    let used = cost(&env, || assert_eq!(env.iter_values().count(), 1_000));
    assert_eq!(used.walked, 1_006);
    assert_eq!(used.probes + used.moved, 0);
}

// ============================================================================
// The module seam
// ============================================================================

#[test]
fn a_component_seed_is_the_version_before_the_binding_and_owns_nothing() {
    let mut env = LogEnv::empty();
    env.add_value(local("x", 1), value(1));
    let id = local("M", 2);
    env.add_module(id, module_of(signature(1)));
    env.add_value(local("x", 3), value(3));
    let thunk = env
        .local_module_components_shared(&Path::pident(id))
        .unwrap();
    let seed = thunk.seed.env().expect("the log is alive");
    assert_eq!(seed.find_value("x").unwrap().val_type, TypeExprRef(1));
    assert!(seed.find_module("M").is_err());
    assert!(seed.same_log(&env));
    // Forcing forks inside the seed's own log and owns no log.
    let (mut working, owned) = LogEnv::component_working_env(&seed);
    assert!(owned.is_none());
    working.add_type(local("t", 4), type_decl(1));
    assert!(env.find_type("t").is_err());
    // The log holds the thunk and the thunk names the log: without a weak
    // seed that is a cycle and the log would never be freed.
    let log = Rc::downgrade(&env.log);
    drop((env, seed, working));
    assert!(thunk.seed.env().is_none());
    assert_eq!(log.strong_count(), 0);
}

#[test]
fn a_frozen_log_is_extended_in_a_new_log_based_on_it() {
    let mut initial = LogEnv::empty();
    initial.add_type(local("int", 1), type_decl(1));
    initial.add_value(local("x", 2), value(1));
    initial.freeze();
    let mut first = initial.clone();
    assert_eq!(first.id(), initial.id());
    first.add_value(local("x", 3), value(2));
    let mut second = initial.clone();
    second.add_module(local("M", 4), module_of(signature(1)));
    assert!(!first.same_log(&initial) && !second.same_log(&first));
    assert_eq!(initial.log().entries.len(), 2);
    assert_eq!(first.find_value("x").unwrap().val_type, TypeExprRef(2));
    assert_eq!(second.find_value("x").unwrap().val_type, TypeExprRef(1));
    assert!(first.find_type("int").is_ok());
    assert_eq!(first.scope_id(), initial.scope_id());
    assert_ne!(second.scope_id(), initial.scope_id());
    // A table built from a frozen seed owns the log it starts.
    let (mut working, owned) = LogEnv::component_working_env(&initial);
    assert!(owned.is_some());
    working.add_type(local("t", 5), type_decl(3));
    assert!(working.find_type("int").is_ok());
    assert!(initial.find_type("t").is_err());
}

#[test]
fn store_type_binds_the_labels_of_a_record_last_field_first() {
    let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
    let field = |name: &str, stamp| crate::types::decl::LabelDeclaration {
        ld_id: local(name, stamp),
        ld_runtime_name: None,
        ld_mutable: crate::types::MutableFlag::Immutable,
        ld_optional: false,
        ld_type: TypeExprRef(0),
        ld_loc: crate::types::DeclLoc::none(),
        ld_attributes: vec![],
    };
    let mut decl = type_decl(0);
    decl.type_kind = TypeKind::TypeRecord(
        vec![field("first", 11), field("second", 12)].into(),
        crate::types::RecordRepresentation::RecordRegular,
    );
    let id = local("r", 10);
    let mut tables = Env::empty();
    let mut log = LogEnv::empty();
    tables.store_type(&ctx, id, decl.clone());
    log.store_type(&ctx, id, decl);
    for name in ["first", "second"] {
        let (left, right) = (
            tables.find_label(name).unwrap(),
            log.find_label(name).unwrap(),
        );
        assert_eq!(
            (left.lbl_name, left.lbl_pos),
            (right.lbl_name, right.lbl_pos)
        );
    }
    assert!(tables.type_label_family(&id).is_some() && log.type_label_family(&id).is_some());
    assert_eq!(log.log().entries.len(), 4);
    assert_eq!(
        log.normalize_path(&ctx, &Path::pident(id)),
        tables.normalize_path(&ctx, &Path::pident(id))
    );
}

// ============================================================================
// The property test: today's tables against the log
// ============================================================================

fn label(n: u32) -> LabelDescription {
    LabelDescription {
        lbl_name: Name::new("field"),
        lbl_runtime_name: Name::new("field"),
        lbl_res: TypeExprRef(0),
        lbl_arg: TypeExprRef(n),
        lbl_mut: crate::types::MutableFlag::Immutable,
        lbl_optional: false,
        lbl_pos: n as i32,
        lbl_all: LabelArrayRef::NONE,
        lbl_repres: crate::types::RecordRepresentation::RecordRegular,
        lbl_private: PrivateFlag::Public,
        lbl_loc: crate::types::DeclLoc::none(),
    }
}

const LOWER: [&str; 4] = ["a", "b", "c", "d"];
const UPPER: [&str; 4] = ["A", "B", "C", "D"];
const STAMPS: u8 = 4;
const RETAINED: usize = 6;

/// An identifier of the test's universe: a name and one of a few stamps, 0
/// for the persistent identifier of the name. Stamps are unique per name, as
/// the compiler's are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IdSpec {
    name: u8,
    stamp: u8,
}

impl IdSpec {
    fn of(n: u32) -> IdSpec {
        IdSpec {
            name: (n % 4) as u8,
            stamp: ((n / 4) % u32::from(STAMPS + 1)) as u8,
        }
    }

    fn ident(self, names: &[&str; 4], base: i32) -> Ident {
        let name = names[self.name as usize % 4];
        match self.stamp % (STAMPS + 1) {
            0 => Ident::create_persistent(name),
            stamp => local(
                name,
                base + i32::from(self.name % 4) * 10 + i32::from(stamp),
            ),
        }
    }

    fn lower(self) -> Ident {
        self.ident(&LOWER, 100)
    }

    fn upper(self) -> Ident {
        self.ident(&UPPER, 200)
    }

    /// Module types take no persistent identifier: `ident_tbl_fold_name_order`
    /// orders names by stamp, and today's tables break a tie by hash order.
    fn modtype(self) -> Ident {
        IdSpec {
            name: self.name,
            stamp: self.stamp % STAMPS + 1,
        }
        .ident(&UPPER, 300)
    }
}

/// One step of a sequence. Every field is data: a sequence replays the same
/// way with any of its steps removed.
#[derive(Clone, Debug)]
enum Op {
    Value {
        env: u8,
        id: IdSpec,
        n: u32,
    },
    Type {
        env: u8,
        id: IdSpec,
        n: u32,
    },
    Variance {
        env: u8,
        id: IdSpec,
    },
    Family {
        env: u8,
        id: IdSpec,
        n: u32,
    },
    Constructor {
        env: u8,
        id: IdSpec,
        n: u32,
    },
    Label {
        env: u8,
        id: IdSpec,
        n: u32,
    },
    Module {
        env: u8,
        id: IdSpec,
        shape: u8,
        n: u32,
    },
    Modtype {
        env: u8,
        id: IdSpec,
        n: u32,
    },
    Open {
        env: u8,
        layers: u8,
        slot: Option<u32>,
        root: u8,
    },
    Replace {
        env: u8,
        name: u8,
        n: u32,
    },
    Constraint {
        env: u8,
        id: IdSpec,
        n: u32,
    },
    GadtLevel {
        env: u8,
    },
    ImplicitRoot {
        env: u8,
        root: u8,
    },
    Coercion {
        env: u8,
    },
    Clone {
        env: u8,
        slot: u8,
    },
    Freeze {
        env: u8,
    },
    Observe {
        env: u8,
    },
}

/// What every sequence shares: the opened signatures and a few declarations.
struct Fixtures {
    ctx: TypeContext,
    constructor: ConstructorDescription,
    layers: Vec<OpenedLayers>,
    roots: Vec<Path>,
    lower: Vec<Name>,
    upper: Vec<Name>,
    /// Identifiers of the opened tables: a lookup by identifier must not
    /// find them through an open, nor through a replacement of one.
    opened_ids: Vec<[Ident; 3]>,
}

impl Fixtures {
    fn new() -> Fixtures {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let constructor = initial_env(&ctx).find_constructor("Some").unwrap().clone();
        let constr = |n: u32| {
            let mut desc = constructor.clone();
            desc.cstr_arity = n as i32;
            desc
        };
        let components = |name: &str, n: u32| {
            Rc::new(StoredModuleComponents::new(
                Env::empty(),
                Path::pident(Ident::create_persistent(name)),
                module_of(signature(n)),
            ))
        };
        let open_id = |name: &str, n: i32| local(name, 400 + n);
        let empty = || OpenedLayers::build(vec![], vec![], vec![], vec![], vec![], vec![], vec![]);
        let layers = vec![
            empty(),
            // Values only.
            OpenedLayers::build(
                vec![
                    (open_id("a", 1), value(1_001), 0),
                    (open_id("b", 2), value(1_002), 1),
                ],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
            ),
            // Every table.
            OpenedLayers::build(
                vec![
                    (open_id("a", 3), value(1_003), 0),
                    (open_id("c", 4), value(1_004), 2),
                ],
                vec![
                    (open_id("a", 5), Arc::new(type_decl(1_005))),
                    (open_id("d", 6), Arc::new(type_decl(1_006))),
                ],
                vec![
                    (open_id("A", 7), constr(1_007)),
                    (open_id("A", 8), constr(1_008)),
                    (open_id("C", 9), constr(1_009)),
                ],
                vec![
                    (open_id("a", 10), label(1_010)),
                    (open_id("a", 11), label(1_011)),
                ],
                vec![
                    (open_id("A", 12), module_of(signature(1_012)), 3),
                    (open_id("B", 13), module_of(signature(1_013)), 4),
                ],
                vec![
                    (open_id("A", 12), components("A", 1_012), 3),
                    (open_id("C", 14), components("C", 1_014), 5),
                ],
                vec![
                    (open_id("A", 15), modtype(1_015)),
                    (open_id("D", 16), modtype(1_016)),
                ],
            ),
            // Constructors and labels only.
            OpenedLayers::build(
                vec![],
                vec![],
                vec![
                    (open_id("B", 17), constr(1_017)),
                    (open_id("A", 18), constr(1_018)),
                ],
                vec![(open_id("b", 19), label(1_019))],
                vec![],
                vec![],
                vec![],
            ),
            // Module types only.
            OpenedLayers::build(
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![
                    (open_id("B", 20), modtype(1_020)),
                    (open_id("C", 21), modtype(1_021)),
                ],
            ),
            // Modules without components, and types.
            OpenedLayers::build(
                vec![],
                vec![(open_id("b", 22), Arc::new(type_decl(1_022)))],
                vec![],
                vec![],
                vec![
                    (open_id("C", 23), module_of(signature(1_023)), 0),
                    (
                        open_id("D", 24),
                        module_of(ModuleType::MtyAlias(
                            AliasPresence::MtaPresent,
                            Arc::new(root("Stdlib")),
                        )),
                        1,
                    ),
                ],
                vec![],
                vec![],
            ),
        ];
        Fixtures {
            ctx,
            constructor,
            layers,
            roots: vec![
                root("Stdlib"),
                root("Pervasives"),
                Path::pident(local("A", 211)),
                root("A"),
            ],
            lower: LOWER.iter().map(|name| Name::new(name)).collect(),
            upper: UPPER.iter().map(|name| Name::new(name)).collect(),
            opened_ids: vec![
                [open_id("a", 1), open_id("A", 12), open_id("A", 15)],
                [open_id("a", 3), open_id("C", 23), open_id("B", 20)],
                [open_id("c", 4), open_id("B", 13), open_id("D", 16)],
            ],
        }
    }

    fn constructor(&self, n: u32) -> ConstructorDescription {
        let mut desc = self.constructor.clone();
        desc.cstr_arity = n as i32;
        desc
    }

    fn module(&self, shape: u8, n: u32) -> ModuleDeclaration {
        let target = IdSpec::of(n).upper();
        module_of(match shape % 5 {
            0 | 1 => signature(n),
            2 => ModuleType::MtyAlias(AliasPresence::MtaPresent, Arc::new(Path::pident(target))),
            3 => ModuleType::MtyIdent(Path::pident(IdSpec::of(n).modtype())),
            _ => ModuleType::MtyAlias(
                AliasPresence::MtaPresent,
                Arc::new(Path::pdot(Path::pident(target), "B")),
            ),
        })
    }
}

/// The retained environments: each as today's tables and as a log version.
struct World {
    envs: Vec<(Env, LogEnv)>,
}

/// Run one step on both representations.
fn apply(world: &mut World, op: &Op, fx: &Fixtures) -> usize {
    let pick = |env: u8| env as usize % world.envs.len();
    macro_rules! both {
        ($env:expr, |$e:ident| $body:expr) => {{
            let at = pick($env);
            let (tables, log) = &mut world.envs[at];
            {
                let $e = tables;
                $body;
            }
            {
                let $e = log;
                $body;
            }
            at
        }};
    }
    match op {
        Op::Value { env, id, n } => both!(*env, |e| e.add_value(id.lower(), value(*n))),
        Op::Type { env, id, n } => both!(*env, |e| e.add_type(id.lower(), type_decl(*n))),
        Op::Variance { env, id } => both!(*env, |e| {
            let _ = e.update_type_variance(id.lower(), vec![Variance::FULL]);
        }),
        Op::Family { env, id, n } => {
            both!(*env, |e| e
                .add_type_label_family(id.lower(), LabelArrayRef(*n)))
        }
        Op::Constructor { env, id, n } => {
            both!(*env, |e| e.add_constructor(id.upper(), fx.constructor(*n)))
        }
        Op::Label { env, id, n } => both!(*env, |e| e.add_label(id.lower(), label(*n))),
        Op::Module { env, id, shape, n } => {
            let id = id.upper();
            let decl = fx.module(*shape, *n);
            match shape % 3 {
                0 => both!(*env, |e| e.add_module(id, decl.clone())),
                1 => both!(*env, |e| e.add_module_arg(id, decl.clone())),
                _ => both!(*env, |e| e.add_module_with_component_context(
                    id,
                    decl.clone(),
                    fx.module(0, *n),
                    Path::pdot(fx.roots[0], id.name_atom()),
                    Some((fx.roots[0], Arc::new(vec![]))),
                )),
            }
        }
        Op::Modtype { env, id, n } => both!(*env, |e| e.add_modtype(id.modtype(), modtype(*n))),
        Op::Open {
            env,
            layers,
            slot,
            root,
        } => {
            let layers = &fx.layers[*layers as usize % fx.layers.len()];
            let root = fx.roots[*root as usize % fx.roots.len()];
            both!(*env, |e| e.add_prebuilt_open_layers(root, layers, *slot))
        }
        Op::Replace { env, name, n } => both!(*env, |e| {
            let _ = e.update_value_type_by_name(LOWER[*name as usize % 4], TypeExprRef(*n));
        }),
        Op::Constraint { env, id, n } => {
            both!(*env, |e| e
                .add_local_constraint(Path::pident(id.lower()), type_decl(*n)))
        }
        Op::GadtLevel { env } => both!(*env, |e| e.add_gadt_instance_level()),
        Op::ImplicitRoot { env, root } => {
            let name = fx.roots[*root as usize % fx.roots.len()]
                .head()
                .name()
                .to_string();
            both!(*env, |e| e.mark_implicit_open_root(&name))
        }
        Op::Coercion { env } => {
            let at = pick(*env);
            world.envs[at] = (
                world.envs[at].0.implicit_coercion(),
                world.envs[at].1.implicit_coercion(),
            );
            at
        }
        Op::Clone { env, slot } => {
            let copy = world.envs[pick(*env)].clone();
            if world.envs.len() < RETAINED {
                world.envs.push(copy);
                world.envs.len() - 1
            } else {
                let at = *slot as usize % world.envs.len();
                world.envs[at] = copy;
                at
            }
        }
        Op::Freeze { env } => {
            let at = pick(*env);
            // The tables have no such step. A log that binds modules is not
            // frozen (see `LogEnv::freeze`).
            if world.envs[at].1.log().modules.len() == 0 {
                world.envs[at].1.freeze();
            }
            at
        }
        Op::Observe { env } => pick(*env),
    }
}

/// The kind and text of a failed lookup, without allocating.
fn text<T>(result: &EnvResult<T>) -> Option<(u8, &str)> {
    Some(match result.as_ref().err()? {
        EnvError::ValueNotFound(name) => (0, name.as_str()),
        EnvError::TypeNotFound(name) => (1, name.as_str()),
        EnvError::ModuleNotFound(name) => (2, name.as_str()),
        EnvError::ModtypeNotFound(name) => (3, name.as_str()),
        EnvError::ConstructorNotFound(name) => (4, name.as_str()),
        EnvError::LabelNotFound(name) => (5, name.as_str()),
        EnvError::InconsistentImport { name, .. } => (6, name.as_str()),
        EnvError::IllegalValueName(_, name) => (7, name.as_str()),
    })
}

/// Compare one lookup made on both representations.
macro_rules! same {
    ($what:expr, $tables:expr, $log:expr) => {{
        let (tables, log) = ($tables, $log);
        if tables != log {
            return Err(format!(
                "{}:\n  tables: {:?}\n  log:    {:?}",
                $what, tables, log
            ));
        }
    }};
}

/// A fallible lookup: the same value, or the same error.
macro_rules! same_result {
    ($what:expr, $tables:expr, $log:expr) => {{
        let (tables, log) = ($tables, $log);
        same!($what, text(&tables), text(&log));
        same!($what, tables.ok(), log.ok());
    }};
}

/// Every lookup by name, of one lower-case and one upper-case name.
fn compare_names(
    tables: &Env,
    log: &LogEnv,
    lower: Name,
    upper: Name,
    fx: &Fixtures,
) -> Result<(), String> {
    let (l, u) = (lower.as_str(), upper.as_str());
    same_result!(
        format!("find_value {l}"),
        tables.find_value(lower),
        log.find_value(lower)
    );
    same_result!(
        format!("find_value(&str) {l}"),
        tables.find_value(l),
        log.find_value(l)
    );
    same_result!(
        format!("find_value_with_id {l}"),
        tables.find_value_with_id(lower),
        log.find_value_with_id(lower)
    );
    same_result!(
        format!("find_value_arc_with_path {l}"),
        tables.find_value_arc_with_path(lower),
        log.find_value_arc_with_path(lower)
    );
    same_result!(
        format!("find_type {l}"),
        tables.find_type(lower),
        log.find_type(lower)
    );
    same_result!(
        format!("find_type_with_path {l}"),
        tables.find_type_with_path(lower),
        log.find_type_with_path(lower)
    );
    same_result!(
        format!("find_type_arc_with_path {l}"),
        tables.find_type_arc_with_path(lower),
        log.find_type_arc_with_path(lower)
    );
    same_result!(
        format!("find_label {l}"),
        tables.find_label(lower),
        log.find_label(lower)
    );
    same!(
        format!("find_all_labels {l}"),
        tables.find_all_labels(lower),
        log.find_all_labels(lower)
    );
    same!(
        format!("find_all_labels_marking {l}"),
        tables.find_all_labels_marking(l),
        log.find_all_labels_marking(l)
    );
    same_result!(
        format!("find_constructor {u}"),
        tables.find_constructor(upper),
        log.find_constructor(upper)
    );
    same!(
        format!("find_all_constructors {u}"),
        tables.find_all_constructors(upper),
        log.find_all_constructors(upper)
    );
    same!(
        format!("find_all_constructors_marking {u}"),
        tables.find_all_constructors_marking(u),
        log.find_all_constructors_marking(u)
    );
    same_result!(
        format!("find_module {u}"),
        tables.find_module(upper),
        log.find_module(upper)
    );
    same_result!(
        format!("find_module_with_id {u}"),
        tables.find_module_with_id(upper),
        log.find_module_with_id(upper)
    );
    same_result!(
        format!("find_module_with_path {u}"),
        tables.find_module_with_path(upper),
        log.find_module_with_path(upper)
    );
    same_result!(
        format!("find_modtype {u}"),
        tables.find_modtype(upper),
        log.find_modtype(upper)
    );
    same_result!(
        format!("find_modtype_with_path {u}"),
        tables.find_modtype_with_path(upper),
        log.find_modtype_with_path(upper)
    );
    for (kind, name) in [
        (OpenLookupKind::Value, lower),
        (OpenLookupKind::Type, lower),
        (OpenLookupKind::Module, upper),
        (OpenLookupKind::Component, upper),
        (OpenLookupKind::Modtype, upper),
    ] {
        same!(
            format!("open_slot_use {kind:?} {}", name.as_str()),
            tables.open_slot_use(kind, name),
            log.open_slot_use(kind, name)
        );
    }
    for root in &fx.roots {
        let dotted = Path::pdot(*root, upper);
        let nested = Path::pdot(dotted, lower);
        same_result!(
            format!("lookup_value {}", dotted.name()),
            tables.lookup_value(&Path::pdot(*root, lower)),
            log.lookup_value(&Path::pdot(*root, lower))
        );
        for path in [dotted, nested] {
            let name = || path.name();
            same!(
                format!("path_starts_with_opened_component {}", name()),
                tables.path_starts_with_opened_component(&path),
                log.path_starts_with_opened_component(&path)
            );
            same!(
                format!("path_starts_with_implicit_opened_component {}", name()),
                tables.path_starts_with_implicit_opened_component(&path),
                log.path_starts_with_implicit_opened_component(&path)
            );
        }
    }
    Ok(())
}

/// Every lookup by identifier and by path, of one identifier of each case.
fn compare_idents(
    tables: &Env,
    log: &LogEnv,
    lower: &Ident,
    upper: &Ident,
    modtype: &Ident,
    fx: &Fixtures,
) -> Result<(), String> {
    let (l, u) = (Path::pident(*lower), Path::pident(*upper));
    // Formatted only when a comparison fails.
    struct Shown<'a>(&'a Ident);
    impl std::fmt::Display for Shown<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}/{}", self.0.name(), self.0.stamp())
        }
    }
    let (ln, un) = (Shown(lower), Shown(upper));
    same_result!(
        format!("lookup_value {ln}"),
        tables.lookup_value(&l),
        log.lookup_value(&l)
    );
    same_result!(
        format!("find_type_by_ident {ln}"),
        tables.find_type_by_ident(lower),
        log.find_type_by_ident(lower)
    );
    same!(
        format!("find_type_arc_by_ident {ln}"),
        tables.find_type_arc_by_ident(lower),
        log.find_type_arc_by_ident(lower)
    );
    same!(
        format!("lookup_type_arc_by_ident {ln}"),
        tables.lookup_type_arc_by_ident(lower),
        log.lookup_type_arc_by_ident(lower)
    );
    same_result!(
        format!("lookup_type {ln}"),
        tables.lookup_type(&l),
        log.lookup_type(&l)
    );
    same!(
        format!("type_label_family {ln}"),
        tables.type_label_family(lower),
        log.type_label_family(lower)
    );
    same!(
        format!("find_local_constraint {ln}"),
        tables.find_local_constraint(&l),
        log.find_local_constraint(&l)
    );
    same!(
        format!("has_module_ident {un}"),
        tables.has_module_ident(upper),
        log.has_module_ident(upper)
    );
    same_result!(
        format!("lookup_module_ident_exact {un}"),
        tables.lookup_module_ident_exact(upper),
        log.lookup_module_ident_exact(upper)
    );
    same_result!(
        format!("find_module_same {un}"),
        tables.find_module_same(upper),
        log.find_module_same(upper)
    );
    same!(
        format!("is_functor_arg_path {un}"),
        tables.is_functor_arg_path(&u),
        log.is_functor_arg_path(&u)
    );
    let m = Path::pident(*modtype);
    same_result!(
        format!("lookup_modtype {}/{}", modtype.name(), modtype.stamp()),
        tables.lookup_modtype(&m),
        log.lookup_modtype(&m)
    );
    let sub = Path::pdot(u, "B");
    for path in [u, sub] {
        struct ShownPath(Path, i32);
        impl std::fmt::Display for ShownPath {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}/{}", self.0.name(), self.1)
            }
        }
        let name = ShownPath(path, upper.stamp());
        same_result!(
            format!("lookup_module {name}"),
            tables.lookup_module(&path),
            log.lookup_module(&path)
        );
        same!(
            format!("is_functor_arg_path {name}"),
            tables.is_functor_arg_path(&path),
            log.is_functor_arg_path(&path)
        );
        same!(
            format!("normalize_path {name}"),
            tables.normalize_path(&fx.ctx, &path),
            log.normalize_path(&fx.ctx, &path)
        );
        same!(
            format!("module_path_requires_env_scoped_cache {name}"),
            tables.module_path_requires_env_scoped_cache(&path),
            log.module_path_requires_env_scoped_cache(&path)
        );
        let (ty, mty, val) = (
            Path::pdot(path, "a"),
            Path::pdot(path, "C"),
            Path::pdot(path, "b"),
        );
        same_result!(
            format!("lookup_type {name}.a"),
            tables.lookup_type(&ty),
            log.lookup_type(&ty)
        );
        same_result!(
            format!("lookup_modtype {name}.C"),
            tables.lookup_modtype(&mty),
            log.lookup_modtype(&mty)
        );
        same!(
            format!("normalize_path_prefix {name}.b"),
            tables.normalize_path_prefix(&fx.ctx, &val),
            log.normalize_path_prefix(&fx.ctx, &val)
        );
    }
    // The component thunk: what it would build, and where.
    let thunk = |components: &StoredModuleComponents| {
        let (_, access_path, decl, has_parent) = components.test_parts();
        (*access_path, decl.clone(), has_parent)
    };
    let log_thunk = |components: &LogComponents| {
        (
            components.access_path,
            components.module_decl.clone(),
            components.parent_context.is_some(),
        )
    };
    same!(
        format!("with_local_module_components {un}"),
        tables.with_local_module_components(&u, thunk),
        log.with_local_module_components(&u, log_thunk)
    );
    let (shared, log_shared) = (
        tables.local_module_components_shared(&u),
        log.local_module_components_shared(&u),
    );
    same!(
        format!("local_module_components_shared {un}"),
        shared.as_deref().map(thunk),
        log_shared.as_deref().map(log_thunk)
    );
    if let (Some(shared), Some(log_shared)) = (shared, log_shared) {
        // The seed is the environment before the binding, on both sides.
        let seed = log_shared
            .seed
            .env()
            .ok_or_else(|| format!("the seed of {un} lost its log"))?;
        let name = (upper.stamp() as usize + lower.stamp() as usize) % 4;
        compare_names(
            shared.test_parts().0,
            &seed,
            fx.lower[name],
            fx.upper[name],
            fx,
        )
        .map_err(|error| format!("in the seed of {un}: {error}"))?;
    }
    Ok(())
}

/// The lookups that read a whole environment.
fn compare_whole(tables: &Env, log: &LogEnv) -> Result<(), String> {
    let mut values: Vec<_> = tables
        .iter_values()
        .map(|(id, desc)| (id.stamp(), id.name(), desc.val_type.0))
        .collect();
    let mut log_values: Vec<_> = log
        .iter_values()
        .map(|(id, desc)| (id.stamp(), id.name(), desc.val_type.0))
        .collect();
    values.sort_unstable();
    log_values.sort_unstable();
    same!("iter_values", values, log_values);
    let mut constraints: Vec<_> = tables
        .iter_local_constraints()
        .map(|(path, decl)| (path.name(), path.head().stamp(), decl.type_arity))
        .collect();
    let mut log_constraints: Vec<_> = log
        .iter_local_constraints()
        .map(|(path, decl)| (path.name(), path.head().stamp(), decl.type_arity))
        .collect();
    constraints.sort_unstable();
    log_constraints.sort_unstable();
    same!("iter_local_constraints", constraints, log_constraints);
    same!(
        "has_local_constraints",
        tables.has_local_constraints(),
        log.has_local_constraints()
    );
    same!(
        "fold_modtype_names",
        tables.fold_modtype_names(),
        log.fold_modtype_names()
    );
    same!(
        "is_implicit_coercion",
        tables.is_implicit_coercion(),
        log.is_implicit_coercion()
    );
    same!(
        "is_in_signature",
        tables.is_in_signature(),
        log.is_in_signature()
    );
    same!(
        "with_current_local_module_aliases",
        tables.with_current_local_module_aliases(|aliases| aliases.to_vec()),
        log.with_current_local_module_aliases(|aliases| aliases.to_vec())
    );
    Ok(())
}

/// Everything, for one retained environment: every name, and every
/// identifier of `ids` (lower-case, upper-case, module type).
fn compare_all(
    tables: &Env,
    log: &LogEnv,
    ids: &[[Ident; 3]],
    fx: &Fixtures,
) -> Result<(), String> {
    for (lower, upper) in fx.lower.iter().zip(&fx.upper) {
        compare_names(tables, log, *lower, *upper, fx)?;
    }
    for [lower, upper, modtype] in ids {
        compare_idents(tables, log, lower, upper, modtype, fx)?;
    }
    compare_whole(tables, log)
}

/// `id` and `scope_id` are equal between two environments exactly when
/// they are today.
fn compare_identity(world: &World) -> Result<(), String> {
    for (i, (tables, log)) in world.envs.iter().enumerate() {
        for (j, (other, other_log)) in world.envs.iter().enumerate().skip(i + 1) {
            same!(
                format!("id equality of {i} and {j}"),
                tables.id() == other.id(),
                log.id() == other_log.id()
            );
            same!(
                format!("scope_id equality of {i} and {j}"),
                tables.scope_id() == other.scope_id(),
                log.scope_id() == other_log.scope_id()
            );
        }
    }
    Ok(())
}

/// The identifier a step binds or names, if it has one.
fn focus(op: &Op) -> Option<IdSpec> {
    match op {
        Op::Value { id, .. }
        | Op::Type { id, .. }
        | Op::Variance { id, .. }
        | Op::Family { id, .. }
        | Op::Constructor { id, .. }
        | Op::Label { id, .. }
        | Op::Module { id, .. }
        | Op::Modtype { id, .. }
        | Op::Constraint { id, .. } => Some(*id),
        Op::Replace { name, n, .. } => Some(IdSpec {
            name: *name,
            stamp: (*n % 5) as u8,
        }),
        _ => None,
    }
}

/// Run a sequence. After every step: every lookup by name and identifier of
/// the name the step touched, on the environment it touched, the
/// whole-environment lookups and the identities. At an `Observe` step and,
/// at the end, for every retained environment: every lookup of every name
/// and of every identifier the sequence uses, and of one it does not.
fn check(ops: &[Op], fx: &Fixtures) -> Result<(), String> {
    let mut world = World {
        envs: vec![(Env::empty(), LogEnv::empty())],
    };
    let mut used: Vec<IdSpec> = vec![IdSpec {
        name: 3,
        stamp: STAMPS,
    }];
    for id in ops.iter().filter_map(focus) {
        if !used.contains(&id) {
            used.push(id);
        }
    }
    let mut ids: Vec<[Ident; 3]> = used
        .iter()
        .map(|id| [id.lower(), id.upper(), id.modtype()])
        .collect();
    ids.extend(fx.opened_ids.iter().copied());
    for (step, op) in ops.iter().enumerate() {
        let at = apply(&mut world, op, fx);
        let after =
            |error: String| format!("after step {step} ({op:?}), environment {at}: {error}");
        let (tables, log) = &world.envs[at];
        if let Op::Observe { .. } = op {
            compare_all(tables, log, &ids, fx).map_err(after)?;
        } else {
            let id = focus(op).unwrap_or(IdSpec::of(step as u32 * 7 + 3));
            let name = id.name as usize % 4;
            compare_names(tables, log, fx.lower[name], fx.upper[name], fx).map_err(after)?;
            compare_idents(tables, log, &id.lower(), &id.upper(), &id.modtype(), fx)
                .map_err(after)?;
            compare_whole(tables, log).map_err(after)?;
        }
        compare_identity(&world).map_err(after)?;
    }
    // Newest first: the log's path moves back through every retained version.
    for at in (0..world.envs.len()).rev() {
        let (tables, log) = &world.envs[at];
        compare_all(tables, log, &ids, fx)
            .map_err(|error| format!("at the end, environment {at}: {error}"))?;
    }
    Ok(())
}

/// `check`, with a panic of either representation reported as a failure.
fn run(ops: &[Op], fx: &Fixtures) -> Result<(), String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| check(ops, fx))) {
        Ok(result) => result,
        Err(panic) => Err(panic
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| panic.downcast_ref::<&str>().map(|text| text.to_string()))
            .unwrap_or_else(|| "panic".to_string())),
    }
}

/// SplitMix64: fixed seeds give fixed sequences on every platform.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: u32) -> u32 {
        (self.next() % u64::from(bound)) as u32
    }
}

fn generate(rng: &mut Rng, length: usize) -> Vec<Op> {
    let mut ops = Vec::with_capacity(length);
    // Mostly the environment used last: nested scopes, with jumps back.
    let mut current = 0u8;
    for _ in 0..length {
        if rng.below(4) == 0 {
            current = rng.below(RETAINED as u32) as u8;
        }
        let env = current;
        let id = IdSpec::of(rng.below(4 * (u32::from(STAMPS) + 1)));
        let n = rng.below(1_000);
        ops.push(match rng.below(40) {
            0..=5 => Op::Value { env, id, n },
            6..=8 => Op::Type { env, id, n },
            9 => Op::Variance { env, id },
            10..=11 => Op::Family { env, id, n },
            12..=14 => Op::Constructor { env, id, n },
            15..=17 => Op::Label { env, id, n },
            18..=21 => Op::Module {
                env,
                id,
                shape: rng.below(15) as u8,
                n,
            },
            22..=23 => Op::Modtype { env, id, n },
            24..=27 => Op::Open {
                env,
                layers: rng.below(6) as u8,
                slot: (rng.below(3) != 0).then(|| rng.below(50)),
                root: rng.below(4) as u8,
            },
            28..=29 => Op::Replace {
                env,
                name: rng.below(4) as u8,
                n,
            },
            30 => Op::Constraint { env, id, n },
            31 => Op::GadtLevel { env },
            32 => Op::ImplicitRoot {
                env,
                root: rng.below(4) as u8,
            },
            33 => Op::Coercion { env },
            34..=36 => {
                current = rng.below(RETAINED as u32) as u8;
                Op::Clone { env, slot: current }
            }
            37 => Op::Freeze { env },
            _ => Op::Observe {
                env: rng.below(RETAINED as u32) as u8,
            },
        });
    }
    ops
}

/// The shortest sequence found that still fails: steps are removed in
/// halving chunks, then one at a time, for as long as the failure stays.
fn shrink(mut ops: Vec<Op>, fx: &Fixtures) -> Vec<Op> {
    let mut chunk = ops.len().div_ceil(2);
    while chunk > 0 {
        let mut start = 0;
        let mut removed = false;
        while start < ops.len() {
            let end = (start + chunk).min(ops.len());
            let mut shorter = ops.clone();
            shorter.drain(start..end);
            if run(&shorter, fx).is_err() {
                ops = shorter;
                removed = true;
            } else {
                start = end;
            }
        }
        if !removed || chunk > 1 {
            chunk = if chunk > 1 {
                chunk.div_ceil(2).min(chunk - 1)
            } else {
                0
            };
        }
    }
    ops
}

const SEED: u64 = 0x5eed_1e55_c0de_2026;

/// Run `count` sequences; on a failure, the report with the shrunk sequence.
fn run_sequences(count: u64, length: usize, fx: &Fixtures) -> Result<(), String> {
    for sequence in 0..count {
        let ops = generate(
            &mut Rng(SEED ^ sequence.wrapping_mul(0x2545_f491_4f6c_dd1d)),
            length,
        );
        if run(&ops, fx).is_err() {
            let minimal = shrink(ops, fx);
            let failure = run(&minimal, fx).expect_err("the shrunk sequence fails");
            let steps: Vec<String> = minimal.iter().map(|op| format!("    {op:?}")).collect();
            return Err(format!(
                "sequence {sequence} (seed {SEED:#x}) fails; minimal failing sequence, {} steps:\n{}\n{failure}",
                minimal.len(),
                steps.join("\n")
            ));
        }
    }
    Ok(())
}

#[test]
fn the_log_answers_every_lookup_as_the_tables_do() {
    let fx = Fixtures::new();
    let started = std::time::Instant::now();
    let result = run_sequences(10_000, 24, &fx);
    eprintln!(
        "environment log property test: 10,000 sequences of 24 steps in {:.1?}",
        started.elapsed()
    );
    if let Err(report) = result {
        panic!("{report}");
    }
}

#[test]
fn the_property_test_catches_an_injected_fault() {
    let fx = Fixtures::new();
    // The panic hook is process-wide: other tests' failures must still print.
    INJECT_FAULT.set(true);
    let result = run_sequences(10_000, 24, &fx);
    INJECT_FAULT.set(false);
    let report = result.expect_err("an open that forgets the earlier opens goes unnoticed");
    eprintln!("injected fault caught:\n{report}");
    let steps = report
        .lines()
        .filter(|line| line.starts_with("    "))
        .count();
    assert!(steps <= 4, "the failing sequence was not shrunk:\n{report}");
}
