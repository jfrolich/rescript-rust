//! Tests of the environment log: the cost of every operation in counted
//! steps, and the module seam.

use super::*;
use crate::context::IdGenerator;
use crate::ident::IdentFlags;
use crate::types::decl::{LabelArrayRef, RecStatus, ValueKind};

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
