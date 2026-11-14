//! Test-only comparison with the verbatim trunk planner, including typed corpora.
use super::*;
use crate::types::variant_runtime::{Instance, Layout, ShapeAllocation};
use std::cell::RefCell;

thread_local! {
    // Test-only collection once per declaration, never part of production lookup.
    static DECLARATIONS: RefCell<Option<Vec<MatchingFacts>>> = const { RefCell::new(None) };
}

/// O(declaration payload bytes) only while the corpus test is collecting layouts.
pub(crate) fn record(layout: &Layout) {
    if layout.unboxed {
        DECLARATIONS.with(|slot| {
            if let Some(facts) = slot.borrow_mut().as_mut() {
                facts.push(layout.matching_facts.clone());
            }
        });
    }
}

macro_rules! snapshot {
    ($name:ident, $implementation:path) => {
        mod $name {
            use $implementation as implementation;
            use implementation::{Plan, Test, TestId, Tree, TreeId, Clause};
            use crate::types::variant_runtime::Instance;
            /// O(expanded test size); this test serializer deliberately preserves order.
            fn test(p: &Plan<u32>, id: TestId) -> String {
                match p.test(id) {
                    Test::Equals(tag) => format!("eq({tag:?})"),
                    Test::Typeof(kind) => format!("typeof({kind:?})"),
                    Test::Instance(Instance::Array(_)) => "array".into(),
                    Test::Instance(Instance::Class { name, .. }) => format!("instance({name})"),
                    Test::NotNull => "nonnull".into(),
                    Test::Not(t) => format!("not({})", test(p, *t)),
                    Test::And(a,b) => format!("and({},{})", test(p,*a),test(p,*b)),
                    Test::Or(a,b) => format!("or({},{})", test(p,*a),test(p,*b)),
                }
            }
            /// O(expanded clause size), for test comparison only.
            fn clause(p: &Plan<u32>, c: &Clause<u32>) -> String {
                match c {
                    Clause::FallsThrough(a) => format!("fall({a:?})"),
                    Clause::Body(t) => tree(p,*t),
                }
            }
            /// O(expanded plan size), ignoring only pool indices and unreachable rows.
            pub(super) fn tree(p: &Plan<u32>, id: TreeId) -> String {
                match p.tree(id) {
                    Tree::Run(a) => format!("run({a})"),
                    Tree::Fallback => "fallback".into(),
                    Tree::Skip => "skip".into(),
                    Tree::If(t,a,b) => format!("if({},{},{})",test(p,*t),tree(p,*a),tree(p,*b)),
                    Tree::Block(t) => format!("block({})",tree(p,*t)),
                    Tree::SwitchValue(c,d) => { assert_eq!(c.len(), p.value_clauses(*c).iter().count()); format!("value({:?};{})",p.value_clauses(*c).iter().map(|(tag,c)| (format!("{tag:?}"),clause(p,c))).collect::<Vec<_>>(),tree(p,*d)) },
                    Tree::SwitchTypeof(c,d) => format!("type({:?};{})",p.typeof_clauses(*c).iter().map(|(kind,c)| (format!("{kind:?}"),clause(p,c))).collect::<Vec<_>>(),tree(p,*d)),
                }
            }
        }
    };
}
snapshot!(current, crate::lambda::untagged_dispatch);
snapshot!(legacy, crate::lambda::untagged_dispatch::legacy_planner);

/// Compare sixteen completeness/body-sharing combinations per declaration.
/// Cost: sixteen planner runs plus serialization of their reachable trees.
fn compare(facts: &MatchingFacts) {
    for shared in [false, true] {
        for complete in 0..4 {
            for fallback in [None, Some(999)] {
                let literals: Vec<_> = facts.literal_tags.iter().enumerate().map(|(i,t)| (t.clone(),if shared { 0 } else { i as u32 })).collect();
                let payloads: Vec<_> = facts.block_types.iter().enumerate().map(|(i,t)| (t.clone(),if shared { 0 } else { (i+facts.literal_tags.len()) as u32 })).collect();
                let a = plan(|a,b| a==b,Input { facts, literal_arms:literals.clone(),payload_arms:payloads.clone(),literals_complete:complete&1!=0,payloads_complete:complete&2!=0,fallback });
                let b = super::legacy_planner::plan(|a,b| a==b,super::legacy_planner::Input { facts,literal_arms:literals,payload_arms:payloads,literals_complete:complete&1!=0,payloads_complete:complete&2!=0,fallback });
                assert_eq!(current::tree(&a,a.root()),legacy::tree(&b,b.root()),"facts={facts:?}, shared={shared}, complete={complete}, fallback={fallback:?}");
            }
        }
    }
}

#[test]
fn hand_written_plans_match_trunk() {
    let literals = vec![LiteralTag::Int(1),LiteralTag::Float("1.5".into()),LiteralTag::BigInt("2".into()),LiteralTag::String("text".into()),LiteralTag::Bool(true),LiteralTag::Null,LiteralTag::Undefined];
    compare(&MatchingFacts { tag_name:None,literal_tags:literals.clone(),block_types:vec![] });
    for kind in [BlockType::Unknown,BlockType::Object,BlockType::Instance(Instance::Array(ShapeAllocation::fresh())),BlockType::Instance(Instance::Class { name: "Example".into(), ancestors: vec![], blocks: crate::types::variant_runtime::ClassBlocks::fresh(0) }),BlockType::Function,BlockType::Bigint,BlockType::Number,BlockType::String,BlockType::Boolean,BlockType::Symbol] {
        compare(&MatchingFacts { tag_name:None,literal_tags:literals.clone(),block_types:vec![kind.clone()] });
        compare(&MatchingFacts { tag_name:None,literal_tags:vec![],block_types:vec![kind] });
    }
    compare(&MatchingFacts { tag_name:Some("kind".into()),literal_tags:vec![LiteralTag::String("left".into()),LiteralTag::String("right".into())],block_types:vec![BlockType::Object,BlockType::Object] });
    compare(&MatchingFacts { tag_name:None,literal_tags:vec![LiteralTag::Null],block_types:vec![] });
}

/// O(source bytes plus typechecking and sixteen comparisons per untagged layout).
fn corpus() {
    use crate::driver::{CompilerOptions,compile_file_to_js_with_options};
    use std::path::{Path,PathBuf};
    /// O(directory entries plus source-path bytes), collecting the full corpus.
    fn sources(dir: &Path,out: &mut Vec<PathBuf>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path=entry.unwrap().path();
            if path.is_dir() { sources(&path,out); }
            else if path.extension().is_some_and(|x|x=="res") { out.push(path); }
        }
    }
    let root=Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let runtime=root.join("packages/@rescript/runtime");
    let mut files=Vec::new();sources(&root.join("tests/tests/src"),&mut files);
    for entry in std::fs::read_dir(&runtime).unwrap() { let path=entry.unwrap().path();if path.extension().is_some_and(|x|x=="res") { files.push(path); } }
    files.sort();assert!(files.len()>700);
    let dirs:std::collections::BTreeSet<_>=files.iter().map(|p|p.parent().unwrap().to_path_buf()).collect();
    let mut declarations=0;
    for path in &files {
        let is_runtime=path.parent()==Some(runtime.as_path());
        let module=path.file_stem().unwrap().to_str().unwrap();
        let options=CompilerOptions {
            runtime_path:Some(runtime.clone()),include_paths:[root.join("tests/tests/lib/rescript"),root.join("tests/dependencies/rescript-react/lib/rescript"),runtime.join("lib/rescript")].into_iter().chain(dirs.iter().cloned()).collect(),
            source_filename:Some(path.to_string_lossy().into_owned()),output_path:Some(path.with_extension("mjs")),output_module_format:Some(crate::js_ir::ModuleFormat::EsModule),module_name:Some(format!("{}{}",module[..1].to_ascii_uppercase(),&module[1..])),warning_specs:vec!["-a".into()],make_runtime:is_runtime,nopervasives:is_runtime,open_modules:if is_runtime {vec!["Pervasives".into()]} else {vec![]},no_version_header:is_runtime,experimental_let_unwrap:true,check_div_by_zero:!is_runtime,..CompilerOptions::default()
        };
        DECLARATIONS.with(|s|*s.borrow_mut()=Some(Vec::new()));
        compile_file_to_js_with_options(path,&options).unwrap_or_else(|e|panic!("{}: {e:#}",path.display()));
        let facts=DECLARATIONS.with(|s|s.borrow_mut().take().unwrap());
        declarations+=facts.len();
        for facts in facts { compare(&facts); }
    }
    assert!(declarations>0);
    println!("untagged declarations compared: {declarations}; source files: {}",files.len());
}

#[test]
fn corpus_declarations_match_trunk() {
    std::thread::Builder::new().stack_size(32*1024*1024).spawn(corpus).unwrap().join().unwrap();
}
