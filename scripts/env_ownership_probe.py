#!/usr/bin/env python3
"""Apply the context-owned diagnostic to an archived main-checkout source only."""
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path('/Users/jake/checkouts/rescript-rust')
D = Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership')
S = D / 'probe-source'
assert Path.cwd() == ROOT
assert not (D / 'probe.patch').exists(), 'Preserve prior probe attempts'
changes = []
def edit(path, fn):
    p = S / path
    before = p.read_text()
    after = fn(before)
    assert before != after, path
    backup = D / 'originals' / path
    backup.parent.mkdir(parents=True, exist_ok=True)
    backup.write_text(before)
    p.write_text(after)
    changes.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile='a/'+path, tofile='b/'+path))
def replace(s, old, new):
    assert s.count(old) == 1, (old[:100], s.count(old))
    return s.replace(old, new)
def body(s, name, text):
    start = s.index(name)
    pos = s.index('{', start)
    # Functions with where clauses used below do not contain earlier braces.
    return s[:pos+1] + '\n' + text + s[pos+1:]

probe = r'''//! Archive-only context-local ownership diagnostic. Not production code.
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashSet};
use std::time::Instant;
use super::{context::TypeContext, path::Path};

#[derive(Debug, Default)]
pub(crate) struct ThunkToken(Cell<Option<u64>>);
// A StoredModuleComponents clone has new OnceCells and a cloned seed Env.
// It is a distinct thunk even when a populated cell shares its image.
impl Clone for ThunkToken { fn clone(&self) -> Self { Self::default() } }
impl ThunkToken {
    pub fn get(&self, p: &EnvProbe) -> u64 {
        if let Some(id) = self.0.get() { return id; }
        let id = p.token(); self.0.set(Some(id)); id
    }
}
#[derive(Debug, Default)]
pub(crate) struct EnvProbe {
    name: RefCell<String>,
    next: Cell<u64>,
    depth: Cell<u64>,
    stats: RefCell<BTreeMap<&'static str, u64>>,
    times: RefCell<BTreeMap<&'static str, (u64, u64)>>,
    queries: RefCell<HashSet<(u64, Path, String, &'static str)>>,
    components: RefCell<HashSet<(u64, String, &'static str)>>,
}
impl EnvProbe {
    pub fn name(&self, name: &str) { *self.name.borrow_mut() = name.to_owned(); }
    pub fn token(&self) -> u64 { let id=self.next.get()+1; self.next.set(id); id }
    pub fn add(&self, key: &'static str, n: usize) {
        *self.stats.borrow_mut().entry(key).or_default() += n as u64;
    }
    pub fn query(&self, env: u64, path: &Path, name: &str, api: &'static str) {
        self.add("query_requests",1);
        if !self.queries.borrow_mut().insert((env,path.clone(),name.to_owned(),api)) {
            self.add("query_repeat_key",1);
        }
    }
    pub fn component(&self, id: u64, name: &str, api: &'static str) {
        self.add("component_requests",1);
        if !self.components.borrow_mut().insert((id,name.to_owned(),api)) {
            self.add("component_repeat_key",1);
        }
    }
    pub fn scope<'a>(&'a self, key: &'static str) -> Scope<'a> {
        let depth=self.depth.get(); self.depth.set(depth+1);
        Scope { p:self, key, start:Instant::now(), outer:depth==0 }
    }
    pub fn report(&self, nodes: usize) {
        assert_eq!(self.depth.get(),0,"unbalanced diagnostic scopes");
        eprintln!("[env-ownership] {}", serde_json::json!({
            "module":self.name.borrow().as_str(), "nodes":nodes,
            "stats":&*self.stats.borrow(), "times":&*self.times.borrow(),
            "unique_query_keys":self.queries.borrow().len(),
            "unique_component_keys":self.components.borrow().len(),
            "tokens":self.next.get()
        }));
    }
}
pub(crate) struct NodeScope<'a> { scope: Scope<'a>, ctx: &'a TypeContext, before: usize }
pub(crate) fn node_scope(ctx: &TypeContext, key: &'static str) -> NodeScope<'_> {
    NodeScope {scope:ctx.env_probe.scope(key), ctx, before:ctx.type_expr_count()}
}
impl Drop for NodeScope<'_> {
    fn drop(&mut self) {
        // Inclusive node allocation delta, never added to other nested deltas.
        self.ctx.env_probe.add(self.scope.key, self.ctx.type_expr_count()-self.before);
    }
}
pub(crate) struct Scope<'a> { p:&'a EnvProbe, key:&'static str, start:Instant, outer:bool }
impl Drop for Scope<'_> {
    fn drop(&mut self) {
        let ns=self.start.elapsed().as_nanos() as u64;
        self.p.depth.set(self.p.depth.get()-1);
        let mut times=self.p.times.borrow_mut();
        let e=times.entry(self.key).or_default(); e.0+=1; e.1+=ns;
        if self.outer { let e=times.entry("outer_union").or_default(); e.0+=1; e.1+=ns; }
    }
}
// Last field of TypeContext. Runs after automatic destruction of earlier fields.
// This measures that context's field teardown, NOT the last release of every
// graph: Env/registry owners outside the context may still retain shared data.
#[derive(Default)]
pub(crate) struct Teardown { start:Cell<Option<Instant>>, name:RefCell<String> }
impl Teardown {
    pub fn start(&self, p: &EnvProbe) {
        *self.name.borrow_mut()=p.name.borrow().clone();
        self.start.set(Some(Instant::now()));
    }
}
impl Drop for Teardown {
    fn drop(&mut self) {
        if let Some(start)=self.start.get() {
            eprintln!("[env-teardown] {}",serde_json::json!({"module":self.name.borrow().as_str(),"fields_ns":start.elapsed().as_nanos() as u64}));
        }
    }
}
// Local query wrapper explicitly times destruction before its enclosing scope
// ends. Owned returned declarations are not destroyed or timed here.
pub(crate) struct ResolutionEnv<'a> {
    pub value: Option<crate::cmi::persistent_env::PersistentEnv>,
    p: &'a EnvProbe,
}
impl<'a> ResolutionEnv<'a> {
    pub fn new(ctx: &'a TypeContext, f: impl FnOnce() -> Option<crate::cmi::persistent_env::PersistentEnv>) -> Self {
        let scope=ctx.env_probe.scope("wrapper_clone");
        let value=f();
        drop(scope);
        Self {value,p:&ctx.env_probe}
    }
}
impl Drop for ResolutionEnv<'_> {
    fn drop(&mut self) {
        let _scope=self.p.scope("wrapper_drop");
        drop(self.value.take());
    }
}
fn attrs(p: &EnvProbe, a: &[super::decl::Attribute]) {
    use super::decl::AttributePayload;
    p.add("attribute_container_elements",a.len());
    for x in a {
        p.add("attribute_name_bytes",x.attr_name.txt.len());
        match &x.attr_payload {
            AttributePayload::Empty|AttributePayload::Int(_)|AttributePayload::Bool(_)=>{},
            AttributePayload::Str(s)|AttributePayload::IntLiteral(s)|AttributePayload::Float(s)|AttributePayload::BigInt(s)|AttributePayload::Ident(s)=>p.add("attribute_payload_string_bytes",s.len()),
            AttributePayload::Deprecated {reason,..}=>p.add("attribute_payload_string_bytes",reason.len()),
            AttributePayload::Structure(xs)=> {p.add("attribute_pairs",xs.len()); for (a,b) in xs {p.add("attribute_payload_string_bytes",a.len()+b.len());}}
        }
    }
}
pub(crate) fn declaration(ctx: &TypeContext, d: &super::decl::TypeDeclaration) {
    use super::decl::{TypeKind, ConstructorArguments, TypeInlinedType};
    let p=&ctx.env_probe;
    p.add("decl_clones",1);
    p.add("decl_param_handles",d.type_params.len());
    p.add("decl_variance_elements",d.type_variance.len());
    p.add("decl_attributes",d.type_attributes.len()); attrs(p,&d.type_attributes);
    p.add("decl_inlined_entries",d.type_inlined_types.len());
    match &d.type_kind {
        TypeKind::TypeRecord(labels,_) => {p.add("decl_record_labels",labels.len()); for l in labels {p.add("decl_label_attributes",l.ld_attributes.len());attrs(p,&l.ld_attributes);}},
        TypeKind::TypeVariant(cs,_) => {p.add("decl_constructors",cs.len()); for c in cs {
            p.add("decl_constructor_attributes",c.cd_attributes.len());attrs(p,&c.cd_attributes);
            match &c.cd_args { ConstructorArguments::CstrTuple(args)=>p.add("decl_constructor_arg_handles",args.len()), ConstructorArguments::CstrRecord(ls)=>p.add("decl_inline_constructor_labels",ls.len()) }
        }},
        TypeKind::TypeAbstract|TypeKind::TypeOpen=>{}
    }
    for i in &d.type_inlined_types { match i { TypeInlinedType::Record {labels,..}=>p.add("decl_inlined_labels",labels.len()) } }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cloned_thunks_have_distinct_identity() {
        let p=EnvProbe::default(); let a=ThunkToken::default(); let first=a.get(&p);
        assert_eq!(first,a.get(&p)); assert_ne!(first,a.clone().get(&p));
    }
    #[test]
    fn query_keys_and_scope_union() {
        let p=EnvProbe::default(); let path=Path::pident(crate::ident::Ident::create_persistent("X"));
        p.query(1,&path,"t","find_type");p.query(1,&path,"t","find_type");
        p.query(2,&path,"t","find_type");p.query(1,&path,"t","probe_module_descr");
        { let _a=p.scope("a"); {let _b=p.scope("b");} }
        assert_eq!(p.queries.borrow().len(),3); assert_eq!(p.stats.borrow()["query_repeat_key"],1);
        assert_eq!(p.times.borrow()["outer_union"].0,1); assert_eq!(p.depth.get(),0);
    }
}
'''
p=S/'compiler-rust/src/types/env_probe.rs'; p.write_text(probe)
changes.extend(difflib.unified_diff([],probe.splitlines(True),fromfile='/dev/null',tofile='b/compiler-rust/src/types/env_probe.rs'))
edit('compiler-rust/src/types/mod.rs', lambda s: replace(s,'pub(crate) mod env_lazy;', 'pub(crate) mod env_lazy;\npub(crate) mod env_probe;'))
def context(s):
    # Last field is important: Teardown::drop must run after all actual fields.
    start=s.index('pub struct TypeContext {'); end=s.index('\n}\n',start)
    s=s[:end]+'\n    pub(crate) env_probe: super::env_probe::EnvProbe,\n    probe_teardown: super::env_probe::Teardown,'+s[end:]
    s=replace(s,'            types: TypeArena::new(),','            types: TypeArena::new(),\n            env_probe: super::env_probe::EnvProbe::default(),\n            probe_teardown: super::env_probe::Teardown::default(),')
    s=body(s,'pub(crate) fn set_persistent_env(', '        if let Some(name)=env.ownership_module_name() {self.env_probe.name(name);}\n')
    s=body(s,'pub(crate) fn persistent_env_clone(', '        let _scope=self.env_probe.scope("all_persistent_clone");\n        if let Some(env)=self.persistent_env.borrow().as_ref() {env.ownership_payload(&self.env_probe);}\n')
    assert 'impl Drop for TypeContext' not in s
    return s+'''\nimpl Drop for TypeContext {
    fn drop(&mut self) {
        self.env_probe.report(self.type_expr_count());
        self.probe_teardown.start(&self.env_probe);
    }
}
'''
edit('compiler-rust/src/types/context.rs',context)
def persistent(s):
    needle='impl PersistentEnv {'
    extra=r'''
    pub(crate) fn ownership_module_name(&self) -> Option<&str> {self.compiling_module.as_deref()}
    pub(crate) fn ownership_payload(&self,p:&crate::types::env_probe::EnvProbe) {
        p.add("persistent_wrapper_observed",1);
        p.add("persistent_alias_local_entries",self.alias_prefix_rewrites.local.len());
        p.add("persistent_memory_override_entries",self.in_memory_module_overrides.len());
        p.add("persistent_source_override_entries",self.source_fallback_path_overrides.len());
        p.add("persistent_portable_override_entries",self.portable_cache_overrides.len());
        p.add("persistent_hidden_entries",self.hidden_modules.len());
        p.add("persistent_prepared_entries",self.prepared_cached_alias_rewrites.len());
        p.add("persistent_owned_key_bytes",self.alias_prefix_rewrites.local.keys().map(String::len).sum::<usize>()
            +self.in_memory_module_overrides.keys().map(String::len).sum::<usize>()
            +self.source_fallback_path_overrides.keys().map(String::len).sum::<usize>()
            +self.portable_cache_overrides.keys().map(String::len).sum::<usize>()
            +self.hidden_modules.iter().map(String::len).sum::<usize>()
            +self.prepared_cached_alias_rewrites.iter().map(String::len).sum::<usize>()
            +self.compiling_module.as_ref().map_or(0,String::len));
        // Arc-backed registries, paths, errors and caches are not deep-copied.
        p.add("persistent_source_override_value_bytes",self.source_fallback_path_overrides.values().map(|v|v.as_os_str().len()).sum());
        p.add("persistent_shared_registry_fields",3);
    }
'''
    return replace(s,needle,needle+extra)
edit('compiler-rust/src/cmi/persistent_env.rs',persistent)
def ctype(s):
    a=s.index("fn resolve_type_item_through_env<'a>("); b=s.index("\nfn resolve_type_through_env<'a>",a)
    part=s[a:b]
    part=body(part,"fn resolve_type_item_through_env<'a>(",'    let _probe_scope=ctx.env_probe.scope("resolve_type_item");\n')
    part=part.replace('let mut persistent_env = in_process_module_resolution_env(ctx);','let mut persistent_env = super::env_probe::ResolutionEnv::new(ctx, || in_process_module_resolution_env(ctx));')
    part=part.replace('&mut persistent_env,','&mut persistent_env.value,')
    part=replace(part,'let resolved_decl = (*decl).clone();','let resolved_decl = {\n            let _clone=ctx.env_probe.scope("decl_transport_clone");\n            let result=(*decl).clone();\n            result\n        };\n        super::env_probe::declaration(ctx, &decl);')
    part=replace(part,'let mut target_decl = resolved_decl.clone();','super::env_probe::declaration(ctx, &resolved_decl);\n                let mut target_decl = resolved_decl.clone();')
    part=replace(part,'let alias_target_for_strengthening = if strengthen_alias_types {','let alias_target_for_strengthening = if strengthen_alias_types {\n            let _alias=ctx.env_probe.scope("alias_strengthening_query");')
    return s[:a]+part+s[b:]
edit('compiler-rust/src/types/ctype.rs',ctype)
def typecore(s):
    s=body(s,"fn lookup_type_in_resolved_path_with_cache_mode<'a>(",'''    let _probe=ctx.env_probe.scope("lookup_type");
    ctx.env_probe.query(env.id(),parent_module_path,type_name,cache_mode.counter_name());
''')
    a=s.index("fn lookup_type_in_resolved_path_with_cache_mode<'a>(");b=s.index('\nfn lookup_type_decl_in_resolved_path_with_cache_mode',a)
    part=s[a:b]
    part=replace(part,'return Some(cached);','ctx.env_probe.add("resolved_type_hit",1);\n        return Some(cached);')
    part=replace(part,'let find_in_sig = |sig: &crate::types::decl::Signature| {','let find_in_sig = |sig: &crate::types::decl::Signature| {\n            let _scan=ctx.env_probe.scope("persistent_type_scan");\n            ctx.env_probe.add("persistent_sig_scan_items",sig.len());')
    part=part.replace('Arc::new(sig_decl.clone())','{super::env_probe::declaration(ctx,sig_decl); Arc::new(sig_decl.clone())}')
    part=part.replace('Arc::new(decl.clone())','{super::env_probe::declaration(ctx,decl); Arc::new(decl.clone())}')
    s=s[:a]+part+s[b:]
    s=body(s,"pub(crate) fn resolve_module_type<'b>(",'        let _probe=ctx.env_probe.scope("raw_module_resolve");\n')
    for name,label in [("pub(crate) fn with_resolved_module_components_for_path_with_cache_mode<'a, R>(","resolved_components"),("fn qualify_resolved_signature_for_access_path_inner<'a>(","qualification"),("pub(crate) fn copy_lookup_signature_for_subst(","signature_copy"),("fn build_module_signature_for_path<'a>(","build_signature")]:
        s=body(s,name,f'    let _probe=ctx.env_probe.scope("{label}");\n')
    return s
edit('compiler-rust/src/types/typecore.rs',typecore)
def lazy(s):
    s=replace(s,'struct StructureComponentTables {','struct StructureComponentTables {\n    probe_id: u64,')
    # Every table literal is created with a TypeContext in scope.
    s=s.replace('tables: Arc::new(StructureComponentTables {','tables: Arc::new(StructureComponentTables {\n                probe_id: ctx.env_probe.token(),')
    s=replace(s,'pub(crate) struct StoredModuleComponents {','pub(crate) struct StoredModuleComponents {\n    probe_token: super::env_probe::ThunkToken,')
    s=replace(s,'            seed_env: Box::new(seed_env),','            seed_env: Box::new(seed_env),\n            probe_token: super::env_probe::ThunkToken::default(),')
    s=body(s,"pub(crate) fn with_components<'a, R>(",'''        let _probe=ctx.env_probe.scope("stored_components");
        let token=self.probe_token.get(&ctx.env_probe);
        ctx.env_probe.component(token,"",cache_mode.counter_name());
        ctx.env_probe.add("stored_parent_root_requests",usize::from(self.parent_context.is_some()));
''')
    s=replace(s,'if let Some(components) = self.cached.get().cloned() {','if let Some(components) = self.cached.get().cloned() {\n            ctx.env_probe.add("stored_cache_hit",1);')
    s=replace(s,'        let components = Arc::new(build_local_module_components(','        ctx.env_probe.add(if cache_mode.publishes() {"stored_real_build"} else {"stored_probe_build"},1);\n        let components = Arc::new(build_local_module_components(')
    s=body(s,"fn build_local_module_components<'a>(",'''    let _probe=super::env_probe::node_scope(ctx,"local_construction");
''')
    for name,label in [('pub(crate) fn lookup_value_for_access(', 'value_query'),('pub(crate) fn lookup_constructors(', 'constructor_query'),('pub(crate) fn lookup_labels(', 'label_query')]:
        s=body(s,name,f'''        let _probe=ctx.env_probe.scope("{label}");
        ctx.env_probe.component(self.tables.probe_id,name,"{label}");
''')
    s=body(s,'fn new_with_child_components_arc_and_value_source_prefix_inner(','''        let _probe=super::env_probe::node_scope(ctx,"table_assembly");
        ctx.env_probe.add("table_signature_items",signature.len());
        ctx.env_probe.add("table_child_roots",child_components.len());
''')
    s=body(s,'fn build_constructors_for_name(', '    let _probe=super::env_probe::node_scope(ctx,"constructor_bucket_build");\n    ctx.env_probe.add("constructor_scan_items",signature.len());\n')
    s=body(s,'fn build_labels_for_name(', '    let _probe=super::env_probe::node_scope(ctx,"label_bucket_build");\n    ctx.env_probe.add("label_scan_items",signature.len());\n')
    s=body(s,'fn force_component_module_declaration_thunk(', '    let _probe=super::env_probe::node_scope(ctx,"module_declaration_force");\n')
    s=replace(s, '        let mut desc = super::typecore::copy_lookup_value_description_for_subst(desc, ctx);', '        let _first=super::env_probe::node_scope(ctx,"value_first_build");\n        let mut desc = super::typecore::copy_lookup_value_description_for_subst(desc, ctx);')
    return s
edit('compiler-rust/src/types/env_lazy.rs',lazy)
(D/'probe.patch').write_text(''.join(changes))
(D/'source-instrumented.json').write_text(json.dumps({str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for c in ['compiler-rust','rewatch'] for p in (S/c).rglob('*') if p.is_file()},sort_keys=True))
print('Archived probe written:', S)
