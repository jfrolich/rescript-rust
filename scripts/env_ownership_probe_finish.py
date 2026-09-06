#!/usr/bin/env python3
"""Finish archived diagnostic accounting. Run after env_ownership_probe.py."""
import difflib,hashlib,json,subprocess
from pathlib import Path
R=Path('/Users/jake/checkouts/rescript-rust');D=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership');S=D/'probe-source';assert Path.cwd()==R
assert not (D/'probe-final.patch').exists()
def edit(rel,f):
 p=S/'compiler-rust/src'/rel;s=p.read_text();n=f(s);assert s!=n,rel;p.write_text(n)
def rep(s,a,b):
 assert s.count(a)==1,(a[:90],s.count(a));return s.replace(a,b)
def probe(s):
 s=rep(s,'times: RefCell<BTreeMap<&\'static str, (u64, u64)>>,','times: RefCell<BTreeMap<&\'static str, (u64, u64, u64)>>,\n    child_ns: RefCell<Vec<u64>>,\n    signatures: RefCell<BTreeMap<usize,(std::sync::Weak<super::decl::Signature>,u64)>>,')
 s=rep(s,'let depth=self.depth.get(); self.depth.set(depth+1);','let depth=self.depth.get(); self.depth.set(depth+1);\n        self.child_ns.borrow_mut().push(0);')
 s=rep(s,'let e=times.entry(self.key).or_default(); e.0+=1; e.1+=ns;','''let child=self.p.child_ns.borrow_mut().pop().expect("scope stack");
        if let Some(parent)=self.p.child_ns.borrow_mut().last_mut() {*parent+=ns;}
        let e=times.entry(self.key).or_default(); e.0+=1; e.1+=ns; e.2+=ns.saturating_sub(child);''')
 s=rep(s,'e.0+=1; e.1+=ns; }\n    }\n}', 'e.0+=1; e.1+=ns; e.2+=ns; }\n    }\n}')
 s=rep(s,'    pub fn report(&self, nodes: usize) {','''    pub fn signature(&self, sig:&std::sync::Arc<super::decl::Signature>) -> u64 {
        // The Weak keeps this allocation's header alive, preventing address reuse.
        // Address is only an index; ptr_eq verifies identity. It owns no graph.
        let weak=std::sync::Arc::downgrade(sig);
        let key=std::sync::Arc::as_ptr(sig) as usize;
        let mut table=self.signatures.borrow_mut();
        if let Some((old,id))=table.get(&key) {assert!(old.ptr_eq(&weak));return *id;}
        let id=self.token(); table.insert(key,(weak,id));id
    }
    pub fn clear_instrumentation(&mut self) {
        self.queries.get_mut().clear(); self.queries.get_mut().shrink_to_fit();
        self.components.get_mut().clear(); self.components.get_mut().shrink_to_fit();
        self.signatures.get_mut().clear(); self.stats.get_mut().clear();self.times.get_mut().clear();
        self.child_ns.get_mut().clear();self.child_ns.get_mut().shrink_to_fit();
    }
    pub fn report(&self, nodes: usize) {''')
 s += '''
// An endpoint census follows existing references only, never forces a thunk.
// Tokens are scoped to the containing context report; never compare across reports.
#[derive(Default)]
pub(crate) struct Roots {
    pub envs: HashSet<u64>, pub thunks: HashSet<u64>, pub tables: HashSet<u64>,
    pub signatures:BTreeMap<u64,(usize,usize)>, pub forced:usize, pub parents:usize,
}
impl Roots {
    pub fn signature(&mut self,p:&EnvProbe,s:&std::sync::Arc<super::decl::Signature>) {
        self.signatures.insert(p.signature(s),(s.len(),std::sync::Arc::strong_count(s)));
    }
    pub fn report(&self,p:&EnvProbe,phase:&str) {
        eprintln!("[env-roots] {}",serde_json::json!({"module":p.name.borrow().as_str(),"phase":phase,
          "envs":self.envs.len(),"thunks":self.thunks.len(),"forced_thunks":self.forced,"parent_links":self.parents,
          "tables":self.tables.len(),"signatures":self.signatures}));
    }
}
'''
 # Teardown consumes instrumentation tables first; name is still intact.
 return s
edit('types/env_probe.rs',probe)
def context(s):
 s=rep(s,'        let _scope=self.env_probe.scope("all_persistent_clone");\n        if let Some(env)=self.persistent_env.borrow().as_ref() {env.ownership_payload(&self.env_probe);}', '        if let Some(env)=self.persistent_env.borrow().as_ref() {let _payload=self.env_probe.scope("wrapper_payload_scan");env.ownership_payload(&self.env_probe);}\n        let _scope=self.env_probe.scope("all_persistent_clone");')
 # All actual clones counted once, outer wrapper timer includes payload scan; report explicitly.
 needle='    pub(crate) fn persistent_env_clone(&self)'
 method='''    pub(crate) fn ownership_roots(&self,phase:&str,env:Option<&super::env::Env>) {
        let start=std::time::Instant::now();
        let mut roots=super::env_probe::Roots::default();
        if let Some(env)=env {env.ownership_roots(self,&mut roots);}
        for env in self.typed_envs.borrow().iter() {env.ownership_roots(self,&mut roots);}
        for sig in self.raw_module_sigs.borrow().values() {roots.signature(&self.env_probe,sig);}
        for sig in self.renamed_module_sigs.borrow().values() {roots.signature(&self.env_probe,sig);}
        for sig in self.raw_component_module_sigs.borrow().values() {roots.signature(&self.env_probe,sig);}
        for sig in self.gentype_raw_module_sigs.borrow().values() {roots.signature(&self.env_probe,sig);}
        for (_,sig) in self.resolved_module_sig_cache.borrow().values() {roots.signature(&self.env_probe,sig);}
        for components in self.qualified_module_components_cache.borrow().values() {components.ownership_roots(self,&mut roots);}
        roots.report(&self.env_probe,phase);
        self.env_probe.add("root_census_ns",start.elapsed().as_nanos() as usize);
    }

'''
 s=rep(s,needle,method+needle)
 s=rep(s,'        self.env_probe.report(self.type_expr_count());\n        self.probe_teardown.start(&self.env_probe);','''        self.ownership_roots("context_drop_entry",None);
        self.env_probe.report(self.type_expr_count());
        let cleanup=std::time::Instant::now();
        self.env_probe.clear_instrumentation();
        eprintln!("[env-probe-cleanup] {}",cleanup.elapsed().as_nanos());
        self.probe_teardown.start(&self.env_probe);''')
 return s
edit('types/context.rs',context)
def env(s):
 return s+'''
impl Env {
    pub(crate) fn ownership_roots(&self,ctx:&super::context::TypeContext,roots:&mut super::env_probe::Roots) {
        if !roots.envs.insert(self.id()) {return;}
        for (_,stored) in self.module_components.iter() {stored.ownership_roots(ctx,roots);}
    }
}
'''
edit('types/env.rs',env)
def lazy(s):
 s += '''
impl StoredModuleComponents {
    pub(crate) fn ownership_roots(&self,ctx:&super::context::TypeContext,roots:&mut super::env_probe::Roots) {
        let id=self.probe_token.get(&ctx.env_probe);
        if !roots.thunks.insert(id) {return;}
        self.seed_env.ownership_roots(ctx,roots);
        if let Some((_,sig))=&self.parent_context {roots.parents+=1;roots.signature(&ctx.env_probe,sig);}
        if let Some(image)=self.cached.get() {roots.forced+=1;image.ownership_roots(ctx,roots);}
    }
}
impl QualifiedModuleComponents {
    pub(crate) fn ownership_roots(&self,ctx:&super::context::TypeContext,roots:&mut super::env_probe::Roots) {
        if !roots.tables.insert(self.tables.probe_id) {return;}
        roots.signature(&ctx.env_probe,&self.signature);
        for (_,child) in self.tables.child_components.borrow().values().flatten() {child.ownership_roots(ctx,roots);}
    }
}
'''
 # Precisely drops temporary local image before enclosing timer ends.
 a=s.index("pub(crate) fn with_components<'a, R>(");b=s.index('    pub(crate) fn instantiate_functor_result_for_application',a);part=s[a:b]
 part=rep(part,'        Some(f(components.as_ref()))','''        let result=f(components.as_ref());
        if !cache_mode.publishes() {
            let _drop=ctx.env_probe.scope("temporary_image_drop");
            drop(components);
        }
        Some(result)''')
 s=s[:a]+part+s[b:]
 # Avoid instrumenting every creation with a full root walk: observe signature once.
 s=rep(s,'        ctx.env_probe.add("table_signature_items",signature.len());','        ctx.env_probe.signature(&signature);\n        ctx.env_probe.add("table_signature_items",signature.len());')
 return s
edit('types/env_lazy.rs',lazy)
def driver(s):
 a=s.index('pub fn compile_preprocessed_structure_in_process_until_js(');b=s.index('\npub fn ',a+8);part=s[a:b]
 part=rep(part,'    let mut tctx = TypeCheckContext::new(&type_ctx, arena);','    type_ctx.env_probe.name(module_name);\n    let mut tctx = TypeCheckContext::new(&type_ctx, arena);')
 part=rep(part,'    drop(env_setup_span);','    drop(env_setup_span);\n    type_ctx.ownership_roots("setup",Some(&env));\n    let probe_tc_start=std::time::Instant::now();')
 needle='    let mut inferred_implementation_coercion = None;'
 part=rep(part,needle,'''    type_ctx.env_probe.add("typecheck_elapsed_ns",probe_tc_start.elapsed().as_nanos() as usize);
    type_ctx.ownership_roots("after_typecheck",Some(&final_env));
'''+needle)
 # Raw phase timer is supplied by existing module timing, root census after lower.
 needle='    Ok(InProcessPreJsCompileResult {'
 part=rep(part,needle,'    type_ctx.ownership_roots("pre_js_exit",Some(&final_env));\n'+needle)
 return s[:a]+part+s[b:]
edit('driver.rs',driver)
# Preserve exact cumulative patch against uninstrumented main, including all additions.
changes=[]
for p in sorted((S/'compiler-rust/src').rglob('*.rs')):
 rel=p.relative_to(S).as_posix()
 before=subprocess.run(['git','show','HEAD:'+rel],cwd=R,capture_output=True)
 old=before.stdout.decode() if before.returncode==0 else ''
 new=p.read_text()
 if old!=new:changes.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+rel if before.returncode==0 else '/dev/null',tofile='b/'+rel))
(D/'probe-final.patch').write_text(''.join(changes))
(D/'source-final.json').write_text(json.dumps({str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for c in ['compiler-rust','rewatch'] for p in (S/c).rglob('*') if p.is_file() and 'target' not in p.relative_to(S).parts},sort_keys=True))
