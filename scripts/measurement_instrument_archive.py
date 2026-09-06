#!/usr/bin/env python3
"""Apply measurement-only probes to the disposable archived A sources.
Never run on the shared worktree. Counters are context-owned Cells; no forcing,
new unsafe code, global counters, or change to timing executables.
"""
from pathlib import Path
import difflib
D=Path('/tmp/rescript-measure-rebaseline-542')
S=D/'historical-source/compiler-rust/src'
changes=[]
def edit(name,transform):
    p=S/name; old=p.read_text(); new=transform(old)
    if old==new: raise RuntimeError(name)
    p.write_text(new); changes.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/compiler-rust/src/'+name,tofile='b/compiler-rust/src/'+name))
def context(s):
    s=s.replace('    types: TypeArena,','    types: TypeArena,\n    measure_clones: Cell<u64>,\n    pub(crate) measure_internal: Cell<(u64,u64,u64)>,')
    s=s.replace('            types: TypeArena::new(),','            types: TypeArena::new(),\n            measure_clones: Cell::new(0),\n            measure_internal: Cell::new((0,0,0)),')
    s=s.replace('        TypeDescSnapshot(self.types.get(r).desc().clone())','        self.measure_clones.set(self.measure_clones.get()+1);\n        TypeDescSnapshot(self.types.get(r).desc().clone())')
    s+='''
// Measurement-only: census of every arena node at context destruction, NOT live
// reachability or total heap. No links followed, descriptors cloned or Env forced.
impl Drop for TypeContext {
    fn drop(&mut self) {
        let mut kinds=[0usize;14];
        let mut lengths=[0usize;6];
        let mut labels=[0usize;3];
        let mut arg_capacity=0usize;
        let mut capacity_bytes=0usize;
        for i in 0..self.types.len() {
            let d=self.types.get(TypeExprRef::from_usize(i)).desc();
            let (k, len, cap)=match &*d {
                TypeDesc::Tvar(_) => (0,None,0),
                TypeDesc::Tarrow{args,..} => (1,Some(args.len()),args.capacity()*std::mem::size_of::<super::type_expr::TypeArg>()),
                TypeDesc::Ttuple(a) => (2,Some(a.len()),a.capacity()*4),
                TypeDesc::Tconstr{args,..} => (3,Some(args.len()),args.capacity()*4),
                TypeDesc::Tobject{..} => (4,None,0),
                TypeDesc::Tfield{..} => (5,None,0),
                TypeDesc::Tnil => (6,None,0),
                TypeDesc::Tlink(_) => (7,None,0),
                TypeDesc::Tsubst(_) => (8,None,0),
                TypeDesc::Tvariant(row) => (9,Some(row.row_fields.len()),row.row_fields.capacity()*std::mem::size_of::<(String,super::type_expr::RowField)>()),
                TypeDesc::Tunivar(_) => (10,None,0),
                TypeDesc::Tpoly{vars,..} => (11,Some(vars.len()),vars.capacity()*4),
                TypeDesc::Tpackage{args,..} => (12,Some(args.len()),args.capacity()*4),
            };
            if let TypeDesc::Tarrow{args,..}=&*d {
                arg_capacity+=args.capacity()*std::mem::size_of::<super::type_expr::TypeArg>();
                for arg in args {labels[match arg.lbl {ArgLabel::Nolabel=>0,ArgLabel::Labelled(_)=>1,ArgLabel::Optional(_)=>2}]+=1;}
            }
            kinds[k]+=1; capacity_bytes+=cap;
            if let Some(n)=len { lengths[match n {0=>0,1=>1,2=>2,3=>3,4..=8=>4,_=>5}]+=1; }
        }
        eprintln!("[measurement-args] labels={:?} capacity_bytes={}",labels,arg_capacity);
        eprintln!("[measurement-census] nodes={} kinds={:?} lengths={:?} selected_vec_capacity_bytes={} get_desc_clones={} internal={:?} sizes={:?}",self.types.len(),kinds,lengths,capacity_bytes,self.measure_clones.get(),self.measure_internal.get(),[
            std::mem::size_of::<TypeExpr>(),std::mem::size_of::<TypeDesc>(),
            std::mem::size_of::<super::type_expr::RowDesc>(),std::mem::size_of::<super::type_expr::TypeArg>(),
            std::mem::size_of::<crate::lambda::Lambda>(),std::mem::size_of::<crate::js_ir::Expression>(),
            std::mem::size_of::<crate::js_ir::ExpressionDesc>()]);
    }
}
'''
    return s
def portable(s):
    needle=') -> Signature {\n    // Portable entries already'
    assert needle in s
    s=s.replace(needle,') -> Signature {\n    let measure_start=std::time::Instant::now();\n    // Portable entries already')
    needle='    remap_signature_refs(&mut sig, remap, &layout_remap);\n    sig'
    assert needle in s
    return s.replace(needle,'    remap_signature_refs(&mut sig, remap, &layout_remap);\n    let (calls,nodes,ns)=ctx.measure_internal.get();\n    ctx.measure_internal.set((calls+1,nodes+graph.entries.len() as u64,ns+measure_start.elapsed().as_nanos() as u64));\n    sig')
edit('types/context.rs',context)
edit('cmi/portable_types.rs',portable)
(D/'measurement-only.patch').write_text(''.join(changes))

# Scheduler event trace is dispatcher-owned. Timestamps are relative to this
# scheduler invocation; events include queue residence, not worker CPU time.
p=D/'historical-source/rewatch/src/build/compile.rs';old=p.read_text();new=old
needle='    rayon::in_place_scope(|scope| {\n        let mut in_flight: usize = 0;'
assert needle in new
new=new.replace(needle,'''    let measure_epoch=Instant::now();
    for name in compile_universe.iter() {
        let module=build_state_ref.modules.get(name).unwrap();
        eprintln!("[measurement-deps] module={} deps={:?}",name,module.deps);
    }
'''+needle)
for needle,event in [
('                    let module_name = pre_js_msg.module_name.clone();','startjs'),
('                let module_name = work.module_name.clone();','startpre'),
('                        let module_name = msg.module_name.clone();\n                        let is_clean = apply_signature_ready','sig'),
('                        let module_name = msg.module_name.clone();\n                        let pending_deps_for_js','pre'),
('                        let ready_name = msg.module_name;','meta'),
('                        let finished_name = msg.module_name.clone();','end')]:
    assert needle in new,needle
    first,*rest=needle.split('\n')
    var='ready_name' if event=='meta' else 'finished_name' if event=='end' else 'module_name'
    insert=first+'\n'+f'                        eprintln!("[measurement-event] ns={{}} event={event} module={{}}",measure_epoch.elapsed().as_nanos(),{var});'
    if rest:insert+='\n'+'\n'.join(rest)
    new=new.replace(needle,insert)
p.write_text(new)
changes.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/rewatch/src/build/compile.rs',tofile='b/rewatch/src/build/compile.rs'))
p=D/'historical-source/rewatch/src/build.rs';old=p.read_text()
needle='    let timing_parse_total = timing_parse_start.elapsed();'
new=old.replace(needle,needle+'\n    eprintln!("[measurement-barrier] ast_ms={} parse_deps_ms={}",timing_ast_elapsed.as_secs_f64()*1000.0,timing_parse_total.as_secs_f64()*1000.0);')
assert new!=old;p.write_text(new)
changes.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/rewatch/src/build.rs',tofile='b/rewatch/src/build.rs'))
(D/'measurement-only.patch').write_text(''.join(changes))
