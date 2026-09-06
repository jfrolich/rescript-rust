#!/usr/bin/env python3
"""Instrument only fresh archived D sources, never production targets."""
import difflib, hashlib, json, subprocess, sys
from pathlib import Path
D=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round')
S=D/'probe-source'
def inventory():
    return {str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for crate in ('compiler-rust','rewatch') for p in sorted((S/crate).rglob('*')) if p.is_file() and 'target' not in p.relative_to(S).parts}
if sys.argv[1]=='restore':
    for name in ('context.rs','ctype.rs'):(S/'compiler-rust/src/types'/name).write_bytes((D/('original-'+name)).read_bytes())
    after=inventory();(D/'probe-source-restored.json').write_text(json.dumps(after,sort_keys=True))
    assert after==json.loads((D/'probe-source-before.json').read_text())
    sys.exit()
assert sys.argv[1]=='prepare' and not S.exists()
S.mkdir()
with (D/'probe-source.tar').open('wb') as out:subprocess.run(['git','archive','5dc38ba2154e158d43436ada2142a13eef9f2c8c'],stdout=out,check=True)
subprocess.run(['tar','-xf',str(D/'probe-source.tar'),'-C',str(S)],check=True)
(D/'probe-source-before.json').write_text(json.dumps(inventory(),sort_keys=True))
changes=[]
def edit(path, transform):
    p=S/path;old=p.read_text();new=transform(old);assert old!=new
    (D/('original-'+p.name)).write_text(old)
    changes.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
    p.write_text(new)
def context(s):
    assert 'impl Drop for TypeContext' not in s
    s=s.replace('    types: TypeArena,','    types: TypeArena,\n    pub(crate) architecture_copy: Cell<[u64; 32]>,\n    pub(crate) architecture_depth: Cell<u64>,')
    s=s.replace('            types: TypeArena::new(),','            types: TypeArena::new(),\n            architecture_copy: Cell::new([0;32]),\n            architecture_depth: Cell::new(0),')
    return s+'''
// Archived measurement only. Explicit per-context state; no traversal at drop.
impl Drop for TypeContext {
    fn drop(&mut self) {
        eprintln!("[architecture-copy] nodes={} counters={:?}", self.type_expr_count(), self.architecture_copy.get());
    }
}
'''
def ctype(s):
    needle='pub(crate) fn copy_type_cached(\n';assert s.count(needle)==1
    s=s.replace(needle,'''pub(crate) fn copy_type_cached(ctx: &TypeContext, ty: TypeExprRef, cache: &mut CopyCache) -> TypeExprRef {
    let depth=ctx.architecture_depth.get();
    let start=if depth==0 {Some((std::time::Instant::now(),ctx.type_expr_count()))} else {None};
    ctx.architecture_depth.set(depth+1);
    let mut c=ctx.architecture_copy.get();c[0]+=1;ctx.architecture_copy.set(c);
    let result=architecture_copy_inner(ctx,ty,cache);
    ctx.architecture_depth.set(depth);
    if let Some((start,nodes))=start {
        let mut c=ctx.architecture_copy.get();c[1]+=1;c[2]+=start.elapsed().as_nanos() as u64;
        c[3]+=(ctx.type_expr_count()-nodes) as u64;c[4]+=cache.nodes.len() as u64;
        c[5]+=cache.nodes.capacity() as u64;c[6]=c[6].max(cache.nodes.len() as u64);
        ctx.architecture_copy.set(c);
    }
    result
}

fn architecture_copy_inner(
''')
    a=s.index('fn architecture_copy_inner(');head=s[:a];body=s[a:]
    body=body.replace('        return marker.tuple;','        let mut c=ctx.architecture_copy.get();c[7]+=1;ctx.architecture_copy.set(c);\n        return marker.tuple;',1)
    body=body.replace('    if let Some(&cached) = cache.nodes.get(&ty) {','    let mut c=ctx.architecture_copy.get();c[8]+=1;ctx.architecture_copy.set(c);\n    if let Some(&cached) = cache.nodes.get(&ty) {\n        let mut c=ctx.architecture_copy.get();c[9]+=1;ctx.architecture_copy.set(c);',1)
    body=body.replace('                return marker.variant;','                let mut c=ctx.architecture_copy.get();c[10]+=1;ctx.architecture_copy.set(c);\n                return marker.variant;',1)
    needle='    // Execute the action without holding the borrow.\n';assert body.count(needle)==1
    diagnostic='''    // Actual selected CopyAction, after direct clones. Not a get_desc census.
    let (kind,elements,path)=match &action {
        CopyAction::ReturnSelf=>(11,0,0), CopyAction::NewVar(_)=>(12,0,0),
        CopyAction::NewUnivar(_)=>(13,0,0), CopyAction::Arrow{args,..}=>(14,args.len(),0),
        CopyAction::Tuple(args)=>(15,args.len(),0), CopyAction::Constr{args,..}=>(16,args.len(),1),
        CopyAction::Object{name,..}=>(17,name.as_ref().map_or(0,|(_,a)|a.len()),usize::from(name.is_some())),
        CopyAction::Field{..}=>(18,0,0),CopyAction::Nil=>(19,0,0),CopyAction::Poly{vars,..}=>(20,vars.len(),0),
        CopyAction::Variant(row)=>(21,row.row_fields.len(),usize::from(row.row_name.is_some())),
        CopyAction::Package{args,..}=>(22,args.len(),1),CopyAction::Link(_)=>(23,0,0),CopyAction::Forget(_)=>(24,0,0),
    };
    let mut c=ctx.architecture_copy.get();c[kind]+=1;c[25]+=elements as u64;c[26]+=path as u64;
    if let CopyAction::Arrow{args,..}=&action {c[27]+=args.len() as u64;c[28]+=args.iter().filter(|a|!matches!(a.label(),crate::types::asttypes::ArgLabel::Nolabel)).count() as u64;}
    ctx.architecture_copy.set(c);

'''
    return head+body.replace(needle,diagnostic+needle)
edit('compiler-rust/src/types/context.rs',context)
edit('compiler-rust/src/types/ctype.rs',ctype)
(D/'probe.patch').write_text(''.join(changes))
(D/'probe-source-instrumented.json').write_text(json.dumps(inventory(),sort_keys=True))
