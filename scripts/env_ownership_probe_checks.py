#!/usr/bin/env python3
"""Complete probe identity/order tests and preserve the exact review patch."""
import difflib,hashlib,json,subprocess
from pathlib import Path
R=Path('/Users/jake/checkouts/rescript-rust');D=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership');S=D/'probe-source';assert Path.cwd()==R
p=S/'compiler-rust/src/types/env_probe.rs';s=p.read_text();s=s.replace("fn node_scope(ctx: &TypeContext, key: &'static str) -> NodeScope<'_>","fn node_scope<'a>(ctx: &'a TypeContext, key: &'static str) -> NodeScope<'a>")
s+='''
#[cfg(test)]
mod identity_tests {
    use super::*;
    #[test]
    fn same_spelling_different_stamp_is_not_same_query() {
        let p=EnvProbe::default();let ids=crate::context::IdGenerator::new();
        let a=Path::pident(ids.create("Same"));let b=Path::pident(ids.create("Same"));
        assert_eq!(a.name(),b.name());assert!(!a.same(&b));
        p.query(7,&a,"t","find_type");p.query(7,&b,"t","find_type");
        assert_eq!(p.queries.borrow().len(),2);
    }
    #[test]
    fn signature_tokens_share_without_owning_graph() {
        let p=EnvProbe::default();let s=std::sync::Arc::new(Vec::new());
        let a=p.signature(&s);let copy=s.clone();assert_eq!(a,p.signature(&copy));
        assert_eq!(std::sync::Arc::strong_count(&s),2);drop(copy);
        assert_eq!(std::sync::Arc::strong_count(&s),1);
        drop(s);assert_eq!(p.signatures.borrow().values().next().unwrap().0.strong_count(),0);
        assert_ne!(a,p.signature(&std::sync::Arc::new(Vec::new())));
    }
    #[test]
    fn destructor_then_fields_in_declaration_order() {
        struct Mark<'a>(&'a RefCell<Vec<&'static str>>, &'static str);
        impl Drop for Mark<'_> {fn drop(&mut self){self.0.borrow_mut().push(self.1);}}
        struct Owner<'a>{first:Mark<'a>,last:Mark<'a>}
        impl Drop for Owner<'_>{fn drop(&mut self){self.first.0.borrow_mut().push("entry");}}
        let events=RefCell::new(Vec::new());
        let owner=Owner{first:Mark(&events,"fields"),last:Mark(&events,"sentinel")};
        assert_eq!(owner.last.1,"sentinel");drop(owner);
        assert_eq!(*events.borrow(),vec!["entry","fields","sentinel"]);
    }
}
''';p.write_text(s)
p=S/'compiler-rust/src/types/env_lazy.rs';s=p.read_text();s+='''
#[cfg(test)]
mod ownership_probe_tests {
    use super::*;
    #[test]
    fn cloned_views_share_table_but_cloned_thunks_are_distinct() {
        let ctx=super::super::context::TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let path=Path::pident(Ident::create_persistent("Probe"));
        let view=QualifiedModuleComponents::new(path.clone(),Vec::new(),&ctx);
        let copy=view.clone();assert_eq!(view.tables.probe_id,copy.tables.probe_id);
        assert!(Arc::ptr_eq(&view.tables,&copy.tables));
        let md=ModuleDeclaration {md_type:ModuleType::MtySignature(Vec::new()),md_attributes:vec![],md_loc:crate::location::Location::none(),md_path:None};
        let thunk=StoredModuleComponents::new(super::super::env::Env::empty(),path,md);
        let id=thunk.probe_token.get(&ctx.env_probe);
        assert_ne!(id,thunk.clone().probe_token.get(&ctx.env_probe));
        assert!(thunk.cached.set(Arc::new(view)).is_ok());
        let cloned=thunk.clone();assert_ne!(id,cloned.probe_token.get(&ctx.env_probe));
        assert!(Arc::ptr_eq(thunk.cached.get().unwrap(),cloned.cached.get().unwrap()));
    }
}
''';p.write_text(s)
# Check actual TypeContext field declaration order, rather than relying on comments.
s=(S/'compiler-rust/src/types/context.rs').read_text();a=s.index('pub struct TypeContext {');b=s.index('\n}\n',a)
assert s[a:b].rstrip().endswith('probe_teardown: super::env_probe::Teardown,')
changes=[]
for p in sorted((S/'compiler-rust/src').rglob('*.rs')):
 rel=p.relative_to(S).as_posix();r=subprocess.run(['git','show','HEAD:'+rel],cwd=R,capture_output=True);old=r.stdout.decode() if r.returncode==0 else '';new=p.read_text()
 if old!=new:changes.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+rel if r.returncode==0 else '/dev/null',tofile='b/'+rel))
(D/'probe-review.patch').write_text(''.join(changes))
(D/'source-review.json').write_text(json.dumps({str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for c in ['compiler-rust','rewatch'] for p in (S/c).rglob('*') if p.is_file() and 'target' not in p.relative_to(S).parts},sort_keys=True))
