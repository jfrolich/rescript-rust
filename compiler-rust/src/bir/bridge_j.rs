//! Post-pass JavaScript migration bridge. Explicit postorder work stacks keep
//! statement lists and expression chains off the Rust call stack. No JS arena
//! or source node handles are retained in the imported representation.
use super::bridge::Unsupported;
use super::*;
use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use crate::js_ir::op::{BinOp, LengthObject, MutableFlag, Number, UsedStats};
use crate::js_ir::{self as js, arena as j};
use crate::lambda::{SwitchDispatch, SwitchKey};
use crate::string_literal::StringLiteral;

/// J-level unit plus legacy naming identities needed by the migration exporter.
pub struct Imported {
    /// Editable J-level tree.
    pub arena: Bir,
    /// Synthetic top-level statement list.
    pub root: NodeId,
    pub(super) idents: Vec<Ident>,
    modules: Vec<js::ModuleId>,
    exports: Vec<Ident>,
    export_set: ahash::AHashSet<Ident>,
    reservations: Vec<Ident>,
    side_effect: Option<String>,
    /// Number of source occurrences decoded, including statement lists.
    pub steps: usize,
}

impl Imported {
    /// Plain J tree built by lowering, before export coercion and dependency discovery.
    pub(super) fn from_lowering(arena: Bir, root: NodeId, idents: Vec<Ident>) -> Self {
        Self { arena, root, idents, modules: vec![], exports: vec![],
            export_set: Default::default(), reservations: vec![], side_effect: None, steps: 0 }
    }
}

#[derive(Clone, Copy)]
enum Source<'a> {
    Expr(j::Expr),
    Stmt(j::Stmt),
    Block(&'a [j::Stmt]),
}

// The child schema is exhaustive, including leaf variants. A new legacy kind
// therefore cannot silently vanish from traversal.
fn children<'a>(a: &'a j::JsArena, source: Source<'a>, mut push: impl FnMut(Source<'a>)) {
    use j::{ExprKind as E, StmtKind as S};
    match source {
        Source::Block(ss) => {
            for &s in ss {
                push(Source::Stmt(s));
            }
        }
        Source::Expr(e) => match a.ek(e) {
            E::Length(x, _)
            | E::IsNullOrUndefined(x)
            | E::Typeof(x)
            | E::JsNot(x)
            | E::JsBnot(x)
            | E::StaticIndex(x, _, _)
            | E::OptionalBlock(x, _)
            | E::CamlBlockTag(x, _)
            | E::Await(x)
            | E::Spread(x)
            | E::RecordRest(_, x) => push(Source::Expr(x)),
            E::StringAppend(x, y)
            | E::In(x, y)
            | E::Seq(x, y)
            | E::Bin(_, x, y)
            | E::FlatCall(x, y)
            | E::ArrayIndex(x, y) => {
                push(Source::Expr(x));
                push(Source::Expr(y));
            }
            E::Cond(x, y, z) => {
                push(Source::Expr(x));
                push(Source::Expr(y));
                push(Source::Expr(z));
            }
            E::Call(f, args, _) | E::TaggedTemplate(f, _, args) => {
                push(Source::Expr(f));
                for &e in a.exprs(args) {
                    push(Source::Expr(e));
                }
            }
            E::New(f, args) => {
                push(Source::Expr(f));
                if let Some(args) = args {
                    for &e in a.exprs(args) {
                        push(Source::Expr(e));
                    }
                }
            }
            E::InterpolatedTemplate(_, args) | E::Array(args, _) | E::CamlBlock(args, _, _) => {
                for &e in a.exprs(args) {
                    push(Source::Expr(e));
                }
            }
            E::Object(props) => {
                for &(_, e) in a.props(props) {
                    push(Source::Expr(e));
                }
            }
            E::Fun(f) => push(Source::Block(a.stmts(a.fun(f).body))),
            E::Jsx(id) => {
                for e in a.jsx(id).expressions(a) {
                    push(Source::Expr(e));
                }
            }
            E::Bool(_)
            | E::Var(_)
            | E::Qualified(_)
            | E::Str(_)
            | E::TemplateLiteral(_)
            | E::JsonLiteral(_)
            | E::RawJsCode(_)
            | E::Number(_)
            | E::Undefined { .. }
            | E::Null => {}
        },
        Source::Stmt(s) => match a.sk(s) {
            S::Block(ss) => {
                for &s in a.stmts(ss) {
                    push(Source::Stmt(s));
                }
            }
            S::Variable(v) => {
                if let Some(e) = a.var(v).value {
                    push(Source::Expr(e));
                }
            }
            S::Exp(e) | S::Return(e) | S::Throw(e) => push(Source::Expr(e)),
            S::If(e, t, f) => {
                push(Source::Expr(e));
                push(Source::Block(a.stmts(t)));
                push(Source::Block(a.stmts(f)));
            }
            S::While(_, e, b) => {
                push(Source::Expr(e));
                push(Source::Block(a.stmts(b)));
            }
            S::ForRange(id) => {
                let h = a.for_range(id);
                if let Some(e) = h.init {
                    push(Source::Expr(e));
                }
                push(Source::Expr(h.end));
                push(Source::Block(a.stmts(h.body)));
            }
            S::ForOf(id) | S::ForAwaitOf(id) => {
                let h = a.for_of(id);
                push(Source::Expr(h.iterable));
                push(Source::Block(a.stmts(h.body)));
            }
            S::IntSwitch(e, id) => {
                push(Source::Expr(e));
                let h = a.int_switch(id);
                for (_, c) in &h.clauses {
                    push(Source::Block(a.stmts(c.body)));
                }
                if let Some(b) = h.default {
                    push(Source::Block(a.stmts(b)));
                }
            }
            S::StringSwitch(e, id) => {
                push(Source::Expr(e));
                let h = a.string_switch(id);
                for c in &h.clauses {
                    push(Source::Block(a.stmts(c.clause.body)));
                }
                if let Some(b) = h.default {
                    push(Source::Block(a.stmts(b)));
                }
            }
            S::Try(id) => {
                let h = a.try_info(id);
                push(Source::Block(a.stmts(h.body)));
                if let Some((_, b)) = h.catch {
                    push(Source::Block(a.stmts(b)));
                }
                if let Some(b) = h.finally {
                    push(Source::Block(a.stmts(b)));
                }
            }
            S::Continue(_) | S::Break(_) | S::Debugger => {}
        },
    }
}

#[derive(Default)]
struct Importer {
    b: Bir,
    vars: AHashMap<Ident, VarId>,
    ids: Vec<Ident>,
    modules: AHashMap<js::ModuleId, ImportId>,
    params: AHashMap<j::FunId, VarSpan>,
    existing_loop_depth: usize,
    rest_binders: crate::fast_hash::AHashSet<VarId>,
    identity_error: Option<Unsupported>,
}
impl Importer {
    fn var(&mut self, id: Ident) -> VarId {
        let v = *self.vars.entry(id).or_insert_with(|| {
            let v = self.b.new_var_id(id.name_atom(), id.stamp() as u32);
            self.ids.push(id);
            v
        });
        if id.is_js() || (id.is_global() && id.stamp() == 0) {
            self.b.vars.flags[v.index()].0 |= VarFlags::JS_IDENT;
        }
        // Ident equality deliberately ignores names on stamped locals and all
        // flags. The bridge cannot silently unify different printed identities.
        if self.ids[v.index()].cmp(&id) != std::cmp::Ordering::Equal {
            self.identity_error = Some(Unsupported("inconsistent JS identifier metadata"));
        }
        v
    }
    fn text(&mut self, a: &j::JsArena, id: j::StrId) -> StrId {
        self.b.intern_text(a.text(id))
    }
    fn label(&mut self, a: &j::JsArena, id: Option<j::StrId>) -> Option<StrId> {
        id.map(|id| self.text(a, id))
    }
    fn property(&mut self, a: &j::JsArena, k: j::PropName) -> PropertyKey {
        match k {
            j::PropName::Lit(s) => PropertyKey::Literal(self.text(a, s)),
            j::PropName::Symbol => PropertyKey::Symbol,
            j::PropName::Spread => PropertyKey::Spread,
            j::PropName::RecordSpread => PropertyKey::RecordSpread,
        }
    }
    fn segment(&mut self, s: &StringLiteral) -> TemplatePart {
        match s {
            StringLiteral::Valid { source, semantic } => TemplatePart {
                raw: self.b.intern_text(source),
                cooked: Some(self.b.intern_text(semantic)),
            },
            StringLiteral::InvalidSource(source) => TemplatePart {
                raw: self.b.intern_text(source),
                cooked: None,
            },
        }
    }
    fn module(&mut self, m: &js::ModuleId) -> ImportId {
        if let Some(&id) = self.modules.get(m) {
            if self.b.pools.j_modules[id.index()].id.cmp(&m.id) != std::cmp::Ordering::Equal {
                self.identity_error = Some(Unsupported("inconsistent JS module identity"));
            }
            return id;
        }
        let path = self.b.intern_text(match &m.kind {
            js::Kind::External { name, .. } => name,
            js::Kind::Ml | js::Kind::Runtime => m.id.name(),
        });
        let id = ImportId(index(self.b.pools.imports.len()));
        self.b.pools.imports.push(Import {
            name: m.id.name_atom(),
            path,
        });
        self.b.pools.j_modules.push(m.clone());
        self.modules.insert(m.clone(), id);
        id
    }
    fn cold(&mut self, a: &j::JsArena, c: j::Cold) -> Result<Option<Cold>, Unsupported> {
        Ok(if c.comment.is_some() || c.source_loc.is_some() {
            Some(Cold {
                loc: c.source_loc.unwrap_or(LamLoc::NONE),
                comment: self.label(a, c.comment),
            })
        } else {
            None
        })
    }
    fn clause(&mut self, a: &j::JsArena, c: j::Clause) -> Result<ClauseMeta, Unsupported> {
        Ok(ClauseMeta {
            should_break: c.should_break,
            comment: self.label(a, c.comment),
            loc: c.source_loc,
        })
    }
    fn number(&mut self, n: &Number) -> Result<ConstId, Unsupported> {
        Ok(match n {
            Number::Int { i, c: _ } => self.b.intern_const(Constant::Int(i64::from(*i))),
            Number::Float(f) => self.b.intern_float(&f.f)?,
            Number::BigInt(n) => {
                let text = self.b.intern_text(&format!(
                    "{}{}",
                    if n.positive { '+' } else { '-' },
                    n.value
                ));
                self.b.intern_const(Constant::BigInt(text))
            }
        })
    }
    fn enter(&mut self, a: &j::JsArena, s: Source<'_>) -> Result<(), Unsupported> {
        if let Source::Stmt(stmt) = s {
            if let j::StmtKind::ForRange(id) = a.sk(stmt) {
                if a.for_range(id).init.is_none() {
                    self.existing_loop_depth += 1;
                }
            }
        }
        if let Source::Expr(e) = s {
            if let j::ExprKind::Fun(f) = a.ek(e) {
                let ids = a.ident_slice(a.fun(f).params);
                let first = ids
                    .first()
                    .map(|id| self.var(*id))
                    .map_or(index(self.ids.len()), |v| v.0);
                for (i, &id) in ids.iter().enumerate() {
                    if self.var(id).0 != first + index(i) {
                        return Err(Unsupported("non-contiguous JS parameter run"));
                    }
                }
                self.params.insert(
                    f,
                    VarSpan {
                        start: first,
                        len: index(ids.len()),
                    },
                );
            }
        }
        Ok(())
    }
    fn build(
        &mut self,
        a: &j::JsArena,
        s: Source<'_>,
        c: &[NodeId],
    ) -> Result<NodeId, Unsupported> {
        use j::{ExprKind as E, StmtKind as S};
        let mut aux = 0;
        // Temporary payload lists belong to their final Bir side pools. Child
        // results are borrowed from a single reusable postorder stack.
        let view = match s {
            Source::Block(_) => View::SBlock { statements: c },
            Source::Expr(e) => match a.ek(e) {
                E::Length(_, kind) => {
                    aux = kind as u16;
                    View::JLength { value: c[0] }
                }
                E::IsNullOrUndefined(_) => View::JIsNullish { value: c[0] },
                E::StringAppend(_, _) => View::JStrAppend {
                    left: c[0],
                    right: c[1],
                },
                E::Bool(b) => {
                    aux = u16::from(b);
                    View::JBool
                }
                E::Typeof(_) => View::JTypeof { value: c[0] },
                E::JsNot(_) => View::JNot { value: c[0] },
                E::JsBnot(_) => View::JBnot { value: c[0] },
                E::In(_, _) => View::JIn {
                    left: c[0],
                    right: c[1],
                },
                E::Seq(_, _) => View::JSeq {
                    first: c[0],
                    second: c[1],
                },
                E::Cond(_, _, _) => View::JCond {
                    condition: c[0],
                    then_: c[1],
                    else_: c[2],
                },
                E::Bin(op, _, _) => {
                    aux = op as u16;
                    View::JBin {
                        left: c[0],
                        right: c[1],
                    }
                }
                E::FlatCall(_, _) => View::JFlatCall {
                    callee: c[0],
                    args: c[1],
                },
                E::Call(_, _, id) => {
                    let info = self.b.js_info(JsPayload::Call(a.call_info(id).clone()));
                    View::JCall {
                        callee: c[0],
                        args: &c[1..],
                        info,
                    }
                }
                E::ArrayIndex(_, _) => View::JIndex {
                    object: c[0],
                    index: c[1],
                },
                E::StaticIndex(_, key, position) => View::JDot {
                    object: c[0],
                    property: self.text(a, key),
                    position,
                },
                E::CamlBlockTag(_, key) => {
                    aux = 1;
                    View::JDot {
                        object: c[0],
                        property: self.text(a, key),
                        position: j::FieldPos::NONE,
                    }
                }
                E::New(_, args) => {
                    aux = u16::from(args.is_some());
                    View::JNew {
                        callee: c[0],
                        args: &c[1..],
                    }
                }
                E::Var(id) => {
                    let var = self.var(a.ident(id));
                    if self.existing_loop_depth != 0 {
                        self.b.vars.flags[var.index()].0 |= VarFlags::CAPTURED;
                    }
                    View::Var { var }
                }
                E::Qualified(id) => {
                    let (m, member) = a.qual(id);
                    let module = self.module(m);
                    View::JQualified {
                        module,
                        member: member.map(|s| self.b.intern_text(s)),
                    }
                }
                E::Fun(id) => {
                    let f = a.fun(id);
                    let attr = FunctionAttribute {
                        return_unit: f.return_unit,
                        async_: f.async_,
                        directive: f.directive.map(|s| a.text(s).to_owned()),
                        ..Default::default()
                    };
                    let span = self.params[&id];
                    if span.iter().any(|v| self.b.vars.binder(v).is_some()) {
                        return Err(Unsupported("multiply bound JS parameter"));
                    }
                    let header = if f.is_method {
                        self.b.method_header(span, attr, LamLoc::NONE)
                    } else {
                        self.b.function_header(span, attr, LamLoc::NONE)
                    };
                    View::JFun { body: c[0], header }
                }
                E::Str(s) => View::JStr {
                    text: self.text(a, s),
                },
                E::JsonLiteral(s) => View::JJson {
                    text: self.text(a, s),
                },
                E::TemplateLiteral(id) => {
                    aux = 1;
                    let part = self.segment(a.template(id));
                    let info = self.b.js_info(JsPayload::Template(vec![part]));
                    View::JTemplate { values: c, info }
                }
                E::InterpolatedTemplate(id, _) => {
                    if a.segments(id).len() != c.len() + 1 {
                        return Err(Unsupported("JS template segment count"));
                    }
                    let parts = a.segments(id).iter().map(|s| self.segment(s)).collect();
                    let info = self.b.js_info(JsPayload::Template(parts));
                    View::JTemplate { values: c, info }
                }
                E::TaggedTemplate(_, id, _) => {
                    if a.tagged(id).len() != c.len() {
                        return Err(Unsupported("JS tagged template segment count"));
                    }
                    let parts = a
                        .tagged(id)
                        .iter()
                        .map(|s| TemplatePart {
                            raw: self.b.intern_text(s),
                            cooked: None,
                        })
                        .collect();
                    let info = self.b.js_info(JsPayload::Tagged(parts));
                    View::JTagged {
                        tag: c[0],
                        values: &c[1..],
                        info,
                    }
                }
                E::RawJsCode(id) => {
                    let r = a.raw(id);
                    aux = u16::from(r.is_stmt);
                    View::JRaw {
                        text: self.b.intern_text(&r.code),
                    }
                }
                E::Array(_, m) => {
                    aux = mutable(m);
                    View::JArray { values: c }
                }
                E::OptionalBlock(_, identity) => {
                    aux = u16::from(identity);
                    View::JOptional { value: c[0] }
                }
                E::CamlBlock(_, m, t) => {
                    aux = mutable(m);
                    let info = self.b.js_info(JsPayload::Block(a.tag(t).clone()));
                    View::JBlockLit { values: c, info }
                }
                E::Number(id) => View::JNumber {
                    value: self.number(a.number(id))?,
                },
                E::Object(props) => {
                    let keys = a
                        .props(props)
                        .iter()
                        .map(|&(k, _)| self.property(a, k))
                        .collect();
                    let info = self.b.js_info(JsPayload::Object(keys));
                    View::JObject { values: c, info }
                }
                E::Jsx(id) => {
                    let j::JsxInfo {
                        callee: _,
                        tag: _,
                        spread,
                        props,
                        children,
                        key,
                        multi,
                        fragment,
                    } = a.jsx(id);
                    aux = u16::from(children.is_some());
                    let props = a
                        .props(props)
                        .iter()
                        .map(|&(k, _)| self.property(a, k))
                        .collect();
                    let h = JsxHeader {
                        spread: spread.is_some(),
                        props,
                        children: children.map_or(0, |cs| index(a.exprs(cs).len())),
                        key: key.is_some(),
                        multi,
                        fragment,
                    };
                    let info = self.b.js_info(JsPayload::Jsx(h));
                    View::JJsx { values: c, info }
                }
                E::Undefined { is_unit } => {
                    aux = u16::from(is_unit);
                    View::JUndefined
                }
                E::Null => View::JNull,
                E::Await(_) => View::JAwait { value: c[0] },
                E::Spread(_) => View::JSpread { value: c[0] },
                E::RecordRest(id, _) => {
                    let fields = a
                        .rest(id)
                        .iter()
                        .map(|f| RestField {
                            name: self.b.intern_text(&f.label),
                            binding: f.ident.map(|id| self.var(id)),
                        })
                        .collect();
                    let info = self.b.js_info(JsPayload::Rest(fields));
                    View::JRecordRest { value: c[0], info }
                }
            },
            Source::Stmt(s) => match a.sk(s) {
                S::Block(_) => {
                    aux = 1;
                    View::SBlock { statements: c }
                }
                S::Variable(id) => {
                    let h = a.var(id);
                    aux = (h.property as u16) | ((h.ident_info.used_stats as u16) << 2);
                    let var = self.var(h.ident);
                    if let Some(&value) = c.first() {
                        if let View::JRecordRest { info, .. } = self.b.view(value) {
                            // Retain the descriptor node (and its cold data).
                            // Bit 15 distinguishes this imported descriptor
                            // from an SRest whose value is the source object.
                            aux |= 1 << 15;
                            View::SRest { var, value, info }
                        } else {
                            View::SDecl {
                                var,
                                value: Some(value),
                            }
                        }
                    } else {
                        View::SDecl { var, value: None }
                    }
                }
                S::Exp(_) => View::SExp { value: c[0] },
                S::Return(_) => View::SReturn { value: c[0] },
                S::Throw(_) => View::SThrow { value: c[0] },
                S::If(_, _, _) => View::SIf {
                    condition: c[0],
                    then_: c[1],
                    else_: Some(c[2]),
                },
                S::While(label, _, _) => View::SWhile {
                    condition: c[0],
                    body: c[1],
                    label: self.label(a, label),
                },
                S::ForRange(id) => {
                    let h = a.for_range(id);
                    aux = h.direction as u16;
                    let var = self.var(a.ident(h.ident));
                    let label = self.label(a, h.label);
                    if h.init.is_some() {
                        View::SForRange {
                            var,
                            parts: c,
                            label,
                        }
                    } else {
                        self.existing_loop_depth -= 1;
                        self.b.vars.flags[var.index()].0 |= VarFlags::ASSIGNED | VarFlags::CAPTURED;
                        let variable = self.b.new_node(View::Var { var }, 0);
                        View::SForRangeExisting {
                            variable,
                            parts: c,
                            label,
                        }
                    }
                }
                S::ForOf(id) => {
                    let h = a.for_of(id);
                    View::SForOf {
                        var: self.var(a.ident(h.ident)),
                        parts: c,
                        label: self.label(a, h.label),
                    }
                }
                S::ForAwaitOf(id) => {
                    let h = a.for_of(id);
                    View::SForAwaitOf {
                        var: self.var(a.ident(h.ident)),
                        parts: c,
                        label: self.label(a, h.label),
                    }
                }
                S::Continue(label) => View::SContinue {
                    label: self.label(a, label),
                },
                S::Break(label) => View::SBreak {
                    label: self.label(a, label),
                },
                S::Debugger => View::SDebugger,
                S::Try(id) => {
                    let h = a.try_info(id);
                    if h.catch.is_none() && h.finally.is_none() {
                        return Err(Unsupported("JS try without handler or finaliser"));
                    }
                    View::STry {
                        parts: c,
                        exception: h.catch.map(|(id, _)| self.var(a.ident(id))),
                    }
                }
                S::IntSwitch(_, id) => {
                    let h = a.int_switch(id);
                    let keys = h
                        .clauses
                        .iter()
                        .map(|&(n, _)| CaseKey::Lambda(SwitchKey::Int(n)))
                        .collect();
                    let clauses = h
                        .clauses
                        .iter()
                        .map(|&(_, c)| self.clause(a, c))
                        .collect::<Result<_, _>>()?;
                    let header = self.b.switch_header(SwitchHeader {
                        keys,
                        clauses,
                        constants: index(h.clauses.len()),
                        consts_full: false,
                        blocks_full: false,
                        has_default: h.default.is_some(),
                        dispatch: SwitchDispatch::Direct,
                    });
                    View::SSwitch {
                        scrutinee: c[0],
                        actions: &c[1..],
                        header,
                    }
                }
                S::StringSwitch(_, id) => {
                    aux = 1;
                    let h = a.string_switch(id);
                    let keys = h
                        .clauses
                        .iter()
                        .map(|cl| CaseKey::JavaScript(cl.tag_type.clone()))
                        .collect();
                    let clauses = h
                        .clauses
                        .iter()
                        .map(|cl| self.clause(a, cl.clause))
                        .collect::<Result<_, _>>()?;
                    let header = self.b.switch_header(SwitchHeader {
                        keys,
                        clauses,
                        constants: index(h.clauses.len()),
                        consts_full: false,
                        blocks_full: false,
                        has_default: h.default.is_some(),
                        dispatch: SwitchDispatch::Direct,
                    });
                    View::SSwitch {
                        scrutinee: c[0],
                        actions: &c[1..],
                        header,
                    }
                }
            },
        };
        if let Some(error) = self.identity_error {
            return Err(error);
        }
        let binder = match view {
            View::SDecl { var, .. }
            | View::SRest { var, .. }
            | View::SForRange { var, .. }
            | View::SForOf { var, .. }
            | View::SForAwaitOf { var, .. } => Some(var),
            View::STry { exception, .. } => exception,
            _ => None,
        };
        if binder.is_some_and(|v| self.b.vars.binder(v).is_some()) {
            return Err(Unsupported("multiply bound JS identifier"));
        }
        if let View::SRest { var, info, .. } = view {
            let JsPayload::Rest(fields) = self.b.javascript(info) else {
                unreachable!()
            };
            self.rest_binders.clear();
            self.rest_binders.insert(var);
            for v in fields.iter().filter_map(|f| f.binding) {
                if self.b.vars.binder(v).is_some() || !self.rest_binders.insert(v) {
                    return Err(Unsupported("multiply bound JS record-rest field"));
                }
            }
        }
        let node = super::j::plain::node(&mut self.b, view, aux);
        let cold = match s {
            Source::Expr(e) => a.expr_cold(e),
            Source::Stmt(s) => a.stmt_cold(s),
            Source::Block(_) => j::Cold::default(),
        };
        if let Some(data) = self.cold(a, cold)? {
            self.b.set_cold(node, data);
            if cold.source_loc.is_some() {
                let mut flags = self.b.nodes[node.index()].flags();
                flags.0 |= NodeFlags::JS_LOC_PRESENT;
                self.b.nodes[node.index()].set_flags(flags);
            }
        }
        if let Source::Expr(expr) = s {
            if let E::Number(id) = a.ek(expr) {
                if let Number::Int { c: Some(code), .. } = a.number(id) {
                    self.b.nodes[node.index()].set_js_char(*code);
                }
            }
        }
        Ok(node)
    }
}
fn mutable(m: MutableFlag) -> u16 {
    match m {
        MutableFlag::Immutable => 0,
        MutableFlag::Mutable => 1,
        MutableFlag::NA => 2,
    }
}

/// Import the reachable post-pass program into a fresh tree. Shared leaves are
/// copied per occurrence; shared non-leaves are rejected rather than expanding
/// an arbitrarily large DAG into an exponentially larger tree.
pub fn import_js(p: &j::JsDepsProgram) -> Result<Imported, Unsupported> {
    enum Work<'a> {
        Enter(Source<'a>),
        Finish(Source<'a>, usize),
    }
    let a = &p.program.arena;
    let mut i = Importer::default();
    i.b.begin_bulk();
    let mut work = vec![Work::Enter(Source::Block(&p.program.block))];
    let mut values = Vec::new();
    let (ne, ns) = a.node_counts();
    let mut seen_e = vec![false; ne + 1];
    let mut seen_s = vec![false; ns + 1];
    let mut steps = 0;
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(s) => {
                steps += 1;
                i.enter(a, s)?;
                let start = work.len();
                work.push(Work::Finish(s, 0));
                children(a, s, |child| work.push(Work::Enter(child)));
                let n = work.len() - start - 1;
                if n != 0 {
                    let seen = match s {
                        Source::Expr(e) => Some(&mut seen_e[e.index()]),
                        Source::Stmt(s) => Some(&mut seen_s[s.index()]),
                        Source::Block(_) => None,
                    };
                    if let Some(seen) = seen {
                        if *seen {
                            // A bounded-size shape can be copied per incoming
                            // edge without a DAG expansion. Limit both arity
                            // and depth: never multiply two unbounded lists.
                            let mut shallow = n <= 4;
                            children(a, s, |child| children(a, child, |_| shallow = false));
                            if !shallow {
                                return Err(Unsupported("shared non-leaf JS node"));
                            }
                        }
                        *seen = true;
                    }
                }
                work[start] = Work::Finish(s, n);
                work[start + 1..].reverse();
            }
            Work::Finish(s, n) => {
                let start = values.len() - n;
                let v = i.build(a, s, &values[start..])?;
                values.truncate(start);
                values.push(v);
            }
        }
    }
    let root = values[0];
    for &id in &p.program.exports {
        let v = i.var(id);
        i.b.export(v, id.name_atom());
    }
    for v in 0..i.ids.len() {
        let v = VarId(index(v));
        if i.b.vars.binder(v).is_none() {
            i.b.mark_js_global(v);
        }
    }
    if let Some(error) = i.identity_error {
        return Err(error);
    }
    i.b.try_finish_bulk(root)?;
    Ok(Imported {
        arena: i.b,
        root,
        idents: i.ids,
        modules: p.modules.clone(),
        exports: p.program.exports.clone(),
        export_set: p.program.export_set.clone(),
        reservations: p.program.name_reservations.clone(),
        side_effect: p.side_effect.clone(),
        steps,
    })
}

#[derive(Clone, Copy)]
enum Output {
    Expr(j::Expr),
    Stmt(j::Stmt),
    Block(j::StmtList),
}
impl Output {
    fn expr(self) -> Result<j::Expr, Unsupported> {
        match self {
            Self::Expr(e) => Ok(e),
            Self::Stmt(_) | Self::Block(_) => {
                Err(Unsupported("statement in JS expression position"))
            }
        }
    }
    fn stmt(self) -> Result<j::Stmt, Unsupported> {
        match self {
            Self::Stmt(s) => Ok(s),
            Self::Expr(_) | Self::Block(_) => {
                Err(Unsupported("non-statement in JS statement list"))
            }
        }
    }
    fn block(self) -> Result<j::StmtList, Unsupported> {
        match self {
            Self::Block(b) => Ok(b),
            Self::Expr(_) | Self::Stmt(_) => Err(Unsupported("non-list in JS block position")),
        }
    }
}
// Explicit discriminant inventories: no transmute and no unsafe. The bridge
// doesn't cast an untrusted aux back into an enum.
macro_rules! decode {
    ($name:ident,$ty:ty,[$($variant:path),+])=>{fn $name(n:u16)->Result<$ty,Unsupported>{$(if n==$variant as u16{return Ok($variant);})+Err(Unsupported(concat!("invalid J encoding: ",stringify!($name))))}};
}
decode!(
    bin,
    BinOp,
    [
        BinOp::Eq,
        BinOp::Or,
        BinOp::And,
        BinOp::EqEqEq,
        BinOp::NotEqEq,
        BinOp::Lt,
        BinOp::Le,
        BinOp::Gt,
        BinOp::Ge,
        BinOp::FloatLt,
        BinOp::FloatLe,
        BinOp::FloatGt,
        BinOp::FloatGe,
        BinOp::Bnot,
        BinOp::Bor,
        BinOp::Bxor,
        BinOp::Band,
        BinOp::Lsl,
        BinOp::Lsr,
        BinOp::Asr,
        BinOp::Plus,
        BinOp::Minus,
        BinOp::Mul,
        BinOp::Div,
        BinOp::Mod,
        BinOp::Pow,
        BinOp::InstanceOf,
        BinOp::In
    ]
);
decode!(
    length,
    LengthObject,
    [
        LengthObject::Array,
        LengthObject::String,
        LengthObject::Bytes,
        LengthObject::Function,
        LengthObject::CamlBlock
    ]
);
decode!(
    direction,
    js::ForDirection,
    [
        js::ForDirection::Upto,
        js::ForDirection::Downto,
        js::ForDirection::Up
    ]
);
decode!(
    property,
    js::Property,
    [
        js::Property::Strict,
        js::Property::Alias,
        js::Property::StrictOpt,
        js::Property::Variable
    ]
);
decode!(
    used,
    UsedStats,
    [
        UsedStats::DeadPure,
        UsedStats::DeadNonPure,
        UsedStats::Exported,
        UsedStats::OncePure,
        UsedStats::Used,
        UsedStats::ScanningPure,
        UsedStats::ScanningNonPure,
        UsedStats::NA
    ]
);
fn mutability(n: u16) -> Result<MutableFlag, Unsupported> {
    match n {
        0 => Ok(MutableFlag::Immutable),
        1 => Ok(MutableFlag::Mutable),
        2 => Ok(MutableFlag::NA),
        _ => Err(Unsupported("invalid J mutability")),
    }
}

struct Exporter<'a> {
    p: &'a Imported,
    a: j::JsArena,
    exprs: Vec<j::Expr>,
    stmts: Vec<j::Stmt>,
    props: Vec<(j::PropName, j::Expr)>,
    ids: Vec<Ident>,
}
impl Exporter<'_> {
    fn ident(&self, v: VarId) -> Result<Ident, Unsupported> {
        let v = self.p.arena.vars.j_origin[v.index()];
        self.p
            .idents
            .get(v.index())
            .copied()
            .ok_or(Unsupported("missing JS identifier identity"))
    }
    fn text(&mut self, s: StrId) -> j::StrId {
        self.a.str(self.p.arena.text(s))
    }
    fn label(&mut self, s: Option<StrId>) -> Option<j::StrId> {
        s.map(|s| self.text(s))
    }
    fn exprs(&mut self, c: &[Output]) -> Result<j::ExprList, Unsupported> {
        self.exprs.clear();
        for &v in c {
            self.exprs.push(v.expr()?);
        }
        Ok(self.a.expr_list(&self.exprs))
    }
    fn stmts(&mut self, c: &[Output]) -> Result<j::StmtList, Unsupported> {
        self.stmts.clear();
        for &v in c {
            self.stmts.push(v.stmt()?);
        }
        Ok(self.a.stmt_list(&self.stmts))
    }
    fn key(&mut self, k: PropertyKey) -> j::PropName {
        match k {
            PropertyKey::Literal(s) => j::PropName::Lit(self.text(s)),
            PropertyKey::Symbol => j::PropName::Symbol,
            PropertyKey::Spread => j::PropName::Spread,
            PropertyKey::RecordSpread => j::PropName::RecordSpread,
        }
    }
    fn props(
        &mut self,
        keys: &[PropertyKey],
        values: &[Output],
    ) -> Result<j::PropList, Unsupported> {
        if keys.len() != values.len() {
            return Err(Unsupported("JS property count mismatch"));
        }
        self.props.clear();
        for (&key, &v) in keys.iter().zip(values) {
            let key = self.key(key);
            self.props.push((key, v.expr()?));
        }
        Ok(self.a.prop_list(&self.props))
    }
    fn segment(&self, p: &TemplatePart) -> StringLiteral {
        let b = &self.p.arena;
        match p.cooked {
            Some(s) => StringLiteral::Valid {
                source: b.text(p.raw).to_owned().into(),
                semantic: b.text(s).to_owned().into(),
            },
            None => StringLiteral::InvalidSource(b.text(p.raw).to_owned().into()),
        }
    }
    fn clause(&mut self, c: ClauseMeta, body: j::StmtList) -> j::Clause {
        j::Clause {
            body,
            should_break: c.should_break,
            comment: self.label(c.comment),
            source_loc: c.loc,
        }
    }
    fn number(&self, id: ConstId) -> Result<Number, Unsupported> {
        let b = &self.p.arena;
        Ok(match b.constant(id) {
            Constant::Int(n) => {
                Number::int(i32::try_from(*n).map_err(|_| Unsupported("J integer outside i32"))?)
            }
            Constant::Char(c) => Number::Int {
                i: *c as i32,
                c: Some(*c as i32),
            },
            Constant::Float(f) => Number::float(b.text(f.spelling())),
            Constant::BigInt(s) => {
                let s = b.text(*s);
                let positive = match s.as_bytes().first() {
                    Some(b'+') => true,
                    Some(b'-') => false,
                    _ => return Err(Unsupported("invalid J bigint sign")),
                };
                Number::bigint(positive, &s[1..])
            }
            Constant::Null
            | Constant::Undefined(_)
            | Constant::Bool(_)
            | Constant::NativeInt(_)
            | Constant::Constructor(_)
            | Constant::DecoratedInt { .. }
            | Constant::String(_)
            | Constant::ImmString(_)
            | Constant::Pointer(_)
            | Constant::Block { .. }
            | Constant::Some(_)
            | Constant::ModuleAlias => return Err(Unsupported("non-number J constant")),
        })
    }
    fn build(&mut self, id: NodeId, c: &[Output]) -> Result<Output, Unsupported> {
        use j::{ExprKind as E, StmtKind as S};
        let b = &self.p.arena;
        let aux = b.node(id).aux();
        let cold = if let Some(c) = b.cold(id) {
            j::Cold {
                comment: self.label(c.comment),
                source_loc: b
                    .node(id)
                    .flags()
                    .contains(NodeFlags::JS_LOC_PRESENT)
                    .then_some(c.loc),
            }
        } else {
            j::Cold::default()
        };
        // Separate expression/statement results avoid storing tree-shaped data
        // or inventing legacy nodes to stand in for a statement list.
        let expr = match b.view(id) {
            View::Var { var } => {
                let id = self.a.ident_id(self.ident(var)?);
                E::Var(id)
            }
            View::JLength { .. } => E::Length(c[0].expr()?, length(aux)?),
            View::JIsNullish { .. } => E::IsNullOrUndefined(c[0].expr()?),
            View::JStrAppend { .. } => E::StringAppend(c[0].expr()?, c[1].expr()?),
            View::JBool => E::Bool(aux != 0),
            View::JTypeof { .. } => E::Typeof(c[0].expr()?),
            View::JNot { .. } => E::JsNot(c[0].expr()?),
            View::JBnot { .. } => E::JsBnot(c[0].expr()?),
            View::JIn { .. } => E::In(c[0].expr()?, c[1].expr()?),
            View::JSeq { .. } => E::Seq(c[0].expr()?, c[1].expr()?),
            View::JCond { .. } => E::Cond(c[0].expr()?, c[1].expr()?, c[2].expr()?),
            View::JBin { .. } => E::Bin(bin(aux)?, c[0].expr()?, c[1].expr()?),
            View::JFlatCall { .. } => E::FlatCall(c[0].expr()?, c[1].expr()?),
            View::JIndex { .. } => E::ArrayIndex(c[0].expr()?, c[1].expr()?),
            View::JDot {
                property, position, ..
            } => {
                let key = self.text(property);
                if aux == 1 {
                    E::CamlBlockTag(c[0].expr()?, key)
                } else {
                    E::StaticIndex(c[0].expr()?, key, position)
                }
            }
            View::JCall { info, .. } => {
                let JsPayload::Call(info) = b.javascript(info) else {
                    return Err(Unsupported("missing J call metadata"));
                };
                let args = self.exprs(&c[1..])?;
                let info = self.a.call_id(info.clone());
                E::Call(c[0].expr()?, args, info)
            }
            View::JNew { .. } => E::New(
                c[0].expr()?,
                if aux == 0 {
                    None
                } else {
                    Some(self.exprs(&c[1..])?)
                },
            ),
            View::JQualified { module, member } => {
                let m = b
                    .pools
                    .j_modules
                    .get(module.index())
                    .ok_or(Unsupported("missing J module identity"))?;
                let q = self
                    .a
                    .qual_id(m.clone(), member.map(|s| b.text(s).to_owned()));
                E::Qualified(q)
            }
            View::JFun { header, .. } => {
                let h = b.function(header);
                let attr = b.function_attributes(header);
                self.ids.clear();
                for i in 0..h.params.len() {
                    self.ids.push(self.ident(b.function_parameter(header, i))?);
                }
                let params = self.a.ident_list(&self.ids);
                let directive = attr.directive.as_deref().map(|s| self.a.str(s));
                let f = self.a.fun_id(j::FunInfo {
                    is_method: h.flags & FuncHeader::METHOD != 0,
                    params,
                    body: c[0].block()?,
                    return_unit: attr.return_unit,
                    async_: attr.async_,
                    directive,
                });
                E::Fun(f)
            }
            View::JStr { text } => E::Str(self.text(text)),
            View::JJson { text } => E::JsonLiteral(self.text(text)),
            View::JTemplate { info, .. } => {
                let JsPayload::Template(parts) = b.javascript(info) else {
                    return Err(Unsupported("missing J template metadata"));
                };
                if aux == 1 {
                    if parts.len() != 1 || !c.is_empty() {
                        return Err(Unsupported("invalid J literal template"));
                    }
                    let s = self.segment(&parts[0]);
                    E::TemplateLiteral(self.a.template_id(s))
                } else {
                    let ss = parts.iter().map(|s| self.segment(s)).collect();
                    let ss = self.a.segments_id(ss);
                    E::InterpolatedTemplate(ss, self.exprs(c)?)
                }
            }
            View::JTagged { info, .. } => {
                let JsPayload::Tagged(parts) = b.javascript(info) else {
                    return Err(Unsupported("missing J tagged metadata"));
                };
                let ss = parts.iter().map(|s| b.text(s.raw).to_owned()).collect();
                let ss = self.a.tagged_id(ss);
                E::TaggedTemplate(c[0].expr()?, ss, self.exprs(&c[1..])?)
            }
            View::JRaw { text } => E::RawJsCode(self.a.raw_id(js::JsRawInfo {
                code: b.text(text).to_owned(),
                is_stmt: aux != 0,
            })),
            View::JArray { .. } => E::Array(self.exprs(c)?, mutability(aux)?),
            View::JOptional { .. } => E::OptionalBlock(c[0].expr()?, aux != 0),
            View::JBlockLit { info, .. } => {
                let JsPayload::Block(tag) = b.javascript(info) else {
                    return Err(Unsupported("missing J block metadata"));
                };
                let tag = self.a.tag_id(tag.clone());
                E::CamlBlock(self.exprs(c)?, mutability(aux)?, tag)
            }
            View::JNumber { value } => {
                let mut number = self.number(value)?;
                if let Some(code) = b.node(id).js_char() {
                    let Number::Int { c, .. } = &mut number else {
                        return Err(Unsupported("character decoration on non-integer J number"));
                    };
                    *c = Some(code);
                }
                E::Number(self.a.number_id(number))
            }
            View::JObject { info, .. } => {
                let JsPayload::Object(keys) = b.javascript(info) else {
                    return Err(Unsupported("missing J object metadata"));
                };
                E::Object(self.props(keys, c)?)
            }
            View::JJsx { info, .. } => {
                let JsPayload::Jsx(h) = b.javascript(info) else {
                    return Err(Unsupported("missing J JSX metadata"));
                };
                let mut k = 2;
                let spread = if h.spread {
                    let e = c[k].expr()?;
                    k += 1;
                    Some(e)
                } else {
                    None
                };
                let props = self.props(&h.props, &c[k..k + h.props.len()])?;
                k += h.props.len();
                let children = if aux != 0 {
                    Some(self.exprs(&c[k..k + h.children as usize])?)
                } else {
                    None
                };
                k += h.children as usize;
                let key = if h.key { Some(c[k].expr()?) } else { None };
                let info = self.a.jsx_id(j::JsxInfo {
                    callee: c[0].expr()?,
                    tag: c[1].expr()?,
                    spread,
                    props,
                    children,
                    key,
                    multi: h.multi,
                    fragment: h.fragment,
                });
                E::Jsx(info)
            }
            View::JUndefined => E::Undefined { is_unit: aux != 0 },
            View::JNull => E::Null,
            View::JAwait { .. } => E::Await(c[0].expr()?),
            View::JSpread { .. } => E::Spread(c[0].expr()?),
            View::JRecordRest { info, .. } => {
                let JsPayload::Rest(fields) = b.javascript(info) else {
                    return Err(Unsupported("missing J rest metadata"));
                };
                let fields = fields
                    .iter()
                    .map(|f| {
                        Ok(js::RecordRestField {
                            label: b.text(f.name).to_owned(),
                            ident: f.binding.map(|v| self.ident(v)).transpose()?,
                        })
                    })
                    .collect::<Result<_, Unsupported>>()?;
                let rest = self.a.rest_id(fields);
                E::RecordRest(rest, c[0].expr()?)
            }
            View::SBlock { .. } => {
                let block = self.stmts(c)?;
                return Ok(if aux == 0 {
                    Output::Block(block)
                } else {
                    Output::Stmt(self.a.stmt_with(S::Block(block), cold))
                });
            }
            View::SRest { var, .. } => {
                if aux & (1 << 15) == 0 {
                    return Err(Unsupported("SRest without imported descriptor"));
                }
                let value = c[0].expr()?;
                let info = self.a.var_id(j::VarDecl {
                    ident: self.ident(var)?,
                    value: Some(value),
                    property: property(aux & 3)?,
                    ident_info: js::IdentInfo {
                        used_stats: used((aux & 0x7fff) >> 2)?,
                    },
                });
                return Ok(Output::Stmt(self.a.stmt_with(S::Variable(info), cold)));
            }
            View::SDecl { var, .. } => {
                let info = j::VarDecl {
                    ident: self.ident(var)?,
                    value: c.first().map(|c| c.expr()).transpose()?,
                    property: property(aux & 3)?,
                    ident_info: js::IdentInfo {
                        used_stats: used(aux >> 2)?,
                    },
                };
                let id = self.a.var_id(info);
                return Ok(Output::Stmt(self.a.stmt_with(S::Variable(id), cold)));
            }
            View::SExp { .. } => {
                return Ok(Output::Stmt(self.a.stmt_with(S::Exp(c[0].expr()?), cold)));
            }
            View::SReturn { .. } => {
                return Ok(Output::Stmt(
                    self.a.stmt_with(S::Return(c[0].expr()?), cold),
                ));
            }
            View::SThrow { .. } => {
                return Ok(Output::Stmt(self.a.stmt_with(S::Throw(c[0].expr()?), cold)));
            }
            View::SIf { .. } => {
                return Ok(Output::Stmt(self.a.stmt_with(
                    S::If(
                        c[0].expr()?,
                        c[1].block()?,
                        if c.len() == 3 {
                            c[2].block()?
                        } else {
                            j::StmtList::EMPTY
                        },
                    ),
                    cold,
                )));
            }
            View::SWhile { label, .. } => {
                let label = self.label(label);
                return Ok(Output::Stmt(
                    self.a
                        .stmt_with(S::While(label, c[0].expr()?, c[1].block()?), cold),
                ));
            }
            View::SForRangeExisting { label, .. } => {
                let E::Var(ident) = self.a.ek(c[0].expr()?) else {
                    return Err(Unsupported("non-variable existing range target"));
                };
                let label = self.label(label);
                let info = self.a.for_range_id(j::ForRangeInfo {
                    label,
                    ident,
                    init: None,
                    end: c[1].expr()?,
                    body: c[2].block()?,
                    direction: direction(aux)?,
                });
                return Ok(Output::Stmt(self.a.stmt_with(S::ForRange(info), cold)));
            }
            View::SForRange { var, label, .. } => {
                let ident = self.a.ident_id(self.ident(var)?);
                let label = self.label(label);
                let info = self.a.for_range_id(j::ForRangeInfo {
                    label,
                    ident,
                    init: if c.len() == 3 {
                        Some(c[0].expr()?)
                    } else {
                        None
                    },
                    end: c[c.len() - 2].expr()?,
                    body: c[c.len() - 1].block()?,
                    direction: direction(aux)?,
                });
                return Ok(Output::Stmt(self.a.stmt_with(S::ForRange(info), cold)));
            }
            View::SForOf { var, label, .. } | View::SForAwaitOf { var, label, .. } => {
                let ident = self.a.ident_id(self.ident(var)?);
                let label = self.label(label);
                let info = self.a.for_of_id(j::ForOfInfo {
                    label,
                    ident,
                    iterable: c[0].expr()?,
                    body: c[1].block()?,
                });
                let kind = if b.node(id).op() == Op::SForOf {
                    S::ForOf(info)
                } else {
                    S::ForAwaitOf(info)
                };
                return Ok(Output::Stmt(self.a.stmt_with(kind, cold)));
            }
            View::STry { exception, .. } => {
                let mut k = 1;
                let catch = if let Some(v) = exception {
                    let id = self.a.ident_id(self.ident(v)?);
                    k += 1;
                    Some((id, c[1].block()?))
                } else {
                    None
                };
                let finally = if k < c.len() {
                    Some(c[k].block()?)
                } else {
                    None
                };
                let info = self.a.try_id(j::TryInfo {
                    body: c[0].block()?,
                    catch,
                    finally,
                });
                return Ok(Output::Stmt(self.a.stmt_with(S::Try(info), cold)));
            }
            View::SBreak { label } => {
                let label = self.label(label);
                return Ok(Output::Stmt(self.a.stmt_with(S::Break(label), cold)));
            }
            View::SContinue { label } => {
                let label = self.label(label);
                return Ok(Output::Stmt(self.a.stmt_with(S::Continue(label), cold)));
            }
            View::SDebugger => return Ok(Output::Stmt(self.a.stmt_with(S::Debugger, cold))),
            View::SSwitch { header, .. } => {
                let h = b.switch(header);
                let default = if h.has_default {
                    Some(c[c.len() - 1].block()?)
                } else {
                    None
                };
                let kind = if aux == 0 {
                    let mut clauses = Vec::with_capacity(h.keys.len());
                    for (i, key) in h.keys.iter().enumerate() {
                        let CaseKey::Lambda(SwitchKey::Int(n)) = key else {
                            return Err(Unsupported("non-integer J switch key"));
                        };
                        clauses.push((*n, self.clause(h.clauses[i], c[i + 1].block()?)));
                    }
                    let info = self.a.int_switch_id(j::IntSwitchInfo { clauses, default });
                    S::IntSwitch(c[0].expr()?, info)
                } else {
                    let mut clauses = Vec::with_capacity(h.keys.len());
                    for (i, key) in h.keys.iter().enumerate() {
                        let CaseKey::JavaScript(tag) = key else {
                            return Err(Unsupported("non-JS string switch key"));
                        };
                        clauses.push(j::StringClauseInfo {
                            tag_type: tag.clone(),
                            clause: self.clause(h.clauses[i], c[i + 1].block()?),
                        });
                    }
                    let info = self
                        .a
                        .string_switch_id(j::StringSwitchInfo { clauses, default });
                    S::StringSwitch(c[0].expr()?, info)
                };
                return Ok(Output::Stmt(self.a.stmt_with(kind, cold)));
            }
            View::Const { .. }
            | View::Global { .. }
            | View::Apply { .. }
            | View::Fun { .. }
            | View::Let { .. }
            | View::LetRec { .. }
            | View::Prim { .. }
            | View::Switch { .. }
            | View::StrSwitch { .. }
            | View::Exit { .. }
            | View::Catch { .. }
            | View::Try { .. }
            | View::TryFinally { .. }
            | View::If { .. }
            | View::Seq { .. }
            | View::While { .. }
            | View::For { .. }
            | View::ForOf { .. }
            | View::ForAwaitOf { .. }
            | View::Assign { .. }
            | View::Break
            | View::Continue => return Err(Unsupported("node not produced by J import")),
        };
        Ok(Output::Expr(self.a.expr_with(expr, cold)))
    }
}

/// Export to a fresh JS arena without running any smart constructors.
pub fn export_js(p: &Imported) -> Result<j::JsDepsProgram, Unsupported> {
    enum Work {
        Enter(NodeId),
        Finish(NodeId, usize),
    }
    let mut e = Exporter {
        p,
        a: j::JsArena::new(),
        exprs: Vec::new(),
        stmts: Vec::new(),
        props: Vec::new(),
        ids: Vec::new(),
    };
    let mut work = vec![Work::Enter(p.root)];
    let mut values = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(id) => {
                let children = p.arena.view(id).children();
                work.push(Work::Finish(id, children.len()));
                work.extend(children.into_iter().rev().map(Work::Enter));
            }
            Work::Finish(id, n) => {
                let start = values.len() - n;
                let result = e.build(id, &values[start..])?;
                values.truncate(start);
                values.push(result);
            }
        }
    }
    let block = e.a.stmts(values[0].block()?).to_vec();
    Ok(j::JsDepsProgram {
        program: j::JsProgram {
            arena: e.a,
            block,
            exports: p.exports.clone(),
            export_set: p.export_set.clone(),
            name_reservations: p.reservations.clone(),
        },
        modules: p.modules.clone(),
        side_effect: p.side_effect.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use j::{ExprKind as E, StmtKind as S};
    fn ident(n: i32) -> Ident {
        Ident::new(format!("v{n}"), n, crate::ident::IdentFlags::NONE)
    }
    fn program(a: j::JsArena, block: Vec<j::Stmt>) -> j::JsDepsProgram {
        j::JsDepsProgram {
            program: j::JsProgram::new_in(block, vec![], a),
            modules: vec![],
            side_effect: Some("retained reason".into()),
        }
    }
    fn roundtrip(p: &j::JsDepsProgram) {
        let imported = import_js(p).unwrap();
        imported.arena.validate(Some(imported.root)).unwrap();
        let q = export_js(&imported).unwrap();
        assert_eq!(
            js::dump::block(&p.program.arena, &p.program.block),
            js::dump::block(&q.program.arena, &q.program.block)
        );
        for jsx in [false, true] {
            assert_eq!(
                js::print_deps_program_with_directives_and_options(
                    p,
                    None,
                    &["'directive';".into()],
                    false,
                    jsx,
                    true
                ),
                js::print_deps_program_with_directives_and_options(
                    &q,
                    None,
                    &["'directive';".into()],
                    false,
                    jsx,
                    true
                )
            );
        }
        assert_eq!(p.modules, q.modules);
        assert_eq!(p.program.exports, q.program.exports);
        assert_eq!(p.program.export_set, q.program.export_set);
        assert_eq!(p.program.name_reservations, q.program.name_reservations);
        assert_eq!(p.side_effect, q.side_effect);
        let again = import_js(&q).unwrap();
        assert_eq!(imported.arena.dump(), again.arena.dump());
        assert_eq!(
            imported
                .arena
                .nodes
                .iter()
                .map(|n| n.js_char())
                .collect::<Vec<_>>(),
            again
                .arena
                .nodes
                .iter()
                .map(|n| n.js_char())
                .collect::<Vec<_>>()
        );
        assert_eq!(imported.arena.pools.j_modules, again.arena.pools.j_modules);
    }
    fn expression(mut build: impl FnMut(&mut j::JsArena, j::Expr, j::Expr) -> E) {
        for effects in 0..4 {
            let mut a = j::JsArena::new();
            let mut operand = |impure| {
                if impure {
                    let raw = a.raw_id(js::JsRawInfo { code: "effect()".into(), is_stmt: false });
                    a.expr(E::RawJsCode(raw))
                } else { a.expr(E::Bool(true)) }
            };
            let x = operand(effects & 1 != 0);
            let y = operand(effects & 2 != 0);
            let kind = build(&mut a, x, y);
            let comment = a.str("retained comment");
            let e = a.expr_with(kind, j::Cold {
                comment: Some(comment), source_loc: Some(LamLoc::for_test(17)),
            });
            let expected_pure = js::build::expression_has_no_side_effects(&a, e);
            let expected_strict = crate::lambda::js_exp_make::js_expr_no_side_effects(&a, e);
            let expected_equal = js::build::ocaml_eq_expression(&a, e, e);
            let expected_subexpression = crate::lambda::js_exp_make::is_pure_subexpression(&a, e);
            let s = a.stmt(S::Exp(e));
            let p = program(a, vec![s]);
            let imported = import_js(&p).unwrap();
            let View::SBlock { statements } = imported.arena.view(imported.root) else { panic!() };
            let View::SExp { value } = imported.arena.view(statements[0]) else { panic!() };
            assert_eq!(imported.arena.node(value).flags().contains(NodeFlags::PURE), expected_pure);
            assert_eq!(crate::bir::j::facts::strictly_pure(&imported.arena, value), expected_strict);
            assert_eq!(crate::bir::j::equal::equal(&imported.arena, value, value, &mut 0), expected_equal);
            assert_eq!(imported.arena.node(value).flags().contains(NodeFlags::J_SUBEXPR), expected_subexpression);
            roundtrip(&p);
        }
    }
    macro_rules! expr_case {
        ($name:ident,|$a:ident,$x:ident,$y:ident|$body:expr) => {
            #[test]
            fn $name() {
                expression(|$a, $x, $y| $body);
            }
        };
    }
    expr_case!(length_node, |_a, x, _y| E::Length(x, LengthObject::Bytes));
    expr_case!(nullish_node, |_a, x, _y| E::IsNullOrUndefined(x));
    expr_case!(string_append_node, |_a, x, y| E::StringAppend(x, y));
    expr_case!(bool_node, |_a, _x, _y| E::Bool(false));
    expr_case!(typeof_node, |_a, x, _y| E::Typeof(x));
    expr_case!(not_node, |_a, x, _y| E::JsNot(x));
    expr_case!(bnot_node, |_a, x, _y| E::JsBnot(x));
    expr_case!(in_node, |_a, x, y| E::In(x, y));
    expr_case!(sequence_node, |_a, x, y| E::Seq(x, y));
    expr_case!(conditional_node, |_a, x, y| E::Cond(x, y, x));
    expr_case!(binary_node, |_a, x, y| E::Bin(BinOp::FloatLt, x, y));
    expr_case!(flat_call_node, |_a, x, y| E::FlatCall(x, y));
    expr_case!(index_node, |_a, x, y| E::ArrayIndex(x, y));
    expr_case!(static_index_node, |a, x, _y| E::StaticIndex(
        x,
        a.str("field"),
        j::FieldPos::new(Some(7))
    ));
    expr_case!(tag_node, |a, x, _y| E::CamlBlockTag(x, a.str("TAG")));
    expr_case!(call_node, |a, x, y| {
        let args = a.expr_list(&[y]);
        let info = a.call_id(js::CallInfo {
            is_method: true,
            call_transformed_jsx: false,
            kind: js::CallKind::MlCall,
            arity: js::CallArity::Full,
            comment: Some("call comment".into()),
        });
        E::Call(x, args, info)
    });
    expr_case!(new_node, |a, x, y| E::New(x, Some(a.expr_list(&[y]))));
    expr_case!(new_no_args, |_a, x, _y| E::New(x, None));
    expr_case!(var_node, |a, _x, _y| E::Var(a.ident_id(ident(1))));
    expr_case!(qualified_node, |a, _x, _y| {
        let m = js::ModuleId {
            id: ident(2),
            kind: js::Kind::External {
                name: "dependency".into(),
                default: true,
                import_attributes: Some(js::op::ImportAttributes {
                    entries: vec![("type".into(), "json".into())],
                }),
            },
            dynamic_import: true,
        };
        E::Qualified(a.qual_id(m, Some("member".into())))
    });
    expr_case!(function_node, |a, x, _y| {
        let ret = a.stmt(S::Return(x));
        let body = a.stmt_list(&[ret]);
        let params = a.ident_list(&[ident(3), ident(4)]);
        let directive = Some(a.str("use server"));
        E::Fun(a.fun_id(j::FunInfo {
            is_method: true,
            params,
            body,
            return_unit: true,
            async_: true,
            directive,
        }))
    });
    expr_case!(string_node, |a, _x, _y| E::Str(a.str("\0é\\n")));
    expr_case!(json_node, |a, _x, _y| E::JsonLiteral(a.str("{\"x\":1}")));
    expr_case!(template_node, |a, _x, _y| E::TemplateLiteral(
        a.template_id(StringLiteral::Valid {
            source: "a\\n".into(),
            semantic: "a\n".into()
        })
    ));
    expr_case!(interpolated_node, |a, x, _y| {
        let segs = a.segments_id(vec![
            crate::string_literal::template_from_semantic("a"),
            crate::string_literal::template_from_semantic("b"),
        ]);
        let args = a.expr_list(&[x]);
        E::InterpolatedTemplate(segs, args)
    });
    expr_case!(tagged_node, |a, x, y| {
        let segs = a.tagged_id(vec!["raw\\x".into(), "end".into()]);
        let args = a.expr_list(&[y]);
        E::TaggedTemplate(x, segs, args)
    });
    expr_case!(raw_node, |a, _x, _y| E::RawJsCode(a.raw_id(
        js::JsRawInfo {
            code: "/*raw*/\nfoo()".into(),
            is_stmt: true
        }
    )));
    expr_case!(array_node, |a, x, y| E::Array(
        a.expr_list(&[x, y]),
        MutableFlag::NA
    ));
    expr_case!(optional_node, |_a, x, _y| E::OptionalBlock(x, true));
    expr_case!(block_literal_node, |a, x, y| {
        let xs = a.expr_list(&[x, y]);
        let tag = a.tag_id(crate::lambda::lam_tag_info::TagInfo::Tuple);
        E::CamlBlock(xs, MutableFlag::Mutable, tag)
    });
    expr_case!(number_node, |a, _x, _y| E::Number(
        a.number_id(Number::char('a'))
    ));
    expr_case!(float_node, |a, _x, _y| E::Number(
        a.number_id(Number::float("-0.00"))
    ));
    expr_case!(bigint_node, |a, _x, _y| E::Number(
        a.number_id(Number::bigint(false, "12345678901234567890"))
    ));
    expr_case!(object_node, |a, x, y| {
        let key = a.str("field");
        E::Object(a.prop_list(&[
            (j::PropName::Lit(key), x),
            (j::PropName::Symbol, y),
            (j::PropName::Spread, x),
            (j::PropName::RecordSpread, y),
        ]))
    });
    expr_case!(jsx_node, |a, x, y| {
        let key = a.str("prop");
        let props = a.prop_list(&[(j::PropName::Lit(key), x)]);
        let children = Some(a.expr_list(&[x, y]));
        E::Jsx(a.jsx_id(j::JsxInfo {
            callee: x,
            tag: y,
            spread: Some(x),
            props,
            children,
            key: Some(y),
            multi: true,
            fragment: false,
        }))
    });
    expr_case!(jsx_empty_children, |a, x, y| {
        let props = a.prop_list(&[]);
        E::Jsx(a.jsx_id(j::JsxInfo {
            callee: x,
            tag: y,
            spread: None,
            props,
            children: Some(j::ExprList::EMPTY),
            key: None,
            multi: false,
            fragment: true,
        }))
    });
    expr_case!(undefined_node, |_a, _x, _y| E::Undefined { is_unit: true });
    expr_case!(null_node, |_a, _x, _y| E::Null);
    expr_case!(await_node, |_a, x, _y| E::Await(x));
    expr_case!(spread_node, |_a, x, _y| E::Spread(x));
    expr_case!(rest_node, |a, x, _y| E::RecordRest(
        a.rest_id(vec![
            js::RecordRestField {
                label: "x".into(),
                ident: Some(ident(8))
            },
            js::RecordRestField {
                label: "y".into(),
                ident: None
            }
        ]),
        x
    ));

    fn statement(build: impl FnOnce(&mut j::JsArena, j::Expr, j::StmtList) -> S) {
        let mut a = j::JsArena::new();
        let x = a.expr(E::Bool(true));
        let ret = a.stmt(S::Return(x));
        let block = a.stmt_list(&[ret]);
        let kind = build(&mut a, x, block);
        let comment = a.str("statement comment");
        let s = a.stmt_with(
            kind,
            j::Cold {
                comment: Some(comment),
                source_loc: Some(LamLoc::for_test(19)),
            },
        );
        let p = program(a, vec![s]);
        let imported = import_js(&p).unwrap();
        let expected = js::build::ocaml_eq_block(&p.program.arena, &p.program.block, &p.program.block);
        assert_eq!(crate::bir::j::equal::equal(&imported.arena, imported.root, imported.root, &mut 0), expected);
        roundtrip(&p);
    }
    macro_rules! stmt_case {
        ($name:ident,|$a:ident,$x:ident,$b:ident|$body:expr) => {
            #[test]
            fn $name() {
                statement(|$a, $x, $b| $body);
            }
        };
    }
    stmt_case!(block_statement, |_a, _x, b| S::Block(b));
    stmt_case!(declaration_statement, |a, x, _b| S::Variable(a.var_id(
        j::VarDecl {
            ident: ident(1),
            value: Some(x),
            property: js::Property::Variable,
            ident_info: js::IdentInfo {
                used_stats: UsedStats::DeadNonPure
            }
        }
    )));
    stmt_case!(empty_declaration, |a, _x, _b| S::Variable(a.var_id(
        j::VarDecl {
            ident: ident(1),
            value: None,
            property: js::Property::Alias,
            ident_info: js::IdentInfo::default()
        }
    )));
    stmt_case!(expression_statement, |_a, x, _b| S::Exp(x));
    stmt_case!(if_statement, |_a, x, b| S::If(x, b, j::StmtList::EMPTY));
    stmt_case!(while_statement, |a, x, b| S::While(
        Some(a.str("loop")),
        x,
        b
    ));
    stmt_case!(range_statement, |a, x, b| {
        let ident = a.ident_id(ident(2));
        let label = Some(a.str("range"));
        S::ForRange(a.for_range_id(j::ForRangeInfo {
            label,
            init: Some(x),
            end: x,
            ident,
            direction: js::ForDirection::Downto,
            body: b,
        }))
    });
    stmt_case!(of_statement, |a, x, b| {
        let ident = a.ident_id(ident(2));
        let label = Some(a.str("each"));
        S::ForOf(a.for_of_id(j::ForOfInfo {
            label,
            ident,
            iterable: x,
            body: b,
        }))
    });
    stmt_case!(await_of_statement, |a, x, b| {
        let ident = a.ident_id(ident(2));
        S::ForAwaitOf(a.for_of_id(j::ForOfInfo {
            label: None,
            ident,
            iterable: x,
            body: b,
        }))
    });
    stmt_case!(continue_statement, |a, _x, _b| S::Continue(Some(
        a.str("loop")
    )));
    stmt_case!(break_statement, |a, _x, _b| S::Break(Some(a.str("loop"))));
    stmt_case!(return_statement, |_a, x, _b| S::Return(x));
    stmt_case!(throw_statement, |_a, x, _b| S::Throw(x));
    stmt_case!(debugger_statement, |_a, _x, _b| S::Debugger);
    stmt_case!(try_statement, |a, _x, b| {
        let ident = a.ident_id(ident(2));
        S::Try(a.try_id(j::TryInfo {
            body: b,
            catch: Some((ident, j::StmtList::EMPTY)),
            finally: Some(j::StmtList::EMPTY),
        }))
    });
    stmt_case!(int_switch_statement, |a, x, b| {
        let comment = Some(a.str("case comment"));
        let cl = j::Clause {
            body: b,
            should_break: false,
            comment,
            source_loc: Some(LamLoc::for_test(3)),
        };
        S::IntSwitch(
            x,
            a.int_switch_id(j::IntSwitchInfo {
                clauses: vec![(7, cl)],
                default: Some(j::StmtList::EMPTY),
            }),
        )
    });
    stmt_case!(string_switch_statement, |a, x, b| {
        let cl = j::Clause {
            body: b,
            should_break: true,
            comment: None,
            source_loc: None,
        };
        S::StringSwitch(
            x,
            a.string_switch_id(j::StringSwitchInfo {
                clauses: vec![j::StringClauseInfo {
                    tag_type: crate::lambda::SwitchCaseTag::String("case".into()),
                    clause: cl,
                }],
                default: None,
            }),
        )
    });

    #[test]
    fn long_statement_list_is_linear() {
        let mut a = j::JsArena::new();
        let x = a.expr(E::Bool(true));
        let block = (0..10_000).map(|_| a.stmt(S::Exp(x))).collect();
        let p = program(a, block);
        let i = import_js(&p).unwrap();
        assert_eq!(i.steps, 20_001);
        i.arena.steps.set(0);
        let q = export_js(&i).unwrap();
        assert_eq!(q.program.block.len(), 10_000);
        assert!(i.arena.steps.get() < 150_000);
    }
    #[test]
    fn long_chains_are_iterative_and_linear() {
        for op in 0..3 {
            let mut a = j::JsArena::new();
            let s = a.str("x");
            let x = a.expr(E::Str(s));
            let mut e = x;
            for _ in 0..10_000 {
                e = a.expr(match op {
                    0 => E::StringAppend(e, x),
                    1 => E::Seq(e, x),
                    _ => E::Bin(BinOp::Or, e, x),
                });
            }
            let stmt = a.stmt(S::Exp(e));
            let p = program(a, vec![stmt]);
            let i = import_js(&p).unwrap();
            assert_eq!(i.steps, 20_003);
            i.arena.steps.set(0);
            let q = export_js(&i).unwrap();
            assert_eq!(q.program.arena.node_counts().0, 20_001);
            assert!(i.arena.steps.get() < 150_000);
        }
    }
    #[test]
    fn variable_facts_and_uses() {
        let mut a = j::JsArena::new();
        let id = ident(1);
        let n = a.number_id(Number::int(7));
        let value = a.expr(E::Number(n));
        let var = a.var_id(j::VarDecl {
            ident: id,
            value: Some(value),
            property: js::Property::Strict,
            ident_info: js::IdentInfo::default(),
        });
        let decl = a.stmt(S::Variable(var));
        let iid = a.ident_id(id);
        let x = a.expr(E::Var(iid));
        let use_ = a.stmt(S::Return(x));
        let mut p = program(a, vec![decl, use_]);
        p.program.exports.push(id);
        p.program.export_set.insert(id);
        p.program.name_reservations.push(ident(9));
        roundtrip(&p);
        let i = import_js(&p).unwrap();
        let v = VarId(0);
        assert_eq!(i.arena.vars.uses(v), 1);
        assert!(matches!(i.arena.vars.fact(v), Fact::Const(_)));
        assert!(i.arena.vars.flags(v).contains(VarFlags::EXPORTED));
        assert!(i.arena.vars.binder(v).is_some());
    }
    #[test]
    fn existing_range_uses_and_assigns_the_declared_variable() {
        let mut a = j::JsArena::new();
        let ident = a.ident_id(ident(1));
        let number = a.number_id(Number::int(0));
        let value = a.expr(E::Number(number));
        let decl = a.var_id(j::VarDecl {
            ident: a.ident(ident),
            value: Some(value),
            property: js::Property::Variable,
            ident_info: js::IdentInfo::default(),
        });
        let decl = a.stmt(S::Variable(decl));
        let info = a.for_range_id(j::ForRangeInfo {
            label: None,
            ident,
            init: None,
            end: value,
            body: j::StmtList::EMPTY,
            direction: js::ForDirection::Upto,
        });
        let loop_ = a.stmt(S::ForRange(info));
        let p = program(a, vec![decl, loop_]);
        roundtrip(&p);
        let i = import_js(&p).unwrap();
        let v = VarId(0);
        assert_eq!(i.arena.vars.uses(v), 1);
        assert!(i.arena.vars.flags(v).contains(VarFlags::ASSIGNED));
        assert!(i.arena.vars.flags(v).contains(VarFlags::CAPTURED));
        assert_eq!(
            i.arena.node(i.arena.vars.binder(v).unwrap()).op(),
            Op::SDecl
        );
    }
    #[test]
    fn destructuring_establishes_every_binder_and_retains_expression_cold() {
        let mut a = j::JsArena::new();
        let obj = a.expr(E::Null);
        let fields = a.rest_id(vec![js::RecordRestField {
            label: "field".into(),
            ident: Some(ident(2)),
        }]);
        let comment = a.str("rest descriptor");
        let value = a.expr_with(
            E::RecordRest(fields, obj),
            j::Cold {
                comment: Some(comment),
                source_loc: Some(LamLoc::for_test(4)),
            },
        );
        let decl = a.var_id(j::VarDecl {
            ident: ident(3),
            value: Some(value),
            property: js::Property::Strict,
            ident_info: js::IdentInfo::default(),
        });
        let decl = a.stmt(S::Variable(decl));
        let field = a.ident_id(ident(2));
        let field = a.expr(E::Var(field));
        let ret = a.stmt(S::Return(field));
        let p = program(a, vec![decl, ret]);
        roundtrip(&p);
        let i = import_js(&p).unwrap();
        let field = VarId(0);
        let rest = VarId(1);
        assert_eq!(i.arena.vars.uses(field), 1);
        assert_eq!(i.arena.vars.binder(field), i.arena.vars.binder(rest));
        assert!(!i.arena.vars.flags(field).contains(VarFlags::JS_GLOBAL));
        assert_eq!(i.arena.vars.fact(field), Fact::Unknown);
    }
    #[test]
    fn captures_parameters_aliases_mutability_and_assignments() {
        let mut a = j::JsArena::new();
        let external = a.ident_id(ident(90));
        let external = a.expr(E::Var(external));
        let param = a.ident_id(ident(1));
        let arg = a.expr(E::Var(param));
        let assign = a.expr(E::Bin(BinOp::Eq, arg, external));
        let ret = a.stmt(S::Return(assign));
        let body = a.stmt_list(&[ret]);
        let params = a.ident_list(&[ident(1)]);
        let info = a.fun_id(j::FunInfo {
            params,
            body,
            is_method: false,
            return_unit: false,
            async_: false,
            directive: None,
        });
        let function = a.expr(E::Fun(info));
        let decl = a.var_id(j::VarDecl {
            ident: ident(2),
            value: Some(function),
            property: js::Property::Strict,
            ident_info: js::IdentInfo::default(),
        });
        let decl = a.stmt(S::Variable(decl));
        let p = program(a, vec![decl]);
        roundtrip(&p);
        let i = import_js(&p).unwrap();
        let param = VarId(0);
        let external = VarId(1);
        let fun = VarId(2);
        assert_eq!(i.arena.vars.fact(param), Fact::Param);
        assert_eq!(i.arena.vars.uses(param), 1);
        assert!(
            i.arena
                .vars
                .flags(param)
                .contains(VarFlags::PARAM | VarFlags::ASSIGNED)
        );
        assert!(
            i.arena
                .vars
                .flags(external)
                .contains(VarFlags::CAPTURED | VarFlags::JS_GLOBAL)
        );
        assert!(matches!(
            i.arena.vars.fact(fun),
            Fact::Function {
                rec: RecFlag::No,
                ..
            }
        ));
    }
    #[test]
    fn shared_bounded_reads_expand_but_unbounded_dags_do_not() {
        let mut a = j::JsArena::new();
        let id = a.ident_id(ident(1));
        let value = a.expr(E::Var(id));
        let field = a.str("field");
        let read = a.expr(E::StaticIndex(value, field, j::FieldPos::NONE));
        let values = a.expr_list(&[read, read]);
        let pair = a.expr(E::Array(values, MutableFlag::Immutable));
        let stmt = a.stmt(S::Exp(pair));
        let p = program(a, vec![stmt]);
        roundtrip(&p);
        let i = import_js(&p).unwrap();
        assert_eq!(i.arena.vars.uses(VarId(0)), 2);
        let mut a = j::JsArena::new();
        let mut e = a.expr(E::Bool(true));
        for _ in 0..30 {
            e = a.expr(E::Seq(e, e));
        }
        let stmt = a.stmt(S::Exp(e));
        assert_eq!(
            import_js(&program(a, vec![stmt])).err().unwrap(),
            Unsupported("shared non-leaf JS node")
        );
    }
    expr_case!(different_character_code, |a, _x, _y| E::Number(
        a.number_id(Number::Int { i: 12, c: Some(65) })
    ));
    expr_case!(negative_static_position, |a, x, _y| E::StaticIndex(
        x,
        a.str("field"),
        j::FieldPos::new(Some(-1))
    ));
    #[test]
    fn explicit_empty_location_is_not_absent() {
        let mut a = j::JsArena::new();
        let value = a.expr_with(
            E::Null,
            j::Cold {
                comment: None,
                source_loc: Some(LamLoc::NONE),
            },
        );
        let body = a.stmt(S::Return(value));
        let body = a.stmt_list(&[body]);
        let sw = a.int_switch_id(j::IntSwitchInfo {
            clauses: vec![(
                1,
                j::Clause {
                    body,
                    should_break: true,
                    comment: None,
                    source_loc: Some(LamLoc::NONE),
                },
            )],
            default: None,
        });
        let s = a.stmt_with(
            S::IntSwitch(value, sw),
            j::Cold {
                comment: None,
                source_loc: Some(LamLoc::NONE),
            },
        );
        let p = program(a, vec![s]);
        roundtrip(&p);
        let q = export_js(&import_js(&p).unwrap()).unwrap();
        assert_eq!(
            q.program.arena.stmt_cold(q.program.block[0]).source_loc,
            Some(LamLoc::NONE)
        );
    }
    #[test]
    fn equal_stamps_do_not_hide_distinct_identifier_metadata() {
        let mut a = j::JsArena::new();
        let x = a.ident_id(ident(1));
        let y = a.ident_id(Ident::new("different", 1, crate::ident::IdentFlags::NONE));
        let x = a.expr(E::Var(x));
        let y = a.expr(E::Var(y));
        let pair = a.expr(E::Seq(x, y));
        let s = a.stmt(S::Exp(pair));
        assert_eq!(
            import_js(&program(a, vec![s])).err().unwrap(),
            Unsupported("inconsistent JS identifier metadata")
        );
    }
    #[test]
    fn packed_sizes_unchanged() {
        assert_eq!(std::mem::size_of::<Node>(), 16);
        assert_eq!(std::mem::size_of::<FuncHeader>(), 20);
        assert_eq!(std::mem::size_of::<TemplatePart>(), 12);
        assert_eq!(std::mem::size_of::<js::ModuleId>(), 80);
        assert_eq!(std::mem::size_of::<ClauseMeta>(), 16);
    }
}
