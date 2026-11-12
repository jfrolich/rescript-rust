//! Borrowed emitter access to J-level nodes. No JS arena is constructed.
//! JS-shaped handles are view-local indices: slot 1 is the empty list and
//! every other handle addresses a Bir node or metadata row at index - 2.
use super::{
    bridge_j::{self, Imported},
    *,
};
use crate::emit::{Unsupported, view::View as EmitView};
use crate::ident::Ident;
use crate::js_ir::{self as js, arena as j, op::Number};
use crate::lambda::{LamLoc, SwitchKey};
use crate::string_literal::{StringLiteral, TemplateSegment};
use std::borrow::Cow;

pub(crate) struct EmitterView<'a> {
    pub(crate) unit: &'a Imported,
}
fn node(i: usize) -> NodeId {
    NodeId(index(i - 2))
}
fn expr(n: NodeId) -> j::Expr {
    j::Expr::new(n.index() + 2)
}
fn stmt(n: NodeId) -> j::Stmt {
    j::Stmt::new(n.index() + 2)
}
fn block(n: NodeId) -> j::StmtList {
    j::StmtList::new(n.index() + 2)
}
fn text(n: StrId) -> j::StrId {
    j::StrId::new(n.index() + 2)
}
fn ident(n: VarId) -> j::IdentId {
    j::IdentId::new(n.index() + 2)
}
impl<'a> EmitterView<'a> {
    pub(crate) fn new(unit: &'a Imported) -> Result<Self, Unsupported> {
        let mut pending = vec![unit.root];
        while let Some(n) = pending.pop() {
            match unit.arena.view(n) {
                View::Const { .. } => return Err(Unsupported("L constant in J emitter")),
                View::Global { .. } => return Err(Unsupported("L global in J emitter")),
                View::Apply { .. }
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
                | View::Continue => return Err(Unsupported("L operation in J emitter")),
                View::Var { .. }
                | View::JBin { .. }
                | View::JNot { .. }
                | View::JBnot { .. }
                | View::JTypeof { .. }
                | View::JIn { .. }
                | View::JCond { .. }
                | View::JSeq { .. }
                | View::JCall { .. }
                | View::JFlatCall { .. }
                | View::JNew { .. }
                | View::JIndex { .. }
                | View::JDot { .. }
                | View::JLength { .. }
                | View::JIsNullish { .. }
                | View::JStrAppend { .. }
                | View::JFun { .. }
                | View::JObject { .. }
                | View::JArray { .. }
                | View::JBlockLit { .. }
                | View::JOptional { .. }
                | View::JJsx { .. }
                | View::JTemplate { .. }
                | View::JTagged { .. }
                | View::JRaw { .. }
                | View::JAwait { .. }
                | View::JSpread { .. }
                | View::JQualified { .. }
                | View::JNumber { .. }
                | View::JStr { .. }
                | View::JBool
                | View::JNull
                | View::JUndefined
                | View::JJson { .. }
                | View::JRecordRest { .. }
                | View::SBlock { .. }
                | View::SDecl { .. }
                | View::SExp { .. }
                | View::SIf { .. }
                | View::SWhile { .. }
                | View::SForRangeExisting { .. }
                | View::SForRange { .. }
                | View::SForOf { .. }
                | View::SForAwaitOf { .. }
                | View::SSwitch { .. }
                | View::SReturn { .. }
                | View::SThrow { .. }
                | View::STry { .. }
                | View::SBreak { .. }
                | View::SContinue { .. }
                | View::SDebugger
                | View::SRest { .. } => {}
            }
            pending.extend(unit.arena.view(n).children());
        }
        Ok(Self { unit })
    }
    fn arena(&self) -> &Bir {
        &self.unit.arena
    }
    fn id(&self, v: VarId) -> Ident {
        self.unit.idents[v.index()]
    }
    fn key(&self, k: PropertyKey) -> j::PropName {
        match k {
            PropertyKey::Literal(s) => j::PropName::Lit(text(s)),
            PropertyKey::Symbol => j::PropName::Symbol,
            PropertyKey::Spread => j::PropName::Spread,
            PropertyKey::RecordSpread => j::PropName::RecordSpread,
        }
    }
    fn segment(&self, p: &TemplatePart) -> TemplateSegment {
        match p.cooked {
            Some(s) => StringLiteral::Valid {
                source: self.arena().text(p.raw).to_owned().into(),
                semantic: self.arena().text(s).to_owned().into(),
            },
            None => StringLiteral::InvalidSource(self.arena().text(p.raw).to_owned().into()),
        }
    }
    fn clause(&self, c: ClauseMeta, n: NodeId) -> j::Clause {
        j::Clause {
            body: block(n),
            should_break: c.should_break,
            comment: c.comment.map(text),
            source_loc: c.loc,
        }
    }
    pub(crate) fn identities(&self) -> &[Ident] {
        &self.unit.idents
    }
    pub(crate) fn root(&self) -> Vec<j::Stmt> {
        self.stmts(block(self.unit.root)).into_owned()
    }
    pub(crate) fn modules(&self) -> &[js::ModuleId] {
        &self.unit.modules
    }
    pub(crate) fn exports(&self) -> &[Ident] {
        &self.unit.exports
    }
    pub(crate) fn reservations(&self) -> &[Ident] {
        &self.unit.reservations
    }
    pub(crate) fn side_effect(&self) -> Option<&str> {
        self.unit.side_effect.as_deref()
    }
}
impl EmitView for EmitterView<'_> {
    fn ek(&self, e: j::Expr) -> j::ExprKind {
        use j::ExprKind as E;
        let n = node(e.index());
        let b = self.arena();
        let aux = b.node(n).aux();
        let list = j::ExprList::new(e.index());
        match b.view(n) {
            View::Var { var } => E::Var(ident(var)),
            View::JLength { value } => E::Length(expr(value), bridge_j::length(aux).unwrap()),
            View::JIsNullish { value } => E::IsNullOrUndefined(expr(value)),
            View::JStrAppend { left, right } => E::StringAppend(expr(left), expr(right)),
            View::JBool => E::Bool(aux != 0),
            View::JTypeof { value } => E::Typeof(expr(value)),
            View::JNot { value } => E::JsNot(expr(value)),
            View::JBnot { value } => E::JsBnot(expr(value)),
            View::JIn { left, right } => E::In(expr(left), expr(right)),
            View::JSeq { first, second } => E::Seq(expr(first), expr(second)),
            View::JCond {
                condition,
                then_,
                else_,
            } => E::Cond(expr(condition), expr(then_), expr(else_)),
            View::JBin { left, right } => {
                E::Bin(bridge_j::bin(aux).unwrap(), expr(left), expr(right))
            }
            View::JFlatCall { callee, args } => E::FlatCall(expr(callee), expr(args)),
            View::JIndex { object, index } => E::ArrayIndex(expr(object), expr(index)),
            View::JDot {
                object,
                property,
                position,
            } => {
                if aux == 1 {
                    E::CamlBlockTag(expr(object), text(property))
                } else {
                    E::StaticIndex(expr(object), text(property), position)
                }
            }
            View::JCall { callee, info, .. } => {
                E::Call(expr(callee), list, j::CallId::new(info.index() + 2))
            }
            View::JNew { callee, .. } => E::New(expr(callee), (aux != 0).then_some(list)),
            View::JQualified { .. } => E::Qualified(j::QualId::new(e.index())),
            View::JFun { .. } => E::Fun(j::FunId::new(e.index())),
            View::JStr { text: s } => E::Str(text(s)),
            View::JJson { text: s } => E::JsonLiteral(text(s)),
            View::JTemplate { info, .. } => {
                if aux == 1 {
                    E::TemplateLiteral(j::TemplateId::new(info.index() + 2))
                } else {
                    E::InterpolatedTemplate(j::SegmentsId::new(info.index() + 2), list)
                }
            }
            View::JTagged { tag, info, .. } => {
                E::TaggedTemplate(expr(tag), j::TaggedId::new(info.index() + 2), list)
            }
            View::JRaw { .. } => E::RawJsCode(j::RawId::new(e.index())),
            View::JArray { .. } => E::Array(list, bridge_j::mutability(aux).unwrap()),
            View::JOptional { value } => E::OptionalBlock(expr(value), aux != 0),
            View::JBlockLit { info, .. } => E::CamlBlock(
                list,
                bridge_j::mutability(aux).unwrap(),
                j::TagId::new(info.index() + 2),
            ),
            View::JNumber { .. } => E::Number(j::NumId::new(e.index())),
            View::JObject { .. } => E::Object(j::PropList::new(e.index())),
            View::JJsx { .. } => E::Jsx(j::JsxId::new(e.index())),
            View::JUndefined => E::Undefined { is_unit: aux != 0 },
            View::JNull => E::Null,
            View::JAwait { value } => E::Await(expr(value)),
            View::JSpread { value } => E::Spread(expr(value)),
            View::JRecordRest { value, info } => {
                E::RecordRest(j::RestId::new(info.index() + 2), expr(value))
            }
            // Only expression handles obtained from this view may reach ek.
            View::Global { .. }
            | View::Const { .. }
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
            | View::Continue
            | View::SBlock { .. }
            | View::SDecl { .. }
            | View::SExp { .. }
            | View::SIf { .. }
            | View::SWhile { .. }
            | View::SForRangeExisting { .. }
            | View::SForRange { .. }
            | View::SForOf { .. }
            | View::SForAwaitOf { .. }
            | View::SSwitch { .. }
            | View::SReturn { .. }
            | View::SThrow { .. }
            | View::STry { .. }
            | View::SBreak { .. }
            | View::SContinue { .. }
            | View::SDebugger
            | View::SRest { .. } => unreachable!("non-expression handle passed to J emitter"),
        }
    }
    fn sk(&self, s: j::Stmt) -> j::StmtKind {
        use j::StmtKind as S;
        let n = node(s.index());
        let b = self.arena();
        match b.view(n) {
            View::SBlock { .. } => S::Block(block(n)),
            View::SDecl { .. } | View::SRest { .. } => S::Variable(j::VarId::new(s.index())),
            View::SExp { value } => S::Exp(expr(value)),
            View::SReturn { value } => S::Return(expr(value)),
            View::SThrow { value } => S::Throw(expr(value)),
            View::SIf {
                condition,
                then_,
                else_,
            } => S::If(
                expr(condition),
                block(then_),
                else_.map(block).unwrap_or(j::StmtList::EMPTY),
            ),
            View::SWhile {
                condition,
                body,
                label,
            } => S::While(label.map(text), expr(condition), block(body)),
            View::SForRange { .. } | View::SForRangeExisting { .. } => {
                S::ForRange(j::ForRangeId::new(s.index()))
            }
            View::SForOf { .. } => S::ForOf(j::ForOfId::new(s.index())),
            View::SForAwaitOf { .. } => S::ForAwaitOf(j::ForOfId::new(s.index())),
            View::STry { .. } => S::Try(j::TryId::new(s.index())),
            View::SBreak { label } => S::Break(label.map(text)),
            View::SContinue { label } => S::Continue(label.map(text)),
            View::SDebugger => S::Debugger,
            View::SSwitch { scrutinee, .. } => {
                if b.node(n).aux() == 0 {
                    S::IntSwitch(expr(scrutinee), j::IntSwitchId::new(s.index()))
                } else {
                    S::StringSwitch(expr(scrutinee), j::StringSwitchId::new(s.index()))
                }
            }
            View::Var { .. }
            | View::Global { .. }
            | View::Const { .. }
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
            | View::Continue
            | View::JBin { .. }
            | View::JNot { .. }
            | View::JBnot { .. }
            | View::JTypeof { .. }
            | View::JIn { .. }
            | View::JCond { .. }
            | View::JSeq { .. }
            | View::JCall { .. }
            | View::JFlatCall { .. }
            | View::JNew { .. }
            | View::JIndex { .. }
            | View::JDot { .. }
            | View::JLength { .. }
            | View::JIsNullish { .. }
            | View::JStrAppend { .. }
            | View::JFun { .. }
            | View::JObject { .. }
            | View::JArray { .. }
            | View::JBlockLit { .. }
            | View::JOptional { .. }
            | View::JJsx { .. }
            | View::JTemplate { .. }
            | View::JTagged { .. }
            | View::JRaw { .. }
            | View::JAwait { .. }
            | View::JSpread { .. }
            | View::JQualified { .. }
            | View::JNumber { .. }
            | View::JStr { .. }
            | View::JBool
            | View::JNull
            | View::JUndefined
            | View::JJson { .. }
            | View::JRecordRest { .. } => unreachable!("non-statement handle passed to J emitter"),
        }
    }
    fn stmts(&self, list: j::StmtList) -> Cow<'_, [j::Stmt]> {
        if list == j::StmtList::EMPTY {
            return Cow::Borrowed(&[]);
        }
        let View::SBlock { statements } = self.arena().view(node(list.index())) else {
            unreachable!("statement list")
        };
        Cow::Owned(statements.iter().copied().map(stmt).collect())
    }
    fn exprs(&self, list: j::ExprList) -> Cow<'_, [j::Expr]> {
        if list == j::ExprList::EMPTY {
            return Cow::Borrowed(&[]);
        }
        let view = self.arena().view(node(list.index()));
        let values = match view {
            View::JCall { args, .. } | View::JNew { args, .. } => args,
            View::JArray { values }
            | View::JBlockLit { values, .. }
            | View::JTemplate { values, .. }
            | View::JTagged { values, .. } => values,
            View::JJsx { values, info } => {
                let JsPayload::Jsx(h) = self.arena().javascript(info) else {
                    unreachable!("JSX metadata")
                };
                let start = 2 + usize::from(h.spread) + h.props.len();
                &values[start..start + h.children as usize]
            }
            View::Var { .. }
            | View::Global { .. }
            | View::Const { .. }
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
            | View::Continue
            | View::JBin { .. }
            | View::JNot { .. }
            | View::JBnot { .. }
            | View::JTypeof { .. }
            | View::JIn { .. }
            | View::JCond { .. }
            | View::JSeq { .. }
            | View::JFlatCall { .. }
            | View::JIndex { .. }
            | View::JDot { .. }
            | View::JLength { .. }
            | View::JIsNullish { .. }
            | View::JStrAppend { .. }
            | View::JFun { .. }
            | View::JObject { .. }
            | View::JOptional { .. }
            | View::JRaw { .. }
            | View::JAwait { .. }
            | View::JSpread { .. }
            | View::JQualified { .. }
            | View::JNumber { .. }
            | View::JStr { .. }
            | View::JBool
            | View::JNull
            | View::JUndefined
            | View::JJson { .. }
            | View::JRecordRest { .. }
            | View::SBlock { .. }
            | View::SDecl { .. }
            | View::SExp { .. }
            | View::SIf { .. }
            | View::SWhile { .. }
            | View::SForRangeExisting { .. }
            | View::SForRange { .. }
            | View::SForOf { .. }
            | View::SForAwaitOf { .. }
            | View::SSwitch { .. }
            | View::SReturn { .. }
            | View::SThrow { .. }
            | View::STry { .. }
            | View::SBreak { .. }
            | View::SContinue { .. }
            | View::SDebugger
            | View::SRest { .. } => unreachable!("expression list"),
        };
        Cow::Owned(values.iter().copied().map(expr).collect())
    }
    fn props(&self, list: j::PropList) -> Cow<'_, [(j::PropName, j::Expr)]> {
        let n = node(list.index());
        let (keys, values) = if let View::JObject { values, info } = self.arena().view(n) {
            let JsPayload::Object(keys) = self.arena().javascript(info) else {
                unreachable!("object metadata")
            };
            (keys.as_slice(), values)
        } else {
            let View::JJsx { values, info } = self.arena().view(n) else {
                unreachable!("properties")
            };
            let JsPayload::Jsx(h) = self.arena().javascript(info) else {
                unreachable!("JSX metadata")
            };
            let start = 2 + usize::from(h.spread);
            (h.props.as_slice(), &values[start..start + h.props.len()])
        };
        Cow::Owned(
            keys.iter()
                .zip(values)
                .map(|(&k, &v)| (self.key(k), expr(v)))
                .collect(),
        )
    }
    fn ident_slice(&self, list: j::IdentList) -> Cow<'_, [Ident]> {
        let h = self.arena().function(FuncId(index(list.index() - 2)));
        Cow::Owned(h.params.iter().map(|v| self.id(v)).collect())
    }
    fn text(&self, id: j::StrId) -> &str {
        self.arena().text(StrId(index(id.index() - 2)))
    }
    fn ident(&self, id: j::IdentId) -> Ident {
        self.id(VarId(index(id.index() - 2)))
    }
    fn number(&self, id: j::NumId) -> Cow<'_, Number> {
        let n = node(id.index());
        let View::JNumber { value } = self.arena().view(n) else {
            unreachable!("number")
        };
        let mut number = match self.arena().constant(value) {
            Constant::Int(i) => Number::int(i32::try_from(*i).expect("J integer")),
            Constant::Char(c) => Number::Int {
                i: *c as i32,
                c: Some(*c as i32),
            },
            Constant::Float(f) => Number::float(self.arena().text(f.spelling())),
            Constant::BigInt(s) => {
                let s = self.arena().text(*s);
                Number::bigint(s.starts_with('+'), &s[1..])
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
            | Constant::ModuleAlias => unreachable!("non-numeric J constant"),
        };
        if let Some(code) = self.arena().node(n).js_char() {
            let Number::Int { c, .. } = &mut number else {
                unreachable!("character decoration")
            };
            *c = Some(code);
        }
        Cow::Owned(number)
    }
    fn call_info(&self, id: j::CallId) -> &js::CallInfo {
        let JsPayload::Call(c) = self.arena().javascript(JsId(index(id.index() - 2))) else {
            unreachable!("call metadata")
        };
        c
    }
    fn fun(&self, id: j::FunId) -> crate::emit::view::Function<'_> {
        let View::JFun { body, header } = self.arena().view(node(id.index())) else {
            unreachable!("function")
        };
        let h = self.arena().function(header);
        let attr = self.arena().function_attributes(header);
        crate::emit::view::Function {
            is_method: h.flags & FuncHeader::METHOD != 0,
            params: j::IdentList::new(header.index() + 2),
            body: block(body),
            return_unit: attr.return_unit,
            async_: attr.async_,
            directive: attr.directive.as_deref(),
        }
    }
    fn tag(&self, id: j::TagId) -> &crate::lambda::TagInfo {
        let JsPayload::Block(tag) = self.arena().javascript(JsId(index(id.index() - 2))) else {
            unreachable!("block metadata")
        };
        tag
    }
    fn qual(&self, id: j::QualId) -> (&js::ModuleId, Option<&str>) {
        let View::JQualified { module, member } = self.arena().view(node(id.index())) else {
            unreachable!("qualified name")
        };
        (
            &self.arena().pools.j_modules[module.index()],
            member.map(|s| self.arena().text(s)),
        )
    }
    fn raw(&self, id: j::RawId) -> Cow<'_, js::JsRawInfo> {
        let n = node(id.index());
        let View::JRaw { text } = self.arena().view(n) else {
            unreachable!("raw JS")
        };
        Cow::Owned(js::JsRawInfo {
            code: self.arena().text(text).to_owned(),
            is_stmt: self.arena().node(n).aux() != 0,
        })
    }
    fn template(&self, id: j::TemplateId) -> Cow<'_, TemplateSegment> {
        let JsPayload::Template(parts) = self.arena().javascript(JsId(index(id.index() - 2)))
        else {
            unreachable!("template metadata")
        };
        Cow::Owned(self.segment(&parts[0]))
    }
    fn segments(&self, id: j::SegmentsId) -> Cow<'_, [TemplateSegment]> {
        let JsPayload::Template(parts) = self.arena().javascript(JsId(index(id.index() - 2)))
        else {
            unreachable!("template metadata")
        };
        Cow::Owned(parts.iter().map(|p| self.segment(p)).collect())
    }
    fn tagged(&self, id: j::TaggedId) -> Cow<'_, [String]> {
        let JsPayload::Tagged(parts) = self.arena().javascript(JsId(index(id.index() - 2))) else {
            unreachable!("tagged metadata")
        };
        Cow::Owned(
            parts
                .iter()
                .map(|p| self.arena().text(p.raw).to_owned())
                .collect(),
        )
    }
    fn rest(&self, id: j::RestId) -> Cow<'_, [js::RecordRestField]> {
        let JsPayload::Rest(fields) = self.arena().javascript(JsId(index(id.index() - 2))) else {
            unreachable!("rest metadata")
        };
        Cow::Owned(
            fields
                .iter()
                .map(|f| js::RecordRestField {
                    label: self.arena().text(f.name).to_owned(),
                    ident: f.binding.map(|v| self.id(v)),
                })
                .collect(),
        )
    }
    fn var(&self, id: j::VarId) -> Cow<'_, j::VarDecl> {
        let n = node(id.index());
        let aux = self.arena().node(n).aux();
        let (var, value) = if let View::SDecl { var, value } = self.arena().view(n) {
            (var, value)
        } else {
            let View::SRest { var, value, .. } = self.arena().view(n) else {
                unreachable!("declaration")
            };
            (var, Some(value))
        };
        Cow::Owned(j::VarDecl {
            ident: self.id(var),
            value: value.map(expr),
            property: bridge_j::property(aux & 3).unwrap(),
            ident_info: js::IdentInfo {
                used_stats: bridge_j::used((aux & 0x7fff) >> 2).unwrap(),
            },
        })
    }
    fn for_range(&self, id: j::ForRangeId) -> j::ForRangeInfo {
        let n = node(id.index());
        let (var, parts, label, existing) =
            if let View::SForRange { var, parts, label } = self.arena().view(n) {
                (var, parts, label, false)
            } else {
                let View::SForRangeExisting {
                    variable,
                    parts,
                    label,
                } = self.arena().view(n)
                else {
                    unreachable!("range")
                };
                let View::Var { var } = self.arena().view(variable) else {
                    unreachable!("range target")
                };
                (var, parts, label, true)
            };
        j::ForRangeInfo {
            ident: ident(var),
            label: label.map(text),
            init: (!existing && parts.len() == 3).then(|| expr(parts[0])),
            end: expr(parts[parts.len() - 2]),
            body: block(parts[parts.len() - 1]),
            direction: bridge_j::direction(self.arena().node(n).aux()).unwrap(),
        }
    }
    fn for_of(&self, id: j::ForOfId) -> j::ForOfInfo {
        let (View::SForOf { var, parts, label } | View::SForAwaitOf { var, parts, label }) =
            self.arena().view(node(id.index()))
        else {
            unreachable!("for-of")
        };
        j::ForOfInfo {
            ident: ident(var),
            label: label.map(text),
            iterable: expr(parts[0]),
            body: block(parts[1]),
        }
    }
    fn int_switch(&self, id: j::IntSwitchId) -> Cow<'_, j::IntSwitchInfo> {
        let View::SSwitch {
            actions, header, ..
        } = self.arena().view(node(id.index()))
        else {
            unreachable!("switch")
        };
        let h = self.arena().switch(header);
        Cow::Owned(j::IntSwitchInfo {
            clauses: h
                .keys
                .iter()
                .enumerate()
                .map(|(i, key)| {
                    let CaseKey::Lambda(SwitchKey::Int(n)) = key else {
                        unreachable!("integer switch key")
                    };
                    (*n, self.clause(h.clauses[i], actions[i]))
                })
                .collect(),
            default: h.has_default.then(|| block(*actions.last().unwrap())),
        })
    }
    fn string_switch(&self, id: j::StringSwitchId) -> Cow<'_, j::StringSwitchInfo> {
        let View::SSwitch {
            actions, header, ..
        } = self.arena().view(node(id.index()))
        else {
            unreachable!("switch")
        };
        let h = self.arena().switch(header);
        Cow::Owned(j::StringSwitchInfo {
            clauses: h
                .keys
                .iter()
                .enumerate()
                .map(|(i, key)| {
                    let CaseKey::JavaScript(tag) = key else {
                        unreachable!("JS switch key")
                    };
                    j::StringClauseInfo {
                        tag_type: tag.clone(),
                        clause: self.clause(h.clauses[i], actions[i]),
                    }
                })
                .collect(),
            default: h.has_default.then(|| block(*actions.last().unwrap())),
        })
    }
    fn try_info(&self, id: j::TryId) -> j::TryInfo {
        let View::STry { parts, exception } = self.arena().view(node(id.index())) else {
            unreachable!("try")
        };
        let k = 1 + usize::from(exception.is_some());
        j::TryInfo {
            body: block(parts[0]),
            catch: exception.map(|v| (ident(v), block(parts[1]))),
            finally: parts.get(k).copied().map(block),
        }
    }
    fn jsx(&self, id: j::JsxId) -> j::JsxInfo {
        let n = node(id.index());
        let View::JJsx { values, info } = self.arena().view(n) else {
            unreachable!("JSX")
        };
        let JsPayload::Jsx(h) = self.arena().javascript(info) else {
            unreachable!("JSX metadata")
        };
        j::JsxInfo {
            callee: expr(values[0]),
            tag: expr(values[1]),
            spread: h.spread.then(|| expr(values[2])),
            props: j::PropList::new(id.index()),
            children: (self.arena().node(n).aux() != 0).then(|| j::ExprList::new(id.index())),
            key: h.key.then(|| expr(*values.last().unwrap())),
            multi: h.multi,
            fragment: h.fragment,
        }
    }
    fn expr_comment(&self, e: j::Expr) -> Option<&str> {
        self.arena()
            .cold(node(e.index()))
            .and_then(|c| c.comment)
            .map(|s| self.arena().text(s))
    }
    fn stmt_comment(&self, s: j::Stmt) -> Option<&str> {
        self.expr_comment(j::Expr::new(s.index()))
    }
    fn expr_loc(&self, e: j::Expr) -> Option<LamLoc> {
        let n = node(e.index());
        self.arena()
            .node(n)
            .flags()
            .contains(NodeFlags::JS_LOC_PRESENT)
            .then(|| self.arena().cold(n).unwrap().loc)
    }
    fn stmt_loc(&self, s: j::Stmt) -> Option<LamLoc> {
        self.expr_loc(j::Expr::new(s.index()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::FunctionAttribute;
    use crate::name::Name;

    /// Aggregate variable facts are not a function's exact free environment.
    /// Swapping capture owners leaves every current variable-table column equal.
    #[test]
    fn capture_flags_do_not_encode_function_environments() {
        fn unit(reverse: bool) -> (Bir, [NodeId; 2]) {
            let mut b = Bir::default();
            b.begin_bulk();
            let x = b.new_var_id(Name::new("x"), 1);
            let y = b.new_var_id(Name::new("x"), 2);
            b.mark_js_global(x);
            b.mark_js_global(y);
            let vars = if reverse { [y, x] } else { [x, y] };
            let mut uses = Vec::new();
            let mut statements = Vec::new();
            for var in vars {
                let value = b.new_node(View::Var { var }, 0);
                uses.push(value);
                let ret = b.new_node(View::SReturn { value }, 0);
                let body = b.new_node(View::SBlock { statements: &[ret] }, 0);
                let header = b.function_header(VarSpan::default(), FunctionAttribute::default(), LamLoc::NONE);
                let function = b.new_node(View::JFun { body, header }, 0);
                statements.push(b.new_node(View::SExp { value: function }, 0));
            }
            let root = b.new_node(View::SBlock { statements: &statements }, 0);
            b.finish_bulk(root);
            (b, [uses[0], uses[1]])
        }
        let (a, a_uses) = unit(false);
        let (b, b_uses) = unit(true);
        for i in 0..a.vars().len() {
            let v = VarId(index(i));
            assert_eq!(a.vars().name(v), b.vars().name(v));
            assert_eq!(a.vars().order(v), b.vars().order(v));
            assert_eq!(a.vars().uses(v), b.vars().uses(v));
            assert_eq!(a.vars().flags(v), b.vars().flags(v));
            assert_eq!(a.vars().binder(v), b.vars().binder(v));
            assert_eq!(a.vars().fact(v), b.vars().fact(v));
            assert_eq!(a.vars().printed(v), b.vars().printed(v));
        }
        let View::Var { var: first_a } = a.view(a_uses[0]) else { unreachable!() };
        let View::Var { var: first_b } = b.view(b_uses[0]) else { unreachable!() };
        assert_ne!(first_a, first_b);
    }
}
