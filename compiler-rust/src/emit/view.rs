//! Read-only input to the shared emitter. Handles belong to the supplying view;
//! no emitter operation constructs or mutates an input node.
use crate::ident::Ident;
use crate::js_ir::op::Number;
use crate::js_ir::{CallInfo, JsRawInfo, ModuleId, RecordRestField, arena::*};
use crate::lambda::{LamLoc, TagInfo};
use std::borrow::Cow;

pub(crate) struct Function<'a> {
    pub is_method: bool,
    pub params: IdentList,
    pub body: StmtList,
    pub return_unit: bool,
    pub async_: bool,
    pub directive: Option<&'a str>,
}

/// A binding occurrence's source identity and dense variable slot.
#[derive(Clone, Copy)]
pub(crate) struct NameKey {
    pub ident: Ident,
    pub slot: usize,
}
#[derive(Clone, Copy)]
pub(crate) enum NameSource {
    Variable(IdentId),
    Declaration(VarId),
    Parameter(IdentList, usize),
    Rest(RestId, usize),
    Qualified(QualId),
    Import(usize, Ident),
    Export(usize, Ident),
}

pub(crate) trait View {
    fn name_key(&self, source: NameSource) -> NameKey;
    fn ek(&self, e: Expr) -> ExprKind;
    fn sk(&self, s: Stmt) -> StmtKind;
    fn stmts(&self, list: StmtList) -> Cow<'_, [Stmt]>;
    fn exprs(&self, list: ExprList) -> Cow<'_, [Expr]>;
    fn props(&self, list: PropList) -> Cow<'_, [(PropName, Expr)]>;
    fn ident_slice(&self, list: IdentList) -> Cow<'_, [Ident]>;
    fn text(&self, id: StrId) -> &str;
    fn ident(&self, id: IdentId) -> Ident;
    fn number(&self, id: NumId) -> Cow<'_, Number>;
    fn call_info(&self, id: CallId) -> &CallInfo;
    fn fun(&self, id: FunId) -> Function<'_>;
    fn tag(&self, id: TagId) -> &TagInfo;
    fn qual(&self, id: QualId) -> (&ModuleId, Option<&str>);
    fn raw(&self, id: RawId) -> Cow<'_, JsRawInfo>;
    fn template(&self, id: TemplateId) -> Cow<'_, crate::string_literal::TemplateSegment>;
    fn segments(&self, id: SegmentsId) -> Cow<'_, [crate::string_literal::TemplateSegment]>;
    fn tagged(&self, id: TaggedId) -> Cow<'_, [String]>;
    fn rest(&self, id: RestId) -> Cow<'_, [RecordRestField]>;
    fn var(&self, id: VarId) -> Cow<'_, VarDecl>;
    fn for_range(&self, id: ForRangeId) -> ForRangeInfo;
    fn for_of(&self, id: ForOfId) -> ForOfInfo;
    fn int_switch(&self, id: IntSwitchId) -> Cow<'_, IntSwitchInfo>;
    fn string_switch(&self, id: StringSwitchId) -> Cow<'_, StringSwitchInfo>;
    fn try_info(&self, id: TryId) -> TryInfo;
    fn jsx(&self, id: JsxId) -> JsxInfo;
    fn expr_comment(&self, e: Expr) -> Option<&str>;
    fn expr_loc(&self, e: Expr) -> Option<LamLoc>;
    fn stmt_comment(&self, s: Stmt) -> Option<&str>;
    fn stmt_loc(&self, s: Stmt) -> Option<LamLoc>;
}

impl View for JsArena {
    fn name_key(&self, source: NameSource) -> NameKey {
        let ident = match source {
            NameSource::Variable(id) => self.ident(id),
            NameSource::Declaration(id) => self.var(id).ident,
            NameSource::Parameter(id, index) => self.ident_slice(id)[index],
            NameSource::Rest(id, index) => self.rest(id)[index].ident.expect("bound rest field"),
            NameSource::Qualified(id) => self.qual(id).0.id,
            NameSource::Import(_, id) | NameSource::Export(_, id) => id,
        };
        NameKey { ident, slot: 0 }
    }
    #[inline]
    fn ek(&self, e: Expr) -> ExprKind {
        JsArena::ek(self, e)
    }
    #[inline]
    fn sk(&self, s: Stmt) -> StmtKind {
        JsArena::sk(self, s)
    }
    #[inline]
    fn stmts(&self, list: StmtList) -> Cow<'_, [Stmt]> {
        Cow::Borrowed(JsArena::stmts(self, list))
    }
    #[inline]
    fn exprs(&self, list: ExprList) -> Cow<'_, [Expr]> {
        Cow::Borrowed(JsArena::exprs(self, list))
    }
    #[inline]
    fn props(&self, list: PropList) -> Cow<'_, [(PropName, Expr)]> {
        Cow::Borrowed(JsArena::props(self, list))
    }
    #[inline]
    fn ident_slice(&self, list: IdentList) -> Cow<'_, [Ident]> {
        Cow::Borrowed(JsArena::ident_slice(self, list))
    }
    #[inline]
    fn text(&self, id: StrId) -> &str {
        JsArena::text(self, id)
    }
    #[inline]
    fn ident(&self, id: IdentId) -> Ident {
        JsArena::ident(self, id)
    }
    #[inline]
    fn number(&self, id: NumId) -> Cow<'_, Number> {
        Cow::Borrowed(JsArena::number(self, id))
    }
    #[inline]
    fn call_info(&self, id: CallId) -> &CallInfo {
        JsArena::call_info(self, id)
    }
    #[inline]
    fn fun(&self, id: FunId) -> Function<'_> {
        let f = JsArena::fun(self, id);
        Function {
            is_method: f.is_method,
            params: f.params,
            body: f.body,
            return_unit: f.return_unit,
            async_: f.async_,
            directive: f.directive.map(|s| self.text(s)),
        }
    }
    #[inline]
    fn tag(&self, id: TagId) -> &TagInfo {
        JsArena::tag(self, id)
    }
    #[inline]
    fn qual(&self, id: QualId) -> (&ModuleId, Option<&str>) {
        JsArena::qual(self, id)
    }
    #[inline]
    fn raw(&self, id: RawId) -> Cow<'_, JsRawInfo> {
        Cow::Borrowed(JsArena::raw(self, id))
    }
    #[inline]
    fn template(&self, id: TemplateId) -> Cow<'_, crate::string_literal::TemplateSegment> {
        Cow::Borrowed(JsArena::template(self, id))
    }
    #[inline]
    fn segments(&self, id: SegmentsId) -> Cow<'_, [crate::string_literal::TemplateSegment]> {
        Cow::Borrowed(JsArena::segments(self, id))
    }
    #[inline]
    fn tagged(&self, id: TaggedId) -> Cow<'_, [String]> {
        Cow::Borrowed(JsArena::tagged(self, id))
    }
    #[inline]
    fn rest(&self, id: RestId) -> Cow<'_, [RecordRestField]> {
        Cow::Borrowed(JsArena::rest(self, id))
    }
    #[inline]
    fn var(&self, id: VarId) -> Cow<'_, VarDecl> {
        Cow::Borrowed(JsArena::var(self, id))
    }
    #[inline]
    fn for_range(&self, id: ForRangeId) -> ForRangeInfo {
        JsArena::for_range(self, id)
    }
    #[inline]
    fn for_of(&self, id: ForOfId) -> ForOfInfo {
        JsArena::for_of(self, id)
    }
    #[inline]
    fn int_switch(&self, id: IntSwitchId) -> Cow<'_, IntSwitchInfo> {
        Cow::Borrowed(JsArena::int_switch(self, id))
    }
    #[inline]
    fn string_switch(&self, id: StringSwitchId) -> Cow<'_, StringSwitchInfo> {
        Cow::Borrowed(JsArena::string_switch(self, id))
    }
    #[inline]
    fn try_info(&self, id: TryId) -> TryInfo {
        JsArena::try_info(self, id)
    }
    #[inline]
    fn jsx(&self, id: JsxId) -> JsxInfo {
        JsArena::jsx(self, id)
    }
    #[inline]
    fn expr_comment(&self, e: Expr) -> Option<&str> {
        JsArena::expr_comment(self, e)
    }
    #[inline]
    fn expr_loc(&self, e: Expr) -> Option<LamLoc> {
        JsArena::expr_loc(self, e)
    }
    #[inline]
    fn stmt_comment(&self, s: Stmt) -> Option<&str> {
        JsArena::stmt_comment(self, s)
    }
    #[inline]
    fn stmt_loc(&self, s: Stmt) -> Option<LamLoc> {
        JsArena::stmt_loc(self, s)
    }
}

/// Assigned names are read independently of input storage.
pub(crate) trait PrintedNames {
    fn name(&self, key: NameKey) -> &str;
    fn method_this_used(&self, f: FunId) -> bool;
    fn finish(&self, s: Stmt) -> &str;
    fn raw_prefix_len(&self) -> usize;
}
