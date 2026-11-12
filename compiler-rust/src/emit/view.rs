//! Read-only input to the shared emitter. Handles belong to the supplying view;
//! no emitter operation constructs or mutates an input node.
use crate::ident::Ident;
use crate::js_ir::op::Number;
use crate::js_ir::{CallInfo, JsRawInfo, ModuleId, RecordRestField, arena::*};
use crate::lambda::{LamLoc, TagInfo};

pub(crate) trait View {
    fn ek(&self, e: Expr) -> ExprKind;
    fn sk(&self, s: Stmt) -> StmtKind;
    fn stmts(&self, list: StmtList) -> &[Stmt];
    fn exprs(&self, list: ExprList) -> &[Expr];
    fn props(&self, list: PropList) -> &[(PropName, Expr)];
    fn ident_slice(&self, list: IdentList) -> &[Ident];
    fn text(&self, id: StrId) -> &str;
    fn ident(&self, id: IdentId) -> Ident;
    fn number(&self, id: NumId) -> &Number;
    fn call_info(&self, id: CallId) -> &CallInfo;
    fn fun(&self, id: FunId) -> FunInfo;
    fn tag(&self, id: TagId) -> &TagInfo;
    fn qual(&self, id: QualId) -> (&ModuleId, Option<&str>);
    fn raw(&self, id: RawId) -> &JsRawInfo;
    fn template(&self, id: TemplateId) -> &crate::string_literal::TemplateSegment;
    fn segments(&self, id: SegmentsId) -> &[crate::string_literal::TemplateSegment];
    fn tagged(&self, id: TaggedId) -> &[String];
    fn rest(&self, id: RestId) -> &[RecordRestField];
    fn var(&self, id: VarId) -> &VarDecl;
    fn for_range(&self, id: ForRangeId) -> ForRangeInfo;
    fn for_of(&self, id: ForOfId) -> ForOfInfo;
    fn int_switch(&self, id: IntSwitchId) -> &IntSwitchInfo;
    fn string_switch(&self, id: StringSwitchId) -> &StringSwitchInfo;
    fn try_info(&self, id: TryId) -> TryInfo;
    fn jsx(&self, id: JsxId) -> JsxInfo;
    fn expr_comment(&self, e: Expr) -> Option<&str>;
    fn expr_loc(&self, e: Expr) -> Option<LamLoc>;
    fn stmt_comment(&self, s: Stmt) -> Option<&str>;
    fn stmt_loc(&self, s: Stmt) -> Option<LamLoc>;
}

impl View for JsArena {
    #[inline]
    fn ek(&self, e: Expr) -> ExprKind {
        JsArena::ek(self, e)
    }
    #[inline]
    fn sk(&self, s: Stmt) -> StmtKind {
        JsArena::sk(self, s)
    }
    #[inline]
    fn stmts(&self, list: StmtList) -> &[Stmt] {
        JsArena::stmts(self, list)
    }
    #[inline]
    fn exprs(&self, list: ExprList) -> &[Expr] {
        JsArena::exprs(self, list)
    }
    #[inline]
    fn props(&self, list: PropList) -> &[(PropName, Expr)] {
        JsArena::props(self, list)
    }
    #[inline]
    fn ident_slice(&self, list: IdentList) -> &[Ident] {
        JsArena::ident_slice(self, list)
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
    fn number(&self, id: NumId) -> &Number {
        JsArena::number(self, id)
    }
    #[inline]
    fn call_info(&self, id: CallId) -> &CallInfo {
        JsArena::call_info(self, id)
    }
    #[inline]
    fn fun(&self, id: FunId) -> FunInfo {
        JsArena::fun(self, id)
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
    fn raw(&self, id: RawId) -> &JsRawInfo {
        JsArena::raw(self, id)
    }
    #[inline]
    fn template(&self, id: TemplateId) -> &crate::string_literal::TemplateSegment {
        JsArena::template(self, id)
    }
    #[inline]
    fn segments(&self, id: SegmentsId) -> &[crate::string_literal::TemplateSegment] {
        JsArena::segments(self, id)
    }
    #[inline]
    fn tagged(&self, id: TaggedId) -> &[String] {
        JsArena::tagged(self, id)
    }
    #[inline]
    fn rest(&self, id: RestId) -> &[RecordRestField] {
        JsArena::rest(self, id)
    }
    #[inline]
    fn var(&self, id: VarId) -> &VarDecl {
        JsArena::var(self, id)
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
    fn int_switch(&self, id: IntSwitchId) -> &IntSwitchInfo {
        JsArena::int_switch(self, id)
    }
    #[inline]
    fn string_switch(&self, id: StringSwitchId) -> &StringSwitchInfo {
        JsArena::string_switch(self, id)
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
