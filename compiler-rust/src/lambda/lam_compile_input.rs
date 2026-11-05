//! Borrowed input facade over Lambda for the shared JS lowering helpers.

use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::{
    ApInfo, ApplyStatus, Constant, DirectionFlag, FunctionAttribute, Lambda, Primitive,
    SwitchDispatch, SwitchKey,
};

#[derive(Clone, Copy)]
pub(crate) enum LambdaInput<'a> {
    Recursive(&'a Lambda),
}

impl<'a> From<&'a Lambda> for LambdaInput<'a> {
    fn from(value: &'a Lambda) -> Self {
        Self::Recursive(value)
    }
}

impl<'a> From<&'a Box<Lambda>> for LambdaInput<'a> {
    fn from(value: &'a Box<Lambda>) -> Self {
        Self::Recursive(value)
    }
}

#[derive(Clone, Copy)]
pub(crate) enum LambdaInputs<'a> {
    Recursive(&'a [Lambda]),
}

impl<'a> LambdaInputs<'a> {
    pub(crate) fn len(self) -> usize {
        match self {
            Self::Recursive(values) => values.len(),
        }
    }

    pub(crate) fn is_empty(self) -> bool {
        self.len() == 0
    }

    pub(crate) fn get(self, index: usize) -> Option<LambdaInput<'a>> {
        match self {
            Self::Recursive(values) => values.get(index).map(LambdaInput::Recursive),
        }
    }

    pub(crate) fn first(self) -> Option<LambdaInput<'a>> {
        self.get(0)
    }

    pub(crate) fn iter(self) -> LambdaInputsIter<'a> {
        LambdaInputsIter {
            values: self,
            index: 0,
        }
    }
}

pub(crate) struct LambdaInputsIter<'a> {
    values: LambdaInputs<'a>,
    index: usize,
}

impl<'a> Iterator for LambdaInputsIter<'a> {
    type Item = LambdaInput<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let value = self.values.get(self.index)?;
        self.index += 1;
        Some(value)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.values.len().saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}
impl ExactSizeIterator for LambdaInputsIter<'_> {}

#[derive(Clone, Copy)]
pub(crate) enum LambdaBindings<'a> {
    Recursive(&'a [(Ident, Lambda)]),
}
impl<'a> LambdaBindings<'a> {
    pub(crate) fn len(self) -> usize {
        match self {
            Self::Recursive(v) => v.len(),
        }
    }
    pub(crate) fn is_empty(self) -> bool {
        self.len() == 0
    }
    pub(crate) fn get(self, index: usize) -> Option<(&'a Ident, LambdaInput<'a>)> {
        match self {
            Self::Recursive(values) => values
                .get(index)
                .map(|(id, value)| (id, LambdaInput::Recursive(value))),
        }
    }
    pub(crate) fn iter(self) -> LambdaBindingsIter<'a> {
        LambdaBindingsIter {
            values: self,
            index: 0,
        }
    }
}
pub(crate) struct LambdaBindingsIter<'a> {
    values: LambdaBindings<'a>,
    index: usize,
}
impl<'a> Iterator for LambdaBindingsIter<'a> {
    type Item = (&'a Ident, LambdaInput<'a>);
    fn next(&mut self) -> Option<Self::Item> {
        let v = self.values.get(self.index)?;
        self.index += 1;
        Some(v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.values.len().saturating_sub(self.index);
        (n, Some(n))
    }
}
impl ExactSizeIterator for LambdaBindingsIter<'_> {}

#[derive(Clone, Copy)]
pub(crate) enum LambdaCases<'a> {
    Recursive { store: &'a [(SwitchKey, Lambda)] },
}
impl<'a> LambdaCases<'a> {
    pub(crate) fn len(self) -> usize {
        match self {
            Self::Recursive { store } => store.len(),
        }
    }
    pub(crate) fn is_empty(self) -> bool {
        self.len() == 0
    }
    pub(crate) fn get(self, index: usize) -> Option<(&'a SwitchKey, LambdaInput<'a>)> {
        match self {
            Self::Recursive { store } => store
                .get(index)
                .map(|(key, value)| (key, LambdaInput::Recursive(value))),
        }
    }
    pub(crate) fn first(self) -> Option<(&'a SwitchKey, LambdaInput<'a>)> {
        self.get(0)
    }
    pub(crate) fn iter(self) -> LambdaCasesIter<'a> {
        LambdaCasesIter {
            values: self,
            index: 0,
        }
    }
}
pub(crate) struct LambdaCasesIter<'a> {
    values: LambdaCases<'a>,
    index: usize,
}
impl<'a> Iterator for LambdaCasesIter<'a> {
    type Item = (&'a SwitchKey, LambdaInput<'a>);
    fn next(&mut self) -> Option<Self::Item> {
        let v = self.values.get(self.index)?;
        self.index += 1;
        Some(v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.values.len().saturating_sub(self.index);
        (n, Some(n))
    }
}
impl ExactSizeIterator for LambdaCasesIter<'_> {}

#[derive(Clone, Copy)]
pub(crate) enum StringCases<'a> {
    Recursive(&'a [(String, Lambda)]),
}
impl<'a> StringCases<'a> {
    pub(crate) fn len(self) -> usize {
        match self {
            Self::Recursive(v) => v.len(),
        }
    }
    pub(crate) fn is_empty(self) -> bool {
        self.len() == 0
    }
    pub(crate) fn get(self, index: usize) -> Option<(&'a String, LambdaInput<'a>)> {
        match self {
            Self::Recursive(values) => values
                .get(index)
                .map(|(key, value)| (key, LambdaInput::Recursive(value))),
        }
    }
    pub(crate) fn first(self) -> Option<(&'a String, LambdaInput<'a>)> {
        self.get(0)
    }
    pub(crate) fn iter(self) -> StringCasesIter<'a> {
        StringCasesIter {
            values: self,
            index: 0,
        }
    }
}
pub(crate) struct StringCasesIter<'a> {
    values: StringCases<'a>,
    index: usize,
}
impl<'a> Iterator for StringCasesIter<'a> {
    type Item = (&'a String, LambdaInput<'a>);
    fn next(&mut self) -> Option<Self::Item> {
        let v = self.values.get(self.index)?;
        self.index += 1;
        Some(v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.values.len().saturating_sub(self.index);
        (n, Some(n))
    }
}
impl ExactSizeIterator for StringCasesIter<'_> {}

#[derive(Clone, Copy)]
pub(crate) struct ApplyInput<'a> {
    pub(crate) function: LambdaInput<'a>,
    pub(crate) args: LambdaInputs<'a>,
    pub(crate) info: &'a ApInfo,
    pub(crate) transformed_jsx: bool,
}
#[derive(Clone, Copy)]
pub(crate) struct FunctionInput<'a> {
    pub(crate) arity: i32,
    pub(crate) params: &'a [Ident],
    pub(crate) body: LambdaInput<'a>,
    pub(crate) attr: &'a FunctionAttribute,
}
#[derive(Clone, Copy)]
pub(crate) struct SwitchInput<'a> {
    pub(crate) consts_full: bool,
    pub(crate) consts: LambdaCases<'a>,
    pub(crate) blocks_full: bool,
    pub(crate) blocks: LambdaCases<'a>,
    pub(crate) fail_action: Option<LambdaInput<'a>>,
    pub(crate) dispatch: &'a SwitchDispatch,
}

pub(crate) enum LambdaInputView<'a> {
    Var(&'a Ident),
    GlobalModule(&'a Ident),
    Const(&'a Constant),
    Apply(ApplyInput<'a>),
    Function(FunctionInput<'a>),
    Let(LetKind, &'a Ident, LambdaInput<'a>, LambdaInput<'a>),
    LetRec(LambdaBindings<'a>, LambdaInput<'a>),
    Prim(&'a Primitive, LambdaInputs<'a>, &'a LamLoc),
    Switch(LambdaInput<'a>, SwitchInput<'a>),
    StringSwitch(LambdaInput<'a>, StringCases<'a>, Option<LambdaInput<'a>>),
    StaticRaise(i32, LambdaInputs<'a>),
    StaticCatch(LambdaInput<'a>, i32, &'a [Ident], LambdaInput<'a>),
    TryWith(LambdaInput<'a>, &'a Ident, LambdaInput<'a>),
    IfThenElse(LambdaInput<'a>, LambdaInput<'a>, LambdaInput<'a>),
    Sequence(LambdaInput<'a>, LambdaInput<'a>),
    Break,
    Continue,
    While(LambdaInput<'a>, LambdaInput<'a>),
    For(
        &'a Ident,
        LambdaInput<'a>,
        LambdaInput<'a>,
        DirectionFlag,
        LambdaInput<'a>,
    ),
    ForOf(&'a Ident, LambdaInput<'a>, LambdaInput<'a>),
    ForAwaitOf(&'a Ident, LambdaInput<'a>, LambdaInput<'a>),
    Assign(&'a Ident, LambdaInput<'a>),
}

impl<'a> LambdaInput<'a> {
    pub(crate) fn view(self) -> LambdaInputView<'a> {
        match self {
            Self::Recursive(lambda) => match lambda {
                Lambda::Lvar(id) => LambdaInputView::Var(id),
                Lambda::LglobalModule(id) => LambdaInputView::GlobalModule(id),
                Lambda::Lconst(c) => LambdaInputView::Const(c),
                Lambda::Lapply(a) => LambdaInputView::Apply(ApplyInput {
                    function: LambdaInput::Recursive(&a.ap_func),
                    args: LambdaInputs::Recursive(&a.ap_args),
                    info: &a.ap_info,
                    transformed_jsx: a.ap_transformed_jsx,
                }),
                Lambda::Lfunction(f) => LambdaInputView::Function(FunctionInput {
                    arity: f.arity,
                    params: &f.params,
                    body: LambdaInput::Recursive(&f.body),
                    attr: &f.attr,
                }),
                Lambda::Llet(k, id, v, b) => LambdaInputView::Let(
                    *k,
                    id,
                    LambdaInput::Recursive(v),
                    LambdaInput::Recursive(b),
                ),
                Lambda::Lletrec(v, b) => {
                    LambdaInputView::LetRec(LambdaBindings::Recursive(v), LambdaInput::Recursive(b))
                }
                Lambda::Lprim(p) => {
                    LambdaInputView::Prim(&p.primitive, LambdaInputs::Recursive(&p.args), &p.loc)
                }
                Lambda::Lswitch(s, w) => LambdaInputView::Switch(
                    LambdaInput::Recursive(s),
                    SwitchInput {
                        consts_full: w.sw_consts_full,
                        consts: LambdaCases::Recursive {
                            store: &w.sw_consts,
                        },
                        blocks_full: w.sw_blocks_full,
                        blocks: LambdaCases::Recursive {
                            store: &w.sw_blocks,
                        },
                        fail_action: w.sw_failaction.as_deref().map(LambdaInput::Recursive),
                        dispatch: &w.sw_dispatch,
                    },
                ),
                Lambda::LstringSwitch(s, c, d) => LambdaInputView::StringSwitch(
                    LambdaInput::Recursive(s),
                    StringCases::Recursive(c),
                    d.as_deref().map(LambdaInput::Recursive),
                ),
                Lambda::LstaticRaise(id, a) => {
                    LambdaInputView::StaticRaise(*id, LambdaInputs::Recursive(a))
                }
                Lambda::LstaticCatch(b, (id, p), h) => LambdaInputView::StaticCatch(
                    LambdaInput::Recursive(b),
                    *id,
                    p,
                    LambdaInput::Recursive(h),
                ),
                Lambda::LtryWith(b, id, h) => LambdaInputView::TryWith(
                    LambdaInput::Recursive(b),
                    id,
                    LambdaInput::Recursive(h),
                ),
                Lambda::LifThenElse(a, b, c) => LambdaInputView::IfThenElse(
                    LambdaInput::Recursive(a),
                    LambdaInput::Recursive(b),
                    LambdaInput::Recursive(c),
                ),
                Lambda::Lsequence(a, b) => {
                    LambdaInputView::Sequence(LambdaInput::Recursive(a), LambdaInput::Recursive(b))
                }
                Lambda::Lbreak => LambdaInputView::Break,
                Lambda::Lcontinue => LambdaInputView::Continue,
                Lambda::Lwhile(a, b) => {
                    LambdaInputView::While(LambdaInput::Recursive(a), LambdaInput::Recursive(b))
                }
                Lambda::Lfor(id, a, b, d, c) => LambdaInputView::For(
                    id,
                    LambdaInput::Recursive(a),
                    LambdaInput::Recursive(b),
                    *d,
                    LambdaInput::Recursive(c),
                ),
                Lambda::Lfor_of(id, a, b) => {
                    LambdaInputView::ForOf(id, LambdaInput::Recursive(a), LambdaInput::Recursive(b))
                }
                Lambda::Lfor_await_of(id, a, b) => LambdaInputView::ForAwaitOf(
                    id,
                    LambdaInput::Recursive(a),
                    LambdaInput::Recursive(b),
                ),
                Lambda::Lassign(id, v) => LambdaInputView::Assign(id, LambdaInput::Recursive(v)),
            },
        }
    }
    pub(crate) fn is_apply_status(self, status: ApplyStatus) -> bool {
        matches!(self.view(),LambdaInputView::Apply(a) if a.info.status==status)
    }

    pub(crate) fn is_top_level_tail(self) -> bool {
        matches!(
            self.view(),
            LambdaInputView::Let(..)
                | LambdaInputView::LetRec(..)
                | LambdaInputView::Sequence(..)
                | LambdaInputView::Prim(
                    Primitive::Pmakeblock(crate::lambda::TagInfo::ModuleExport(_), _),
                    _,
                    _
                )
        )
    }
}
