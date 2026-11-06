//! JSX preserve mode in translcore (`jsx_call`, `transl_jsx_element`,
//! compiler/ml/translcore.ml): a call of a JSX external as the JSX PPX
//! produces it becomes a `Pjsx` element. The JSX module's names (`jsx`,
//! `jsxs`, `jsxKeyed`, `jsxsKeyed`, `jsxFragment`) are fixed by the PPX, unlike
//! the JS names of the externals.

use std::borrow::Cow;

use super::{RawLambdaConverter, label_runtime_name, raw_optional_none};
use crate::lambda::lam_primitive::JsxElement;
use crate::lambda::{FieldDbgInfo, LamLoc, Primitive};
use crate::raw_lambda::{LetKind, RawLambda};
use crate::types::asttypes::ArgLabel;
use crate::types::decl::{LabelDescription, PrimKind, RecordRepresentation, ValueKind};
use crate::types::external_ffi_types::{
    Attr, DeclKind, ExternalDecl, ExternalFfi, LabelNoname, ModuleSource, Param, ReturnWrapper,
};
use crate::types::path::Path;
use crate::types::typedtree::{
    ApplyArg, Expression, ExpressionDesc, RecordField, RecordLabelDefinition,
};

/// `jsx_props`: the props as the PPX passes them.
pub(super) enum JsxProps<'e> {
    /// The PPX passes the spread itself when there are no other props.
    Spread(&'e Expression),
    Record {
        /// In `lbl_all` order.
        fields: Cow<'e, [RecordField]>,
        init: Option<&'e Expression>,
        /// `transl_record`'s choice: copy the fields of `init` one by one,
        /// or take a shallow copy of it.
        copy_fields: bool,
        children: Option<Vec<&'e Expression>>,
    },
}

/// `jsx_call`.
pub(super) struct JsxCall<'e> {
    name: String,
    ffi: ExternalDecl,
    multi: bool,
    fragment: bool,
    tag: &'e Expression,
    props: JsxProps<'e>,
    key: Option<&'e Expression>,
}

/// `jsx_is_fragment`: a fragment's tag is the `jsxFragment` of the JSX module
/// whose `jsx` or `jsxs` the PPX calls; a component of another module may
/// have that name.
fn jsx_is_fragment(funct: &Expression, tag: &Expression) -> bool {
    match (&funct.exp_desc, &tag.exp_desc) {
        (
            ExpressionDesc::Texp_ident(Path::Pdot(jsx_module, _, _), _, _),
            ExpressionDesc::Texp_ident(Path::Pdot(tag_module, name, _), _, _),
        ) => name.as_str() == "jsxFragment" && jsx_module.same(tag_module),
        _ => false,
    }
}

fn is_construct(e: &Expression, name: &str) -> bool {
    matches!(
        &e.exp_desc,
        ExpressionDesc::Texp_construct(_, cstr, args) if cstr.cstr_name == name && args.is_empty()
    )
}

/// `jsx_children`: the PPX's children: a single child, or for `jsxs` an
/// array literal wrapped in the JSX module's `array` identity. An optional
/// `children` field wraps that in `Some`, which is the identity on an array
/// literal.
fn jsx_children<'e>(
    multi: bool,
    lbl: &LabelDescription,
    child: &'e Expression,
) -> Option<Vec<&'e Expression>> {
    if !multi {
        return Some(vec![child]);
    }
    let child = match &child.exp_desc {
        ExpressionDesc::Texp_construct(_, cstr, args)
            if cstr.cstr_name == "Some" && args.len() == 1 && lbl.lbl_optional =>
        {
            &args[0]
        }
        _ => child,
    };
    match &child.exp_desc {
        ExpressionDesc::Texp_apply { funct, args, .. } => {
            match (&funct.exp_desc, args.as_slice()) {
                (
                    ExpressionDesc::Texp_ident(_, _, desc),
                    [
                        ApplyArg {
                            label: ArgLabel::Nolabel,
                            expression: Some(array),
                        },
                    ],
                ) if matches!(&desc.val_kind, ValueKind::ValPrim(p) if p.prim_name == "%identity") => {
                    match &array.exp_desc {
                        ExpressionDesc::Texp_array(children) => Some(children.iter().collect()),
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// `Lambda.record_fields_are_array`: the runtime names are "0", "1", ...
fn record_fields_are_array(fields: &[RecordField]) -> bool {
    !fields.is_empty()
        && fields
            .iter()
            .enumerate()
            .all(|(i, (_, lbl, _, _))| lbl.lbl_runtime_name == i.to_string())
}

fn is_omitted(lbl: &LabelDescription, definition: &RecordLabelDefinition) -> bool {
    lbl.lbl_optional
        && match definition {
            RecordLabelDefinition::OmittedOptionalNone(..) => true,
            RecordLabelDefinition::Overridden(_, e) => is_construct(e, "None"),
            RecordLabelDefinition::Kept(_) => false,
        }
}

fn is_plain_param(param: &Param) -> bool {
    param.arg_label == LabelNoname::ArgEmpty && param.arg_type == Attr::Nothing
}

impl<'a> RawLambdaConverter<'a> {
    /// `jsx_props_of`.
    fn jsx_props_of<'e>(&self, multi: bool, props: &'e Expression) -> Option<JsxProps<'e>> {
        // `explicit` holds the fields with a definition in the source: all
        // of them, or the explicit ones of a sparse record, whose omitted
        // optional fields are statically `None`.
        let (fields, explicit, init): (Cow<'e, [RecordField]>, &'e [RecordField], _) =
            match &props.exp_desc {
                ExpressionDesc::Texp_record {
                    fields,
                    empty_representation,
                    extended_expression,
                } if fields
                    .first()
                    .map(|(_, lbl, _, _)| &lbl.lbl_repres)
                    .or(empty_representation.as_deref())
                    .is_none_or(|repres| *repres == RecordRepresentation::RecordRegular) =>
                {
                    (
                        Cow::Borrowed(fields.as_slice()),
                        fields.as_slice(),
                        extended_expression.as_deref(),
                    )
                }
                ExpressionDesc::Texp_record_sparse {
                    fields,
                    all_labels,
                    omitted_loc,
                    extended_expression,
                } => (
                    Cow::Owned(self.expand_sparse_record_fields(all_labels, fields, *omitted_loc)),
                    fields.as_slice(),
                    extended_expression.as_deref(),
                ),
                _ => return Some(JsxProps::Spread(props)),
            };
        let children = explicit
            .iter()
            .find_map(|(_, lbl, definition, _)| match definition {
                RecordLabelDefinition::Overridden(_, child)
                    if lbl.lbl_name == "children" && !is_omitted(lbl, definition) =>
                {
                    Some((lbl, child))
                }
                _ => None,
            });
        let copy_fields = match init {
            None => true,
            Some(_) => fields.len() < 20 && !fields.iter().any(|(_, lbl, _, _)| lbl.lbl_optional),
        };
        let children = match children {
            // A record with the runtime names "0", "1", ... is an array.
            _ if record_fields_are_array(&fields) => return None,
            None => None,
            // Children printed as JSX children must be the `children` prop.
            Some((lbl, _)) if lbl.lbl_runtime_name != "children" => return None,
            Some((lbl, child)) => Some(jsx_children(multi, lbl, child)?),
        };
        Some(JsxProps::Record {
            fields,
            init,
            copy_fields,
            children,
        })
    }

    /// `jsx_call`: `None` when the call doesn't have the shape the PPX
    /// produces; it then compiles as an ordinary external call.
    pub(super) fn jsx_call<'e>(
        &self,
        e: &Expression,
        funct: &'e Expression,
        args: &'e [ApplyArg],
    ) -> Option<JsxCall<'e>> {
        let ExpressionDesc::Texp_ident(path, _, desc) = &funct.exp_desc else {
            return None;
        };
        let ValueKind::ValPrim(p) = &desc.val_kind else {
            return None;
        };
        let multi = match path.last() {
            "jsx" | "jsxKeyed" => false,
            "jsxs" | "jsxsKeyed" => true,
            _ => return None,
        };
        let PrimKind::KindExternal(spec) = &p.prim_kind else {
            return None;
        };
        let ExternalFfi::FfiBs(arg_types, result, ffi) = spec.as_ref() else {
            return None;
        };
        if !matches!(ffi.kind, DeclKind::DeclVal { .. })
            || !matches!(ffi.module_, None | Some(ModuleSource::ModuleNamed(_)))
            || ffi.variadic
            || !matches!(
                result,
                ReturnWrapper::ReturnUnset | ReturnWrapper::ReturnIdentity
            )
        {
            return None;
        }
        // A call returning unit is sequenced with the unit value, see
        // `external_result_wrap`.
        if *result == ReturnWrapper::ReturnUnset {
            let env = self.env_for_expr(e)?;
            if self.external_returns_unit(&env, p, desc.val_type) {
                return None;
            }
        }
        let (tag, props, key) = match (arg_types.as_slice(), args) {
            (
                [tag_t, props_t],
                [
                    ApplyArg {
                        label: ArgLabel::Nolabel,
                        expression: Some(tag),
                    },
                    ApplyArg {
                        label: ArgLabel::Nolabel,
                        expression: Some(props),
                    },
                ],
            ) if is_plain_param(tag_t) && is_plain_param(props_t) => (tag, props, None),
            (
                [tag_t, props_t, key_t, unit_t],
                [
                    ApplyArg {
                        label: ArgLabel::Nolabel,
                        expression: Some(tag),
                    },
                    ApplyArg {
                        label: ArgLabel::Nolabel,
                        expression: Some(props),
                    },
                    ApplyArg {
                        label: ArgLabel::Labelled(key_label) | ArgLabel::Optional(key_label),
                        expression: Some(key),
                    },
                    ApplyArg {
                        label: ArgLabel::Nolabel,
                        expression: Some(unit),
                    },
                ],
            ) if is_plain_param(tag_t)
                && is_plain_param(props_t)
                && key_t.arg_label == LabelNoname::ArgOptional
                && key_t.arg_type == Attr::Nothing
                && key_label.txt == "key"
                && unit_t.arg_label == LabelNoname::ArgEmpty
                && matches!(unit_t.arg_type, Attr::Ignore | Attr::ExternUnit)
                && is_construct(unit, "()") =>
            {
                (tag, props, Some(key))
            }
            _ => return None,
        };
        let props = self.jsx_props_of(multi, props)?;
        Some(JsxCall {
            name: p.prim_name.clone(),
            ffi: ffi.clone(),
            multi,
            fragment: jsx_is_fragment(funct, tag),
            tag,
            props,
            key,
        })
    }

    /// `transl_jsx_element`: the arguments of `Pjsx` are in the order the
    /// call evaluates them, except that the children come after the other
    /// props, as in JSX.
    pub(super) fn transl_jsx_element(&mut self, loc: LamLoc, call: JsxCall<'_>) -> RawLambda {
        let init_id = self.fresh_ident("init");
        let (init, spread, fields, children) = match call.props {
            JsxProps::Spread(props) => (None, Some(self.convert_expr_raw(props)), Vec::new(), None),
            JsxProps::Record {
                fields,
                init,
                copy_fields,
                children,
            } => {
                // An optional prop that is statically `undefined` can be left
                // out, unless it overrides a prop of the spread.
                let has_spread = init.is_some() && !copy_fields;
                let mut props = Vec::with_capacity(fields.len());
                for (i, (_, lbl, definition, _)) in fields.iter().enumerate() {
                    let value = match definition {
                        RecordLabelDefinition::Overridden(..)
                            if lbl.lbl_name == "children" && children.is_some() =>
                        {
                            continue;
                        }
                        RecordLabelDefinition::Overridden(_, value) => self.convert_expr_raw(value),
                        RecordLabelDefinition::OmittedOptionalNone(..) => raw_optional_none(),
                        RecordLabelDefinition::Kept(_) if copy_fields => RawLambda::prim(
                            Primitive::Pfield(
                                i as i32,
                                FieldDbgInfo::Record {
                                    name: label_runtime_name(lbl),
                                },
                            ),
                            vec![RawLambda::var(init_id)],
                            loc,
                        ),
                        RecordLabelDefinition::Kept(_) => continue,
                    };
                    props.push((
                        label_runtime_name(lbl),
                        lbl.lbl_optional && !has_spread,
                        value,
                    ));
                }
                let children = children.map(|children| {
                    children
                        .into_iter()
                        .map(|child| self.convert_expr_raw(child))
                        .collect::<Vec<_>>()
                });
                let (init, spread) = match init {
                    None => (None, None),
                    Some(init) if copy_fields => (Some(self.convert_expr_raw(init)), None),
                    Some(init) => (None, Some(self.convert_expr_raw(init))),
                };
                (init, spread, props, children)
            }
        };
        // OCaml evaluates the arguments of `@` right to left: the key before
        // the tag.
        let key = call.key.map(|key| self.convert_expr_raw(key));
        let tag = self.convert_expr_raw(call.tag);
        let element = JsxElement {
            jsx_name: call.name,
            jsx_ffi: call.ffi,
            jsx_multi: call.multi,
            jsx_fragment: call.fragment,
            jsx_spread: spread.is_some(),
            jsx_props: fields
                .iter()
                .map(|(name, optional, _)| (name.clone(), *optional))
                .collect(),
            jsx_children: children.as_ref().map(Vec::len),
            jsx_key: key.is_some(),
        };
        let mut args = Vec::with_capacity(2 + fields.len() + children.as_ref().map_or(0, Vec::len));
        args.push(tag);
        args.extend(spread);
        args.extend(fields.into_iter().map(|(_, _, value)| value));
        args.extend(children.into_iter().flatten());
        args.extend(key);
        let lam = RawLambda::prim(Primitive::Pjsx(Box::new(element)), args, loc);
        match init {
            None => lam,
            Some(init) => RawLambda::let_(LetKind::Strict, init_id, init, lam),
        }
    }
}
