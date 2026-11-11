//! Port of `Ast_helper.Jsx_component` (`compiler/ml/ast_helper.ml`):
//! `@react.component` and its variants are taken out of the attributes when a
//! value binding or value description is built, so every producer (the
//! parser, a ppx, the frozen AST bridge) agrees on what is a component.

use crate::parse_arena::{Located, ParseArena};
use crate::parser::ast::{
    Attribute, Attributes, JsxComponent, JsxComponentKind, JsxComponentNamespace, Payload,
    ValueBinding, ValueDescription,
};

/// OCaml `Jsx_component.of_attribute`.
pub fn of_attribute(arena: &ParseArena, attr: &Attribute) -> Option<JsxComponent> {
    let (name, payload) = attr;
    let (namespace, with_props) = match arena.get_string(name.txt) {
        "react.component" => (JsxComponentNamespace::React, false),
        "jsx.component" => (JsxComponentNamespace::Jsx, false),
        "react.componentWithProps" => (JsxComponentNamespace::React, true),
        "jsx.componentWithProps" => (JsxComponentNamespace::Jsx, true),
        _ => return None,
    };
    let kind = match payload {
        Payload::PStr(items) if items.is_empty() => {
            if with_props {
                JsxComponentKind::WithProps
            } else {
                JsxComponentKind::Labelled(None)
            }
        }
        Payload::PTyp(typ) if !with_props => JsxComponentKind::Labelled(Some(*typ)),
        _ => return None,
    };
    Some(JsxComponent {
        pjc_kind: kind,
        pjc_namespace: namespace,
        pjc_loc: name.loc,
    })
}

/// OCaml `Jsx_component.to_attribute`.
pub fn to_attribute(arena: &ParseArena, component: &JsxComponent) -> Attribute {
    let name = arena.jsx_component_attribute_name(&component.pjc_kind, component.pjc_namespace);
    let payload = match component.pjc_kind {
        JsxComponentKind::Labelled(Some(typ)) => Payload::PTyp(typ),
        JsxComponentKind::Labelled(None) | JsxComponentKind::WithProps => {
            Payload::PStr(Box::default())
        }
    };
    (
        Located {
            txt: name,
            loc: component.pjc_loc,
        },
        payload,
    )
}

/// OCaml `Jsx_component.take`: the first `@react.component`, or failing that
/// the first `@react.componentWithProps` (the JSX transform has always given
/// them this precedence), and the other attributes. A later one, or one
/// whose payload is not understood, is left in the attributes for the JSX
/// transform to reject, so that formatting does not drop it.
pub fn take(arena: &ParseArena, attrs: Attributes) -> (Option<Box<JsxComponent>>, Attributes) {
    let find = |labelled: bool| {
        attrs.iter().enumerate().find_map(|(index, attr)| {
            of_attribute(arena, attr)
                .filter(|component| {
                    matches!(component.pjc_kind, JsxComponentKind::Labelled(_)) == labelled
                })
                .map(|component| (index, component))
        })
    };
    let Some((index, component)) = find(true).or_else(|| find(false)) else {
        return (None, attrs);
    };
    let rest = attrs
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != index)
        .map(|(_, attr)| attr.clone())
        .collect();
    (Some(Box::new(component)), Attributes::from_vec(rest))
}

/// OCaml `Jsx_component.put_back`, the inverse of [`take`], for printers and
/// the frozen AST bridge. Attributes print in source order, so the
/// annotation goes back where it was written. Ppx output has no source
/// position, so all of it ties on `Location.none`; the annotation then goes
/// first among the tied, where it is usually written.
pub fn put_back(
    arena: &ParseArena,
    component: Option<&JsxComponent>,
    attrs: &Attributes,
) -> Attributes {
    let Some(component) = component else {
        return attrs.clone();
    };
    let start = arena.loc_start(component.pjc_loc).cnum;
    let (earlier, later): (Vec<&Attribute>, Vec<&Attribute>) = attrs
        .iter()
        .partition(|(name, _)| arena.loc_start(name.loc).cnum < start);
    let mut out = Vec::with_capacity(attrs.len() + 1);
    out.extend(earlier.into_iter().cloned());
    out.push(to_attribute(arena, component));
    out.extend(later.into_iter().cloned());
    Attributes::from_vec(out)
}

/// OCaml `Ast_helper.Vb.binding_attributes`: the attributes as written.
pub fn binding_attributes(arena: &ParseArena, vb: &ValueBinding) -> Attributes {
    put_back(arena, vb.pvb_jsx_component.as_deref(), &vb.pvb_attributes)
}

/// OCaml `Ast_helper.Val.description_attributes`: the attributes as written.
pub fn description_attributes(arena: &ParseArena, vd: &ValueDescription) -> Attributes {
    put_back(arena, vd.pval_jsx_component.as_deref(), &vd.pval_attributes)
}
