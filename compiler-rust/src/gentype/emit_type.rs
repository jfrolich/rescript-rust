// Port of compiler/gentype/EmitType.ml:1-455.
// This Stage 4 GenType port is intentionally not wired into the crate yet.

use crate::gentype::gen_type_common::{
    ArgType, ClosedFlag, Field, Function, Ident, Mutable, Optional, Payload, Type, Variant, ident,
    ident_with, is_js_safe_property_name, label_js_to_string, sanitize_type_name, unknown,
};

pub fn file_header(source_file: &str) -> String {
    // Mirrors compiler/gentype/EmitType.ml:3-15.
    let lines = vec![format!(
        "TypeScript file generated from {source_file} by genType."
    )];
    let header = match lines.as_slice() {
        [line] => format!("/* {line} */\n\n"),
        _ => format!(
            "/** \n{}\n */\n\n",
            lines
                .iter()
                .map(|line| format!(" * {line}"))
                .collect::<Vec<_>>()
                .join("\n")
        ),
    };
    format!("{header}/* eslint-disable */\n/* tslint:disable */\n")
}

pub fn interface_name(config: &crate::gentype::config::T, name: &str) -> String {
    // Mirrors compiler/gentype/EmitType.ml:16-19.
    match config.export_interfaces {
        true => format!("I{name}"),
        false => name.to_string(),
    }
}

// Mirrors compiler/gentype/EmitType.ml:21-61.
pub fn type_any() -> Type {
    ident("any")
}

pub fn type_react_component(props_type: Type) -> Type {
    ident_with(true, vec![props_type], "React.ComponentType")
}

pub fn type_react_context(type_: Type) -> Type {
    ident_with(true, vec![type_], "React.Context")
}

pub fn type_react_element_type_script() -> Type {
    ident("React.JSX.Element")
}

pub fn type_react_child_type_script() -> Type {
    ident("React.ReactNode")
}

pub fn type_react_element() -> Type {
    type_react_element_type_script()
}

pub fn type_react_child() -> Type {
    type_react_child_type_script()
}

pub fn is_type_react_element(type_: &Type) -> bool {
    *type_ == type_react_element()
}

pub fn type_react_d_o_m_re_dom_ref() -> Type {
    ident_with(true, vec![unknown()], "React.Ref")
}

pub fn type_react_event_mouse_t() -> Type {
    ident("MouseEvent")
}

pub const REACT_REF_CURRENT: &str = "current";

pub fn type_react_ref(type_: Type) -> Type {
    Type::Object(
        ClosedFlag::Open,
        vec![Field {
            mutable_: Mutable::Mutable,
            name_js: REACT_REF_CURRENT.to_string(),
            optional: Optional::Mandatory,
            type_: Type::Null(Box::new(type_)),
            doc_string: crate::gentype::gen_type_common::doc_string::empty,
        }],
    )
}

pub fn is_type_react_ref(fields: &[Field]) -> bool {
    // Mirrors compiler/gentype/EmitType.ml:54-58.
    matches!(
        fields,
        [Field {
            mutable_: Mutable::Mutable,
            name_js,
            optional: Optional::Mandatory,
            ..
        }] if name_js == REACT_REF_CURRENT
    )
}

pub fn is_type_function_component(fields: &[Field], type_: &Type) -> bool {
    is_type_react_element(type_) && !is_type_react_ref(fields)
}

pub fn render_type(
    config: &crate::gentype::config::T,
    indent: crate::gentype::indent::T,
    type_name_is_interface: &impl Fn(&str) -> bool,
    in_fun_type: bool,
    type0: &Type,
) -> String {
    // Mirrors compiler/gentype/EmitType.ml:63-253.
    match type0 {
        Type::Array(t, array_kind) => {
            let type_is_simple = matches!(t.as_ref(), Type::Ident(_) | Type::TypeVar(_));
            if type_is_simple && *array_kind == Mutable::Mutable {
                format!(
                    "{}[]",
                    render_type(config, indent, type_name_is_interface, in_fun_type, t)
                )
            } else {
                let array_name = match *array_kind == Mutable::Mutable {
                    true => "Array",
                    false => "ReadonlyArray",
                };
                format!(
                    "{array_name}<{}>",
                    render_type(config, indent, type_name_is_interface, in_fun_type, t)
                )
            }
        }
        Type::Dict(type_) => format!(
            "{{[id: string]: {}}}",
            render_type(config, indent, type_name_is_interface, in_fun_type, type_)
        ),
        Type::Function(Function {
            arg_types,
            ret_type,
            type_vars,
        }) if matches!(
            arg_types.as_slice(),
            [ArgType {
                a_type: Type::Object(_, _),
                ..
            }]
        ) && match &arg_types[0].a_type {
            Type::Object(_, fields) => is_type_function_component(fields, ret_type),
            _ => false,
        } =>
        {
            let Type::Object(closed_flag, fields) = &arg_types[0].a_type else {
                unreachable!()
            };
            let fields = fields
                .iter()
                .map(|field| {
                    let mut field = field.clone();
                    field.type_ =
                        crate::gentype::type_vars::substitute(&field.type_, &|s| match type_vars
                            .iter()
                            .any(|type_var| type_var == s)
                        {
                            true => Some(type_any()),
                            false => None,
                        });
                    field
                })
                .collect::<Vec<_>>();
            render_type(
                config,
                indent,
                type_name_is_interface,
                in_fun_type,
                &type_react_component(Type::Object(*closed_flag, fields)),
            )
        }
        Type::Function(Function {
            arg_types,
            ret_type,
            type_vars,
        }) => render_fun_type(
            config,
            indent,
            in_fun_type,
            type_name_is_interface,
            type_vars,
            arg_types,
            ret_type,
        ),
        Type::Object(_, fields) => {
            let indent1 = crate::gentype::indent::heuristic_fields(&indent, fields);
            render_fields(config, indent1, in_fun_type, type_name_is_interface, fields)
        }
        Type::Ident(Ident {
            builtin,
            name,
            type_args,
        }) => {
            let name = sanitize_type_name(name);
            let name = match !builtin && config.export_interfaces && type_name_is_interface(&name) {
                true => interface_name(config, &name),
                false => name,
            };
            let rendered_type_args = type_args
                .iter()
                .map(|type_arg| {
                    render_type(
                        config,
                        indent.clone(),
                        type_name_is_interface,
                        in_fun_type,
                        type_arg,
                    )
                })
                .collect::<Vec<_>>();
            format!(
                "{}{}",
                name,
                crate::gentype::emit_text::generics_string(&rendered_type_args)
            )
        }
        Type::Null(type_) => format!(
            "(null | {})",
            render_type(config, indent, type_name_is_interface, in_fun_type, type_)
        ),
        Type::Nullable(type_) => {
            let rendered = render_type(config, indent, type_name_is_interface, in_fun_type, type_);
            let rendered = match type_.as_ref() {
                Type::Function(_) | Type::Variant(_) => {
                    crate::gentype::emit_text::parens(&[rendered])
                }
                _ => rendered,
            };
            format!("(null | undefined | {rendered})")
        }
        Type::Option(type_) => {
            let rendered = render_type(config, indent, type_name_is_interface, in_fun_type, type_);
            let rendered = match type_.as_ref() {
                Type::Function(_) | Type::Variant(_) => {
                    crate::gentype::emit_text::parens(&[rendered])
                }
                _ => rendered,
            };
            format!("(undefined | {rendered})")
        }
        Type::Promise(type_) => format!(
            "Promise<{}>",
            render_type(config, indent, type_name_is_interface, in_fun_type, type_)
        ),
        Type::Tuple(inner_types) => format!(
            "[{}]",
            inner_types
                .iter()
                .map(|type_| {
                    render_type(
                        config,
                        indent.clone(),
                        type_name_is_interface,
                        in_fun_type,
                        type_,
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::TypeVar(s) => s.clone(),
        Type::Variant(variant) => {
            render_variant(config, indent, type_name_is_interface, in_fun_type, variant)
        }
    }
}

pub fn render_field(
    config: &crate::gentype::config::T,
    indent: crate::gentype::indent::T,
    type_name_is_interface: &impl Fn(&str) -> bool,
    in_fun_type: bool,
    Field {
        mutable_,
        name_js: lbl,
        optional,
        type_,
        doc_string,
    }: &Field,
) -> String {
    // Mirrors compiler/gentype/EmitType.ml:254-280.
    let opt_marker = match optional == &Optional::Optional {
        true => "?",
        false => "",
    };
    let mut_marker = match mutable_ == &Mutable::Immutable {
        true => "readonly ",
        false => "",
    };
    let lbl = match is_js_safe_property_name(lbl) {
        true => lbl.clone(),
        false => crate::gentype::emit_text::quotes(lbl),
    };
    let def_str = format!(
        "{mut_marker}{lbl}{opt_marker}: {}",
        render_type(
            config,
            indent.clone(),
            type_name_is_interface,
            in_fun_type,
            type_
        )
    );
    if crate::gentype::gen_type_common::doc_string::has_content(doc_string) {
        let indent_str = indent.clone().unwrap_or_default();
        format!(
            "\n{}{}{}{}",
            indent_str,
            crate::gentype::gen_type_common::doc_string::render(doc_string),
            indent_str,
            def_str
        )
    } else {
        format!("{}{}", crate::gentype::indent::break_(&indent), def_str)
    }
}

pub fn render_fields(
    config: &crate::gentype::config::T,
    indent: crate::gentype::indent::T,
    in_fun_type: bool,
    type_name_is_interface: &impl Fn(&str) -> bool,
    fields: &[Field],
) -> String {
    // Mirrors compiler/gentype/EmitType.ml:282-297.
    let indent1 = crate::gentype::indent::more(&indent);
    let space = match indent.is_none() && !fields.is_empty() {
        true => " ",
        false => "",
    };
    let rendered_fields = fields
        .iter()
        .map(|field| {
            render_field(
                config,
                indent1.clone(),
                type_name_is_interface,
                in_fun_type,
                field,
            )
        })
        .collect::<Vec<_>>();
    format!(
        "{{{space}{}{}{space}}}",
        rendered_fields.join("; "),
        crate::gentype::indent::break_(&indent)
    )
}

pub fn render_fun_type(
    config: &crate::gentype::config::T,
    indent: crate::gentype::indent::T,
    in_fun_type: bool,
    type_name_is_interface: &impl Fn(&str) -> bool,
    type_vars: &[String],
    arg_types: &[ArgType],
    ret_type: &Type,
) -> String {
    // Mirrors compiler/gentype/EmitType.ml:299-327.
    format!(
        "{}{}({}) => {}{}",
        match in_fun_type {
            true => "(",
            false => "",
        },
        crate::gentype::emit_text::generics_string(type_vars),
        arg_types
            .iter()
            .enumerate()
            .map(|(i, ArgType { a_name, a_type })| {
                let parameter_name = match a_name.is_empty() {
                    true => format!("_{}:", i + 1),
                    false => format!("{a_name}:"),
                };
                format!(
                    "{}{}",
                    parameter_name,
                    render_type(config, indent.clone(), type_name_is_interface, true, a_type)
                )
            })
            .collect::<Vec<_>>()
            .join(", "),
        render_type(
            config,
            indent,
            type_name_is_interface,
            in_fun_type,
            ret_type
        ),
        match in_fun_type {
            true => ")",
            false => "",
        }
    )
}

pub fn type_to_string(
    config: &crate::gentype::config::T,
    type_name_is_interface: &impl Fn(&str) -> bool,
    type_: &Type,
) -> String {
    // Mirrors compiler/gentype/EmitType.ml:328-329.
    render_type(config, None, type_name_is_interface, false, type_)
}

pub fn emit_export_const(
    early: bool,
    comment: &str,
    config: &crate::gentype::config::T,
    doc_string: crate::gentype::gen_type_common::doc_string::T,
    emitters: crate::gentype::emitters::T,
    name: &str,
    type_: &Type,
    type_name_is_interface: &impl Fn(&str) -> bool,
    line: &str,
) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitType.ml:331-343.
    let type_string = type_to_string(config, type_name_is_interface, type_);
    let output = format!(
        "{}{}export const {name}: {type_string} = {line} as any;",
        match comment.is_empty() {
            true => String::new(),
            false => format!("// {comment}\n"),
        },
        crate::gentype::gen_type_common::doc_string::render(&doc_string)
    );
    if early {
        crate::gentype::emitters::export_early(emitters, output)
    } else {
        crate::gentype::emitters::export(emitters, output)
    }
}

pub fn emit_export_default(
    emitters: crate::gentype::emitters::T,
    name: &str,
) -> crate::gentype::emitters::T {
    crate::gentype::emitters::export(emitters, format!("export default {name};"))
}

pub fn emit_export_type(
    config: &crate::gentype::config::T,
    emitters: crate::gentype::emitters::T,
    name_as: Option<String>,
    opaque: bool,
    type_: &Type,
    type_name_is_interface: &impl Fn(&str) -> bool,
    type_vars: &[String],
    doc_string: crate::gentype::gen_type_common::doc_string::T,
    resolved_type_name: &str,
) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitType.ml:348-388.
    let doc_string = crate::gentype::gen_type_common::doc_string::render(&doc_string);
    let type_params_string = crate::gentype::emit_text::generics_string(type_vars);
    let is_interface = type_name_is_interface(resolved_type_name);
    let resolved_type_name = match config.export_interfaces && is_interface {
        true => interface_name(config, resolved_type_name),
        false => resolved_type_name.to_string(),
    };
    let export_name_as = match name_as {
        None => String::new(),
        Some(s) => format!(
            "\nexport type {s}{type_params_string} = {resolved_type_name}{type_params_string};"
        ),
    };
    let output = if opaque {
        let type_of_opaque_field = match type_vars.is_empty() {
            true => "any".to_string(),
            false => type_vars.join(" | "),
        };
        format!(
            "{doc_string}export abstract class {resolved_type_name}{type_params_string} {{ protected opaque!: {type_of_opaque_field} }}; /* simulate opaque types */{export_name_as}"
        )
    } else {
        format!(
            "{}{}{};{}",
            doc_string,
            if is_interface && config.export_interfaces {
                format!("export interface {resolved_type_name}{type_params_string} ")
            } else {
                format!("export type {resolved_type_name}{type_params_string} = ")
            },
            type_to_string(config, type_name_is_interface, type_),
            export_name_as
        )
    };
    crate::gentype::emitters::export(emitters, output)
}

pub fn emit_import_value_as_early(
    emitters: crate::gentype::emitters::T,
    name: &str,
    name_as: Option<String>,
    import_path: &crate::gentype::import_path::T,
) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitType.ml:390-398.
    crate::gentype::emitters::require_early(
        emitters,
        format!(
            "import {} from '{}';",
            match name_as {
                Some(name_as) => format!("{{{name} as {name_as}}}"),
                None => name.to_string(),
            },
            crate::gentype::import_path::emit(import_path)
        ),
    )
}

pub fn emit_require(
    imported_value_or_component: bool,
    early: bool,
    emitters: crate::gentype::emitters::T,
    config: &crate::gentype::config::T,
    module_name: &crate::gentype::module_name::T,
    import_path: &crate::gentype::import_path::T,
) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitType.ml:400-417.
    let module_name_string = crate::gentype::module_name::to_string(module_name);
    let import_path_string = crate::gentype::import_path::emit(import_path);
    let output = match config.module_ {
        crate::gentype::config::Module::ESModule if !imported_value_or_component => {
            format!("import * as {module_name_string} from '{import_path_string}';")
        }
        _ => format!("const {module_name_string} = require('{import_path_string}');"),
    };
    if early {
        crate::gentype::emitters::require_early(emitters, output)
    } else {
        crate::gentype::emitters::require(emitters, output)
    }
}

pub fn emit_import_react(emitters: crate::gentype::emitters::T) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitType.ml:419-425.
    require(
        true,
        emitters,
        "import * as React from 'react';".to_string(),
    )
}

pub fn require(
    early: bool,
    emitters: crate::gentype::emitters::T,
    output: String,
) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitType.ml:419-422.
    if early {
        crate::gentype::emitters::require_early(emitters, output)
    } else {
        crate::gentype::emitters::require(emitters, output)
    }
}

pub fn emit_import_type_as(
    emitters: crate::gentype::emitters::T,
    config: &crate::gentype::config::T,
    type_name: &str,
    as_type_name: Option<String>,
    type_name_is_interface: &impl Fn(&str) -> bool,
    import_path: &crate::gentype::import_path::T,
) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitType.ml:427-452.
    let type_name = sanitize_type_name(type_name);
    let as_type_name = as_type_name.map(|s| sanitize_type_name(&s));
    let (type_name, as_type_name) = match as_type_name {
        Some(as_name) if type_name_is_interface(&as_name) => (
            interface_name(config, &type_name),
            Some(interface_name(config, &as_name)),
        ),
        other => (type_name, other),
    };
    crate::gentype::emitters::import(
        emitters,
        format!(
            "import type {{{}{}}} from '{}';",
            type_name,
            match as_type_name {
                Some(as_t) => format!(" as {as_t}"),
                None => String::new(),
            },
            crate::gentype::import_path::emit(import_path)
        ),
    )
}

pub fn emit_type_cast(
    config: &crate::gentype::config::T,
    type_: &Type,
    type_name_is_interface: &impl Fn(&str) -> bool,
    s: &str,
) -> String {
    // Mirrors compiler/gentype/EmitType.ml:454-455.
    format!(
        "{s} as {}",
        type_to_string(config, type_name_is_interface, type_)
    )
}

fn render_variant(
    config: &crate::gentype::config::T,
    indent: crate::gentype::indent::T,
    type_name_is_interface: &impl Fn(&str) -> bool,
    in_fun_type: bool,
    Variant {
        inherits,
        no_payloads,
        payloads,
        polymorphic,
        tag,
        unboxed,
    }: &Variant,
) -> String {
    let inherits_rendered = inherits
        .iter()
        .map(|type_| {
            render_type(
                config,
                indent.clone(),
                type_name_is_interface,
                in_fun_type,
                type_,
            )
        })
        .collect::<Vec<_>>();
    let no_payloads_rendered = no_payloads
        .iter()
        .map(label_js_to_string)
        .collect::<Vec<_>>();
    let field = |name: String, value: String| Field {
        mutable_: Mutable::Mutable,
        name_js: name,
        optional: Optional::Mandatory,
        type_: Type::TypeVar(value),
        doc_string: crate::gentype::gen_type_common::doc_string::empty,
    };
    let fields = |fields: Vec<Field>| {
        render_fields(
            config,
            indent.clone(),
            in_fun_type,
            type_name_is_interface,
            &fields,
        )
    };
    let payloads_rendered = payloads
        .iter()
        .map(|Payload { case, t: type_ }| {
            let render = |t: &Type| {
                render_type(
                    config,
                    indent.clone(),
                    type_name_is_interface,
                    in_fun_type,
                    t,
                )
            };
            let tag_field = field(
                crate::gentype::runtime::js_variant_tag(false, tag.as_deref()),
                label_js_to_string(case),
            );
            match (*unboxed, type_) {
                (true, type_) => {
                    let t = render(type_);
                    match type_ {
                        Type::Function(_) => crate::gentype::emit_text::parens(&[t]),
                        _ => t,
                    }
                }
                (false, type_) if *polymorphic => fields(vec![
                    field(
                        crate::gentype::runtime::js_variant_tag(*polymorphic, tag.as_deref()),
                        label_js_to_string(case),
                    ),
                    field(
                        crate::gentype::runtime::js_variant_value(*polymorphic),
                        render(type_),
                    ),
                ]),
                (false, Type::Object(ClosedFlag::Inline, flds)) => {
                    let mut flds = flds.clone();
                    flds.insert(0, tag_field);
                    fields(flds)
                }
                (false, type_) => {
                    let payloads = match type_ {
                        Type::Tuple(ts) => ts.clone(),
                        _ => vec![type_.clone()],
                    };
                    let mut flds = vec![tag_field];
                    flds.extend(payloads.into_iter().enumerate().map(|(n, t)| {
                        field(
                            crate::gentype::runtime::js_variant_payload_tag(n as i32),
                            render(&t),
                        )
                    }));
                    fields(flds)
                }
            }
        })
        .collect::<Vec<_>>();
    let mut rendered = inherits_rendered;
    rendered.extend(no_payloads_rendered);
    rendered.extend(payloads_rendered);
    let indent1 = crate::gentype::indent::heuristic_variants(&indent, &rendered);
    format!(
        "{}{}",
        match indent1.is_none() {
            true => String::new(),
            false => format!("{}  ", crate::gentype::indent::break_(&indent1)),
        },
        rendered.join(&format!(
            "{}| ",
            match indent1.is_none() {
                true => " ".to_string(),
                false => crate::gentype::indent::break_(&indent1),
            }
        ))
    )
}
