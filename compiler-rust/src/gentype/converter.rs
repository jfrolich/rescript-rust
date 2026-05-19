// Port of compiler/gentype/Converter.ml:1-89.
// This Stage 4 GenType port is intentionally not wired into the crate yet.

use crate::gentype::code_item;
use crate::gentype::gen_type_common::{
    ArgType, Function, Ident, Payload, StringSet, Type, Variant,
};

pub fn type_get_inlined(
    config: &crate::gentype::config::T,
    lookup_id: &impl Fn(&str) -> Option<code_item::ExportTypeItem>,
    type_name_is_interface: &impl Fn(&str) -> bool,
    type0: &Type,
) -> Type {
    // Mirrors compiler/gentype/Converter.ml:3-89.
    fn visit(
        config: &crate::gentype::config::T,
        lookup_id: &impl Fn(&str) -> Option<code_item::ExportTypeItem>,
        type_name_is_interface: &impl Fn(&str) -> bool,
        circular: &mut String,
        visited: &StringSet,
        type_: &Type,
    ) -> Type {
        match type_ {
            Type::Array(t, mutable_) => Type::Array(
                Box::new(visit(
                    config,
                    lookup_id,
                    type_name_is_interface,
                    circular,
                    visited,
                    t,
                )),
                *mutable_,
            ),
            Type::Dict(_) => type_.clone(),
            Type::Function(function_) => Type::Function(Function {
                arg_types: function_
                    .arg_types
                    .iter()
                    .map(|arg_type| {
                        arg_type_to_grouped_arg(
                            config,
                            lookup_id,
                            type_name_is_interface,
                            circular,
                            visited,
                            arg_type,
                        )
                    })
                    .collect(),
                ret_type: Box::new(visit(
                    config,
                    lookup_id,
                    type_name_is_interface,
                    circular,
                    visited,
                    &function_.ret_type,
                )),
                type_vars: function_.type_vars.clone(),
            }),
            Type::Ident(Ident { builtin: true, .. }) => type_.clone(),
            Type::Ident(Ident {
                builtin: false,
                name,
                type_args,
            }) => {
                if visited.contains(name) {
                    *circular = name.clone();
                    type_.clone()
                } else {
                    let mut visited = visited.clone();
                    visited.insert(name.clone());
                    // Mirrors compiler/gentype/Converter.ml:26-46: a missing
                    // type id takes the Not_found branch and keeps the Ident
                    // shape while recursively visiting its type arguments.
                    match lookup_id(name) {
                        Some(code_item::ExportTypeItem {
                            annotation: crate::gentype::annotation::T::GenTypeOpaque,
                            ..
                        })
                        | Some(code_item::ExportTypeItem {
                            annotation: crate::gentype::annotation::T::NoGenType,
                            ..
                        }) => type_.clone(),
                        Some(code_item::ExportTypeItem {
                            type_vars, type_, ..
                        }) => {
                            let pairs = type_vars
                                .iter()
                                .cloned()
                                .zip(type_args.iter().cloned())
                                .collect::<Vec<_>>();
                            let substituted =
                                crate::gentype::type_vars::substitute(&type_, &|type_var| {
                                    pairs
                                        .iter()
                                        .find(|(type_var1, _)| type_var == type_var1)
                                        .map(|(_, type_argument)| type_argument.clone())
                                });
                            visit(
                                config,
                                lookup_id,
                                type_name_is_interface,
                                circular,
                                &visited,
                                &substituted,
                            )
                        }
                        None => Type::Ident(Ident {
                            builtin: false,
                            name: name.clone(),
                            type_args: type_args
                                .iter()
                                .map(|t| {
                                    visit(
                                        config,
                                        lookup_id,
                                        type_name_is_interface,
                                        circular,
                                        &visited,
                                        t,
                                    )
                                })
                                .collect(),
                        }),
                    }
                }
            }
            Type::Null(t) => Type::Null(Box::new(visit(
                config,
                lookup_id,
                type_name_is_interface,
                circular,
                visited,
                t,
            ))),
            Type::Nullable(t) => Type::Nullable(Box::new(visit(
                config,
                lookup_id,
                type_name_is_interface,
                circular,
                visited,
                t,
            ))),
            Type::Object(_, _) => type_.clone(),
            Type::Option(t) => Type::Option(Box::new(visit(
                config,
                lookup_id,
                type_name_is_interface,
                circular,
                visited,
                t,
            ))),
            Type::Promise(t) => Type::Promise(Box::new(visit(
                config,
                lookup_id,
                type_name_is_interface,
                circular,
                visited,
                t,
            ))),
            Type::Tuple(inner_types) => Type::Tuple(
                inner_types
                    .iter()
                    .map(|t| {
                        visit(
                            config,
                            lookup_id,
                            type_name_is_interface,
                            circular,
                            visited,
                            t,
                        )
                    })
                    .collect(),
            ),
            Type::TypeVar(_) => type_.clone(),
            Type::Variant(variant) => {
                let ordinary_variant = !variant.polymorphic;
                let with_payload_converted = variant
                    .payloads
                    .iter()
                    .map(|payload| Payload {
                        t: visit(
                            config,
                            lookup_id,
                            type_name_is_interface,
                            circular,
                            visited,
                            &payload.t,
                        ),
                        ..payload.clone()
                    })
                    .collect::<Vec<_>>();
                match with_payload_converted.as_slice() {
                    [] if ordinary_variant => type_.clone(),
                    [_payload] if ordinary_variant => Type::Variant(Variant {
                        payloads: with_payload_converted,
                        ..variant.clone()
                    }),
                    _ => Type::Variant(Variant {
                        payloads: with_payload_converted,
                        ..variant.clone()
                    }),
                }
            }
        }
    }

    fn arg_type_to_grouped_arg(
        config: &crate::gentype::config::T,
        lookup_id: &impl Fn(&str) -> Option<code_item::ExportTypeItem>,
        type_name_is_interface: &impl Fn(&str) -> bool,
        circular: &mut String,
        visited: &StringSet,
        ArgType { a_name, a_type }: &ArgType,
    ) -> ArgType {
        ArgType {
            a_name: a_name.clone(),
            a_type: visit(
                config,
                lookup_id,
                type_name_is_interface,
                circular,
                visited,
                a_type,
            ),
        }
    }

    let mut circular = String::new();
    let normalized = visit(
        config,
        lookup_id,
        type_name_is_interface,
        &mut circular,
        &StringSet::new(),
        type0,
    );
    if crate::gentype::debug::converter.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "type0:{} \n",
            crate::gentype::emit_type::type_to_string(config, type_name_is_interface, type0)
        ));
    }
    normalized
}
