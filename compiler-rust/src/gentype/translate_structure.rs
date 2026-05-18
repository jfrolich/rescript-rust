// Port of compiler/gentype/TranslateStructure.ml:1-366.
// This Stage 3 GenType port is intentionally not wired into the crate yet.

use crate::gentype::gen_type_common::{ArgType, StringSet, Type};
use crate::parse_arena::ParseArena;
use crate::types::decl::ModuleType as DeclModuleType;
use crate::types::typedtree::{
    ApplyArg, Expression, ExpressionDesc, FunctionParam, ModuleBinding, ModuleExprDesc,
    ModuleTypeConstraint, Pattern, PatternDesc, Structure, StructureItem, StructureItemDesc,
    ValueBinding,
};

#[allow(non_snake_case)]
pub fn addAnnotationsToTypes_(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    expr: &Expression,
    arg_types: &[ArgType],
) -> Vec<ArgType> {
    // Mirrors compiler/gentype/TranslateStructure.ml:3-32.
    match (&expr.exp_desc, arg_types.split_first()) {
        (
            ExpressionDesc::Texp_function { params, body, .. },
            Some((ArgType { a_type, .. }, next_types)),
        ) if !params.is_empty() && !body.is_empty() => {
            let next_types1 = addAnnotationsToTypes_(arena, config, &body[0].c_rhs, next_types);
            let a_name = function_param_name(arena, &params[0]);
            let mut out = vec![ArgType {
                a_name,
                a_type: a_type.clone(),
            }];
            out.extend(next_types1);
            out
        }
        (ExpressionDesc::Texp_apply { funct, args, .. }, _)
            if is_uncurried_fn_mk_apply(funct, args) =>
        {
            if let Some(expr1) = args.iter().find_map(|arg| arg.expression.as_ref()) {
                addAnnotationsToTypes_(arena, config, expr1, arg_types)
            } else {
                arg_types.to_vec()
            }
        }
        _ => arg_types.to_vec(),
    }
}

pub fn add_annotations_to_types(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    expr: &Expression,
    arg_types: &[ArgType],
) -> Vec<ArgType> {
    // Mirrors compiler/gentype/TranslateStructure.ml:34-47.
    let arg_types = addAnnotationsToTypes_(arena, config, expr, arg_types);
    if arg_types
        .iter()
        .filter(|ArgType { a_name, .. }| a_name == "param")
        .count()
        > 1
    {
        arg_types
            .into_iter()
            .enumerate()
            .map(|(i, ArgType { a_name, a_type })| ArgType {
                a_name: format!("{a_name}_{i}"),
                a_type,
            })
            .collect()
    } else {
        arg_types
    }
}

pub fn add_annotations_to_fields(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    expr: &Expression,
    fields: &[crate::gentype::gen_type_common::Field],
    arg_types: &[ArgType],
) -> (Vec<crate::gentype::gen_type_common::Field>, Vec<ArgType>) {
    // Mirrors compiler/gentype/TranslateStructure.ml:48-62.
    match (&expr.exp_desc, fields.split_first()) {
        (_, None) => (
            vec![],
            add_annotations_to_types(arena, config, expr, arg_types),
        ),
        (ExpressionDesc::Texp_function { body, .. }, Some((field, next_fields)))
            if !body.is_empty() =>
        {
            let (next_fields1, types1) =
                add_annotations_to_fields(arena, config, &body[0].c_rhs, next_fields, arg_types);
            let mut field = field.clone();
            field.name_js = crate::gentype::translate_type_declarations::rename_record_field(
                arena,
                &expr.exp_attributes,
                &field.name_js,
            );
            let mut fields = vec![field];
            fields.extend(next_fields1);
            (fields, types1)
        }
        _ => (fields.to_vec(), arg_types.to_vec()),
    }
}

pub fn add_annotations_to_function_type(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    expr: &Expression,
    type_: Type,
) -> Type {
    // Mirrors compiler/gentype/TranslateStructure.ml:64-73.
    match type_ {
        Type::Function(mut function_) => {
            function_.arg_types =
                add_annotations_to_types(arena, config, expr, &function_.arg_types);
            Type::Function(function_)
        }
        _ => type_,
    }
}

pub fn remove_value_binding_duplicates(structure_items: &[StructureItem]) -> Vec<StructureItem> {
    // Mirrors compiler/gentype/TranslateStructure.ml:75-102.
    fn process_bindings(bindings: &[ValueBinding], seen: &mut StringSet) -> Vec<ValueBinding> {
        let mut out = Vec::new();
        for binding in bindings {
            match &binding.vb_pat.pat_desc {
                PatternDesc::Tpat_var(id, _) => {
                    let name = id.name().to_string();
                    if !seen.contains(&name) {
                        seen.insert(name);
                        out.push(binding.clone());
                    }
                }
                _ => out.push(binding.clone()),
            }
        }
        out
    }

    let mut seen = StringSet::new();
    let mut acc = Vec::new();
    for item in structure_items.iter().rev() {
        let mut item = item.clone();
        if let StructureItemDesc::Tstr_value(rec_flag, value_bindings) = &item.str_desc {
            item.str_desc = StructureItemDesc::Tstr_value(
                rec_flag.clone(),
                process_bindings(value_bindings, &mut seen),
            );
        }
        acc.push(item);
    }
    acc.reverse();
    acc
}

pub fn translate_value_binding(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    value_binding: &ValueBinding,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateStructure.ml:103-123.
    let id = match value_binding_id(&value_binding.vb_pat) {
        None => return crate::gentype::translation::empty(),
        Some(id) => id,
    };
    let name = unwrap_uppercase_exotic(id.name()).to_string();
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Translate Value Binding {name}\n"));
    }
    let module_item = crate::gentype::runtime::new_module_item(&name);
    crate::gentype::type_env::update_module_item(module_item, type_env);
    if crate::gentype::annotation::from_attributes(
        arena,
        config,
        value_binding.vb_pat.pat_loc,
        &value_binding.vb_attributes,
    ) == crate::gentype::annotation::T::GenType
    {
        crate::gentype::translation::translate_value(
            ctx,
            arena,
            &value_binding.vb_attributes,
            config,
            crate::gentype::annotation::doc_string_from_attrs(arena, &value_binding.vb_attributes),
            output_file_relative,
            resolver,
            type_env,
            value_binding.vb_pat.pat_type,
            |t| add_annotations_to_function_type(arena, config, &value_binding.vb_expr, t),
            &name,
        )
    } else {
        crate::gentype::translation::empty()
    }
}

pub fn remove_duplicate_value_bindings(
    structure_items: &[StructureItem],
) -> (StringSet, Vec<StructureItem>) {
    // Mirrors compiler/gentype/TranslateStructure.ml:125-159.
    match structure_items.split_first() {
        Some((structure_item, rest)) => {
            let (mut bound_in_rest, filtered_rest) = remove_duplicate_value_bindings(rest);
            match &structure_item.str_desc {
                StructureItemDesc::Tstr_value(rec_flag, value_bindings) => {
                    let value_bindings_filtered = value_bindings
                        .iter()
                        .filter(|value_binding| match &value_binding.vb_pat.pat_desc {
                            PatternDesc::Tpat_var(id, _) => !bound_in_rest.contains(id.name()),
                            _ => true,
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    for value_binding in value_bindings {
                        if let PatternDesc::Tpat_var(id, _) = &value_binding.vb_pat.pat_desc {
                            bound_in_rest.insert(id.name().to_string());
                        }
                    }
                    let mut item = structure_item.clone();
                    item.str_desc =
                        StructureItemDesc::Tstr_value(rec_flag.clone(), value_bindings_filtered);
                    let mut out = vec![item];
                    out.extend(filtered_rest);
                    (bound_in_rest, out)
                }
                _ => {
                    let mut out = vec![structure_item.clone()];
                    out.extend(filtered_rest);
                    (bound_in_rest, out)
                }
            }
        }
        None => (StringSet::new(), vec![]),
    }
}

pub fn translate_module_binding(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    module_binding: &ModuleBinding,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateStructure.ml:161-270.
    let name = module_binding.mb_id.name();
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Translate Module Binding {name}\n"));
    }
    let module_item = crate::gentype::runtime::new_module_item(name);
    let config = crate::gentype::annotation::update_config_for_module(
        arena,
        config,
        &module_binding.mb_attributes,
    );
    crate::gentype::type_env::update_module_item(module_item, type_env);
    let type_env = crate::gentype::type_env::new_module(name, type_env);

    match &module_binding.mb_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(path, _) => {
            let dep = crate::gentype::dependencies::from_path(&config, &type_env, path);
            let internal = crate::gentype::dependencies::is_internal(&dep);
            crate::gentype::type_env::add_module_equation(dep, internal, &type_env);
            match &module_binding.mb_expr.mod_type {
                DeclModuleType::MtySignature(signature) => crate::gentype::translation::combine(
                    &crate::gentype::translate_signature_from_types::translate_signature_from_types(
                        ctx,
                        arena,
                        &config,
                        output_file_relative,
                        resolver,
                        &type_env,
                        signature,
                    ),
                ),
                DeclModuleType::MtyAlias(_, _)
                | DeclModuleType::MtyIdent(_)
                | DeclModuleType::MtyFunctor { .. } => crate::gentype::translation::empty(),
            }
        }
        ModuleExprDesc::Tmod_structure(structure) => {
            let is_let_private = crate::gentype::annotation::has_attribute(
                arena,
                crate::gentype::annotation::tag_is_intern_local,
                &module_binding.mb_attributes,
            );
            if is_let_private {
                crate::gentype::translation::empty()
            } else {
                crate::gentype::translation::combine(&translate_structure(
                    ctx,
                    arena,
                    &config,
                    output_file_relative,
                    resolver,
                    &type_env,
                    structure,
                ))
            }
        }
        ModuleExprDesc::Tmod_apply(_, _, _) => match &module_binding.mb_expr.mod_type {
            DeclModuleType::MtySignature(signature) => crate::gentype::translation::combine(
                &crate::gentype::translate_signature_from_types::translate_signature_from_types(
                    ctx,
                    arena,
                    &config,
                    output_file_relative,
                    resolver,
                    &type_env,
                    signature,
                ),
            ),
            DeclModuleType::MtyIdent(_) => not_implemented("Mty_ident"),
            DeclModuleType::MtyFunctor { .. } => not_implemented("Mty_functor"),
            DeclModuleType::MtyAlias(_, _) => not_implemented("Mty_alias"),
        },
        ModuleExprDesc::Tmod_unpack(_, module_type) => match module_type {
            DeclModuleType::MtySignature(signature) => crate::gentype::translation::combine(
                &crate::gentype::translate_signature_from_types::translate_signature_from_types(
                    ctx,
                    arena,
                    &config,
                    output_file_relative,
                    resolver,
                    &type_env,
                    signature,
                ),
            ),
            DeclModuleType::MtyIdent(path) => {
                match crate::gentype::type_env::lookup_module_type_signature(path, &type_env) {
                    None => crate::gentype::translation::empty(),
                    Some((signature, _, type_env)) => crate::gentype::translation::combine(
                        &crate::gentype::translate_signature::translate_signature(
                            ctx,
                            arena,
                            &config,
                            output_file_relative,
                            resolver,
                            &type_env,
                            &signature,
                        ),
                    ),
                }
            }
            DeclModuleType::MtyFunctor { .. } => not_implemented("Mty_functor"),
            DeclModuleType::MtyAlias(_, _) => not_implemented("Mty_alias"),
        },
        ModuleExprDesc::Tmod_functor(_, _, _, _) => not_implemented("Tmod_functor"),
        ModuleExprDesc::Tmod_constraint(_, module_type, module_type_constraint, coercion) => {
            translate_module_constraint(
                ctx,
                arena,
                &config,
                output_file_relative,
                resolver,
                &type_env,
                module_type,
                module_type_constraint,
                coercion,
            )
        }
    }
}

pub fn translate_structure_item(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    struct_item: &StructureItem,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateStructure.ml:272-357.
    match &struct_item.str_desc {
        StructureItemDesc::Tstr_type(rec_flag, type_declarations) => {
            crate::gentype::translation::T {
                import_types: vec![],
                code_items: vec![],
                type_declarations:
                    crate::gentype::translate_type_declarations::translate_type_declarations(
                        ctx,
                        arena,
                        config,
                        output_file_relative,
                        matches!(rec_flag, crate::parser::ast::RecFlag::Recursive),
                        resolver,
                        type_env,
                        type_declarations,
                    ),
            }
        }
        StructureItemDesc::Tstr_value(_, value_bindings) => crate::gentype::translation::combine(
            &value_bindings
                .iter()
                .map(|value_binding| {
                    translate_value_binding(
                        ctx,
                        arena,
                        config,
                        output_file_relative,
                        resolver,
                        type_env,
                        value_binding,
                    )
                })
                .collect::<Vec<_>>(),
        ),
        StructureItemDesc::Tstr_primitive(value_description) => {
            crate::gentype::translation::translate_primitive(
                ctx,
                arena,
                config,
                output_file_relative,
                resolver,
                type_env,
                value_description,
            )
        }
        StructureItemDesc::Tstr_module(module_binding) => translate_module_binding(
            ctx,
            arena,
            config,
            output_file_relative,
            resolver,
            type_env,
            module_binding,
        ),
        StructureItemDesc::Tstr_modtype(module_type_declaration) => {
            crate::gentype::translate_signature::translate_module_type_declaration(
                ctx,
                arena,
                config,
                output_file_relative,
                resolver,
                type_env,
                module_type_declaration,
            )
        }
        StructureItemDesc::Tstr_recmodule(module_bindings) => crate::gentype::translation::combine(
            &module_bindings
                .iter()
                .map(|module_binding| {
                    translate_module_binding(
                        ctx,
                        arena,
                        config,
                        output_file_relative,
                        resolver,
                        type_env,
                        module_binding,
                    )
                })
                .collect::<Vec<_>>(),
        ),
        StructureItemDesc::Tstr_include(include_declaration) => {
            crate::gentype::translation::combine(
                &crate::gentype::translate_signature_from_types::translate_signature_from_types(
                    ctx,
                    arena,
                    config,
                    output_file_relative,
                    resolver,
                    type_env,
                    &include_declaration.incl_type,
                ),
            )
        }
        StructureItemDesc::Tstr_eval(_, _) => not_implemented("Tstr_eval"),
        StructureItemDesc::Tstr_typext(_) => not_implemented("Tstr_typext"),
        StructureItemDesc::Tstr_exception(_) => not_implemented("Tstr_exception"),
        StructureItemDesc::Tstr_open(_) => not_implemented("Tstr_open"),
        StructureItemDesc::Tstr_attribute(_) => not_implemented("Tstr_attribute"),
    }
}

pub fn translate_structure(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    structure: &Structure,
) -> Vec<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/TranslateStructure.ml:359-366.
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item("Translate Structure\n");
    }
    remove_value_binding_duplicates(&structure.str_items)
        .iter()
        .map(|struct_item| {
            translate_structure_item(
                ctx,
                arena,
                config,
                output_file_relative,
                resolver,
                type_env,
                struct_item,
            )
        })
        .collect()
}

fn translate_module_constraint(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    module_type: &DeclModuleType,
    module_type_constraint: &ModuleTypeConstraint,
    _coercion: &crate::types::typedtree::ModuleCoercion,
) -> crate::gentype::translation::T {
    match (module_type, module_type_constraint) {
        (DeclModuleType::MtyIdent(path), ModuleTypeConstraint::Tmodtype_explicit(_)) => {
            match crate::gentype::type_env::lookup_module_type_signature(path, type_env) {
                None => crate::gentype::translation::empty(),
                Some((signature, _, type_env)) => crate::gentype::translation::combine(
                    &crate::gentype::translate_signature::translate_signature(
                        ctx,
                        arena,
                        config,
                        output_file_relative,
                        resolver,
                        &type_env,
                        &signature,
                    ),
                ),
            }
        }
        (DeclModuleType::MtySignature(signature), ModuleTypeConstraint::Tmodtype_explicit(_)) => {
            crate::gentype::translation::combine(
                &crate::gentype::translate_signature_from_types::translate_signature_from_types(
                    ctx,
                    arena,
                    config,
                    output_file_relative,
                    resolver,
                    type_env,
                    signature,
                ),
            )
        }
        (_, ModuleTypeConstraint::Tmodtype_explicit(module_type))
            if matches!(
                module_type.mty_desc,
                crate::types::typedtree::ModuleTypeDesc::Tmty_signature(_)
            ) =>
        {
            if let crate::types::typedtree::ModuleTypeDesc::Tmty_signature(signature) =
                &module_type.mty_desc
            {
                crate::gentype::translation::combine(
                    &crate::gentype::translate_signature::translate_signature(
                        ctx,
                        arena,
                        config,
                        output_file_relative,
                        resolver,
                        type_env,
                        signature,
                    ),
                )
            } else {
                crate::gentype::translation::empty()
            }
        }
        _ => not_implemented("Tmod_constraint"),
    }
}

fn value_binding_id(pattern: &Pattern) -> Option<&crate::ident::Ident> {
    match &pattern.pat_desc {
        PatternDesc::Tpat_var(id, _) => Some(id),
        PatternDesc::Tpat_alias(inner, id, _)
            if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
        {
            Some(id)
        }
        _ => None,
    }
}

fn function_param_name(arena: &ParseArena, param: &FunctionParam) -> String {
    let a_name = param.param_id.name();
    if a_name == "*opt*" {
        match &param.label {
            crate::parser::ast::ArgLabel::Optional(loc) => arena.get_string(loc.txt).to_string(),
            _ => String::new(),
        }
    } else {
        a_name.to_string()
    }
}

fn is_uncurried_fn_mk_apply(funct: &Expression, args: &[ApplyArg]) -> bool {
    if args.len() != 1 || args[0].expression.is_none() {
        return false;
    }
    match &funct.exp_desc {
        ExpressionDesc::Texp_ident(path, _, _) => {
            let mut path = crate::gentype::translate_type_expr_from_types::path_to_list(path);
            path.reverse();
            matches!(path.as_slice(), [a, b, fn_mk] if a == "Js" && b == "Internal" && fn_mk.starts_with("fn_mk"))
        }
        _ => false,
    }
}

fn not_implemented(name: &str) -> crate::gentype::translation::T {
    crate::gentype::gen_type_common::log_not_implemented(&format!(
        "{name} compiler/gentype/TranslateStructure.ml"
    ));
    crate::gentype::translation::empty()
}

fn unwrap_uppercase_exotic(name: &str) -> &str {
    let bytes = name.as_bytes();
    if bytes.len() >= 3 && bytes[0] == b'\\' && bytes[1] == b'"' && bytes[bytes.len() - 1] == b'"' {
        &name[2..name.len() - 1]
    } else {
        name
    }
}
