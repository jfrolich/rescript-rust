// Port of compiler/gentype/EmitJs.ml:1-711.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use crate::gentype::code_item;
use crate::gentype::gen_type_common::{
    ArgType, Field, Function, Ident, StringMap, Type, doc_string, unknown,
};

pub type RequiresMap = BTreeMap<crate::gentype::module_name::T, crate::gentype::import_path::T>;

#[derive(Debug, Clone)]
pub struct Env {
    pub requires_early: RequiresMap,
    pub requires: RequiresMap,
    /// For each .cmt we import types from, keep the map of exported types.
    pub cmt_to_export_type_map: StringMap<code_item::ExportTypeMap>,
    /// Map of types imported from other files.
    pub export_type_map_from_other_files: code_item::ExportTypeMap,
    pub imported_value_or_component: bool,
}

pub type InputCmtTranslateTypeDeclarations<'a> = dyn Fn(
        &mut crate::gentype::config::T,
        &str,
        &crate::gentype::module_resolver::Resolver,
        &str,
    ) -> crate::gentype::translation::T
    + 'a;

pub type GetCmtFile<'a> = dyn Fn(&str) -> String + 'a;

pub fn require_module(
    import: bool,
    mut env: Env,
    import_path: crate::gentype::import_path::T,
    module_name: &crate::gentype::module_name::T,
) -> Env {
    // Mirrors compiler/gentype/EmitJs.ml:13-24.
    if import {
        env.requires_early.insert(module_name.clone(), import_path);
    } else {
        env.requires.insert(module_name.clone(), import_path);
    }
    env
}

pub fn create_export_type_map(
    config: &crate::gentype::config::T,
    file: &str,
    from_cmt_read_recursively: bool,
    type_declarations: &[code_item::TypeDeclaration],
) -> code_item::ExportTypeMap {
    // Mirrors compiler/gentype/EmitJs.ml:26-61.
    if crate::gentype::debug::code_items.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Create Type Map for {file}\n"));
    }

    let mut export_type_map = StringMap::new();
    for type_declaration in type_declarations {
        let code_item::ExportFromTypeDeclaration {
            export_type,
            annotation,
        } = &type_declaration.export_from_type_declaration;
        let annotation = match annotation {
            crate::gentype::annotation::T::NoGenType if from_cmt_read_recursively => {
                crate::gentype::annotation::T::GenType
            }
            annotation => *annotation,
        };

        if crate::gentype::debug::code_items.load(std::sync::atomic::Ordering::Relaxed) {
            crate::gentype::log_::item(&format!(
                "Type Map: {}{} {}\n",
                crate::gentype::resolved_name::to_string(&export_type.resolved_type_name),
                match export_type.type_vars.is_empty() {
                    true => String::new(),
                    false => format!("({})", export_type.type_vars.join(",")),
                },
                format!(
                    "{} = {}",
                    crate::gentype::emit_text::comment(crate::gentype::annotation::to_string(
                        annotation
                    )),
                    crate::gentype::emit_type::type_to_string(
                        config,
                        &|_| false,
                        &export_type.type_
                    )
                )
            ));
        }

        export_type_map.insert(
            crate::gentype::resolved_name::to_string(&export_type.resolved_type_name),
            code_item::ExportTypeItem {
                type_vars: export_type.type_vars.clone(),
                type_: export_type.type_.clone(),
                annotation,
            },
        );
    }
    export_type_map
}

pub fn code_item_to_string(
    config: &crate::gentype::config::T,
    type_name_is_interface: &impl Fn(&str) -> bool,
    code_item: &code_item::T,
) -> String {
    // Mirrors compiler/gentype/EmitJs.ml:63-72.
    match code_item {
        code_item::T::ExportValue(code_item::ExportValue {
            resolved_name,
            type_,
            ..
        }) => format!(
            "ExportValue resolvedName:{} type:{}",
            crate::gentype::resolved_name::to_string(resolved_name),
            crate::gentype::emit_type::type_to_string(config, type_name_is_interface, type_)
        ),
        code_item::T::ImportValue(code_item::ImportValue {
            import_annotation, ..
        }) => format!(
            "ImportValue {}",
            crate::gentype::import_path::dump(&import_annotation.import_path)
        ),
    }
}

pub fn emit_export_type(
    emitters: crate::gentype::emitters::T,
    config: &crate::gentype::config::T,
    type_name_is_interface: &impl Fn(&str) -> bool,
    export_type: &code_item::ExportType,
) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitJs.ml:74-108.
    let free_type_vars = crate::gentype::type_vars::free(&export_type.type_);
    let is_gadt = free_type_vars
        .iter()
        .any(|s| !export_type.type_vars.iter().any(|type_var| type_var == s));
    let opaque = match export_type.opaque {
        Some(true) => export_type.opaque,
        _ if is_gadt => {
            crate::gentype::log_::color::setup();
            crate::gentype::log_::info(
                || {
                    format!(
                        "GADT types are not supported: exporting {} as opaque type",
                        crate::gentype::resolved_name::to_string(&export_type.resolved_type_name)
                    )
                },
                &export_type.loc,
                "Warning genType",
            );
            Some(true)
        }
        opaque => opaque,
    };
    let opaque = opaque.unwrap_or(false);
    let resolved_type_name =
        crate::gentype::resolved_name::to_string(&export_type.resolved_type_name);
    crate::gentype::emit_type::emit_export_type(
        config,
        emitters,
        export_type.name_as.clone(),
        opaque,
        &export_type.type_,
        type_name_is_interface,
        &export_type.type_vars,
        export_type.doc_string.clone(),
        &resolved_type_name,
    )
}

pub fn type_name_is_interface(
    export_type_map: &code_item::ExportTypeMap,
    export_type_map_from_other_files: &code_item::ExportTypeMap,
    type_name: &str,
) -> bool {
    // Mirrors compiler/gentype/EmitJs.ml:109-121.
    fn type_is_interface(type_: &Type) -> bool {
        matches!(type_, Type::Object(_, _))
    }

    export_type_map
        .get(type_name)
        .map(|item| type_is_interface(&item.type_))
        .or_else(|| {
            export_type_map_from_other_files
                .get(type_name)
                .map(|item| type_is_interface(&item.type_))
        })
        .unwrap_or(false)
}

pub fn emit_export_from_type_declaration(
    config: &crate::gentype::config::T,
    emitters: crate::gentype::emitters::T,
    env: Env,
    type_name_is_interface: &impl Fn(&str) -> bool,
    export_from_type_declaration: &code_item::ExportFromTypeDeclaration,
) -> (Env, crate::gentype::emitters::T) {
    // Mirrors compiler/gentype/EmitJs.ml:123-128.
    (
        env,
        emit_export_type(
            emitters,
            config,
            type_name_is_interface,
            &export_from_type_declaration.export_type,
        ),
    )
}

pub fn emit_export_from_type_declarations(
    config: &crate::gentype::config::T,
    emitters: crate::gentype::emitters::T,
    env: Env,
    type_name_is_interface: &impl Fn(&str) -> bool,
    export_from_type_declarations: &[code_item::ExportFromTypeDeclaration],
) -> (Env, crate::gentype::emitters::T) {
    // Mirrors compiler/gentype/EmitJs.ml:130-137.
    export_from_type_declarations.iter().fold(
        (env, emitters),
        |(env, emitters), export_from_type_declaration| {
            emit_export_from_type_declaration(
                config,
                emitters,
                env,
                type_name_is_interface,
                export_from_type_declaration,
            )
        },
    )
}

fn replace_react_element_children(fields: &[Field], filter_key: bool) -> Vec<Field> {
    // Mirrors the repeated React props field rewrites in
    // compiler/gentype/EmitJs.ml:175-183, 202-211, 295-303, and 331-340.
    fields
        .iter()
        .filter_map(|field| match field.name_js.as_str() {
            "children" if crate::gentype::emit_type::is_type_react_element(&field.type_) => {
                let mut field = field.clone();
                field.type_ = crate::gentype::emit_type::type_react_child();
                Some(field)
            }
            "key" if filter_key => None,
            _ => Some(field.clone()),
        })
        .collect()
}

#[derive(Debug, Clone)]
pub struct HookType {
    pub props_type: Type,
    pub resolved_type_name: crate::gentype::resolved_name::T,
    pub type_vars: Vec<String>,
}

pub fn emit_code_item(
    config: &mut crate::gentype::config::T,
    emitters: crate::gentype::emitters::T,
    module_items_emitter: &mut crate::gentype::export_module::ExportModuleItems,
    env: Env,
    file_name: &crate::gentype::module_name::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    inline_one_level: &impl Fn(&Type) -> Type,
    type_name_is_interface: &impl Fn(&str) -> bool,
    code_item: &code_item::T,
) -> (Env, crate::gentype::emitters::T) {
    // Mirrors compiler/gentype/EmitJs.ml:139-389.
    if crate::gentype::debug::code_items.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Code Item: {}\n",
            code_item_to_string(config, type_name_is_interface, code_item)
        ));
    }

    match code_item {
        code_item::T::ImportValue(code_item::ImportValue {
            as_path,
            import_annotation,
            type_,
            value_name,
        }) => {
            let import_path = &import_annotation.import_path;
            let (first_name_in_path, rest_of_path) = if value_name == as_path {
                (value_name.clone(), String::new())
            } else {
                let parts = as_path.split('.').collect::<Vec<_>>();
                match parts.as_slice() {
                    [x, rest @ ..] => {
                        let rest_of_path = match rest.is_empty() {
                            true => String::new(),
                            false => format!(".{}", rest.join(".")),
                        };
                        ((*x).to_string(), rest_of_path)
                    }
                    _ => (as_path.clone(), String::new()),
                }
            };

            let value_name_not_checked = format!("{value_name}NotChecked");
            let emitters = crate::gentype::emit_type::emit_import_value_as_early(
                emitters,
                &first_name_in_path,
                Some(value_name_not_checked.clone()),
                import_path,
            );
            let imported_as_name = value_name_not_checked;

            let type_ = match type_ {
                Type::Function(function_) if function_.arg_types.len() == 1 => {
                    let arg = &function_.arg_types[0];
                    match &arg.a_type {
                        Type::Object(closed_flag, fields)
                            if crate::gentype::emit_type::is_type_function_component(
                                fields,
                                function_.ret_type.as_ref(),
                            ) =>
                        {
                            let fields = replace_react_element_children(fields, false);
                            Type::Function(Function {
                                arg_types: vec![ArgType {
                                    a_type: Type::Object(*closed_flag, fields),
                                    a_name: arg.a_name.clone(),
                                }],
                                ret_type: function_.ret_type.clone(),
                                type_vars: function_.type_vars.clone(),
                            })
                        }
                        Type::Ident(Ident { name, .. })
                            if name.ends_with("props")
                                && crate::gentype::emit_type::is_type_function_component(
                                    &[],
                                    function_.ret_type.as_ref(),
                                ) =>
                        {
                            match inline_one_level(&arg.a_type) {
                                Type::Object(closed_flags, fields) => {
                                    let fields = replace_react_element_children(&fields, true);
                                    Type::Function(Function {
                                        arg_types: vec![ArgType {
                                            a_type: Type::Object(closed_flags, fields),
                                            a_name: arg.a_name.clone(),
                                        }],
                                        ret_type: function_.ret_type.clone(),
                                        type_vars: function_.type_vars.clone(),
                                    })
                                }
                                _ => type_.clone(),
                            }
                        }
                        _ => type_.clone(),
                    }
                }
                _ => type_.clone(),
            };

            let value_name_type_checked = format!("{value_name}TypeChecked");
            let checked_line = format!("{imported_as_name}{rest_of_path}");
            let comment = format!(
                "In case of type error, check the type of '{value_name}' in '{}.res' and '{}'.",
                crate::gentype::module_name::to_string(file_name),
                crate::gentype::import_path::emit(import_path)
            );
            let emitters = crate::gentype::emit_type::emit_export_const(
                true,
                &comment,
                config,
                doc_string::empty,
                emitters,
                &value_name_type_checked,
                &type_,
                type_name_is_interface,
                &checked_line,
            );

            let value_name_not_default = match value_name.as_str() {
                "default" => crate::gentype::runtime::default.to_string(),
                _ => value_name.clone(),
            };
            let cast_line = crate::gentype::emit_type::emit_type_cast(
                config,
                &type_,
                type_name_is_interface,
                &value_name_type_checked,
            );
            let unknown = unknown();
            let emitters = crate::gentype::emit_type::emit_export_const(
                true,
                &format!(
                    "Export '{value_name_not_default}' early to allow circular import from the '.bs.js' file."
                ),
                config,
                doc_string::empty,
                emitters,
                &value_name_not_default,
                &unknown,
                type_name_is_interface,
                &cast_line,
            );
            let emitters = match value_name.as_str() {
                "default" => crate::gentype::emit_type::emit_export_default(
                    emitters,
                    &value_name_not_default,
                ),
                _ => emitters,
            };
            let mut env = env;
            env.imported_value_or_component = true;
            (env, emitters)
        }
        code_item::T::ExportValue(code_item::ExportValue {
            doc_string,
            module_access_path,
            original_name,
            resolved_name,
            type_,
        }) => {
            let resolved_name_str = crate::gentype::resolved_name::to_string(resolved_name);
            let suffix = config.suffix.clone();
            let import_path = crate::gentype::module_resolver::resolve_module(
                config,
                &suffix,
                output_file_relative,
                resolver,
                false,
                file_name,
            );
            let file_name_js = crate::gentype::module_name::for_js_file(file_name);
            let env_with_requires = require_module(false, env, import_path, &file_name_js);
            let default = "default";
            let make = "make";
            let name = match original_name == default {
                true => crate::gentype::runtime::default.to_string(),
                false => resolved_name_str,
            };

            let (type_, hook_type) = match type_ {
                Type::Function(function_) if function_.arg_types.len() == 1 => {
                    let arg = &function_.arg_types[0];
                    match &arg.a_type {
                        Type::Object(closed_flags, fields)
                            if crate::gentype::emit_type::is_type_function_component(
                                fields,
                                function_.ret_type.as_ref(),
                            ) =>
                        {
                            let fields = replace_react_element_children(fields, false);
                            let props_type = Type::Object(*closed_flags, fields);
                            let type_vars = function_.type_vars.clone();
                            let function_ = Function {
                                arg_types: vec![ArgType {
                                    a_name: String::new(),
                                    a_type: props_type.clone(),
                                }],
                                ret_type: function_.ret_type.clone(),
                                type_vars: type_vars.clone(),
                            };
                            let resolved_type_name = if !config.emit_type_prop_done
                                && (original_name == default || original_name == make)
                            {
                                config.emit_type_prop_done = true;
                                crate::gentype::resolved_name::from_string("Props")
                            } else {
                                crate::gentype::resolved_name::dot(
                                    "Props",
                                    &crate::gentype::resolved_name::from_string(&name),
                                )
                            };
                            (
                                Type::Function(function_),
                                Some(HookType {
                                    props_type,
                                    resolved_type_name,
                                    type_vars,
                                }),
                            )
                        }
                        Type::Ident(Ident { name, .. })
                            if name.ends_with("props")
                                && crate::gentype::emit_type::is_type_function_component(
                                    &[],
                                    function_.ret_type.as_ref(),
                                ) =>
                        {
                            let comp_type = match inline_one_level(&arg.a_type) {
                                Type::Object(closed_flags, fields) => {
                                    let fields = replace_react_element_children(&fields, true);
                                    Type::Function(Function {
                                        arg_types: vec![ArgType {
                                            a_name: String::new(),
                                            a_type: Type::Object(closed_flags, fields),
                                        }],
                                        ret_type: function_.ret_type.clone(),
                                        type_vars: function_.type_vars.clone(),
                                    })
                                }
                                _ => type_.clone(),
                            };
                            (comp_type, None)
                        }
                        _ => (type_.clone(), None),
                    }
                }
                _ => (type_.clone(), None),
            };

            crate::gentype::export_module::extend_export_modules(
                module_items_emitter,
                doc_string.clone(),
                type_.clone(),
                resolved_name,
            );
            let emitters = match hook_type {
                Some(HookType {
                    props_type,
                    resolved_type_name,
                    type_vars,
                }) => {
                    let export_type = code_item::ExportType {
                        loc: crate::location::Location::none(),
                        name_as: None,
                        opaque: Some(false),
                        type_: props_type,
                        type_vars,
                        resolved_type_name,
                        doc_string: doc_string.clone(),
                    };
                    config.emit_import_react = true;
                    emit_export_type(emitters, config, type_name_is_interface, &export_type)
                }
                None => emitters,
            };
            let line = format!(
                "{}.{}",
                crate::gentype::module_name::to_string(&file_name_js),
                crate::gentype::runtime::emit_module_access_path(config, module_access_path)
            );
            let emitters = crate::gentype::emit_type::emit_export_const(
                false,
                "",
                config,
                doc_string.clone(),
                emitters,
                &name,
                &type_,
                type_name_is_interface,
                &line,
            );
            let emitters = match original_name == default {
                true => crate::gentype::emit_type::emit_export_default(
                    emitters,
                    crate::gentype::runtime::default,
                ),
                false => emitters,
            };
            (env_with_requires, emitters)
        }
    }
}

pub fn emit_code_items(
    config: &mut crate::gentype::config::T,
    output_file_relative: &str,
    emitters: crate::gentype::emitters::T,
    module_items_emitter: &mut crate::gentype::export_module::ExportModuleItems,
    env: Env,
    file_name: &crate::gentype::module_name::T,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_name_is_interface: &impl Fn(&str) -> bool,
    inline_one_level: &impl Fn(&Type) -> Type,
    code_items: &[code_item::T],
) -> (Env, crate::gentype::emitters::T) {
    // Mirrors compiler/gentype/EmitJs.ml:391-400.
    code_items
        .iter()
        .fold((env, emitters), |(env, emitters), code_item| {
            emit_code_item(
                config,
                emitters,
                module_items_emitter,
                env,
                file_name,
                output_file_relative,
                resolver,
                inline_one_level,
                type_name_is_interface,
                code_item,
            )
        })
}

pub fn emit_requires(
    imported_value_or_component: bool,
    early: bool,
    config: &crate::gentype::config::T,
    requires: &RequiresMap,
    emitters: crate::gentype::emitters::T,
) -> crate::gentype::emitters::T {
    // Mirrors compiler/gentype/EmitJs.ml:402-409.
    requires
        .iter()
        .fold(emitters, |emitters, (module_name, import_path)| {
            crate::gentype::emit_type::emit_require(
                imported_value_or_component,
                early,
                emitters,
                config,
                module_name,
                import_path,
            )
        })
}

pub fn type_get_inlined(
    config: &crate::gentype::config::T,
    export_type_map: &code_item::ExportTypeMap,
    type_: &Type,
) -> Type {
    // Mirrors compiler/gentype/EmitJs.ml:411-415.
    crate::gentype::converter::type_get_inlined(
        config,
        &|s| export_type_map.get(s).cloned(),
        &|_| false,
        type_,
    )
}

pub fn read_cmt_files_recursively(
    config: &mut crate::gentype::config::T,
    env: Env,
    get_cmt_file: &GetCmtFile<'_>,
    input_cmt_translate_type_declarations: &InputCmtTranslateTypeDeclarations<'_>,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    import_type: &code_item::ImportType,
) -> Env {
    // Mirrors compiler/gentype/EmitJs.ml:417-484.
    fn update_type_map_from_other_files(
        config: &crate::gentype::config::T,
        type_name: &str,
        as_type: &str,
        export_type_map_from_cmt: &code_item::ExportTypeMap,
        mut env: Env,
    ) -> Env {
        match export_type_map_from_cmt.get(type_name) {
            Some(export_type_item) => {
                let type_ =
                    type_get_inlined(config, export_type_map_from_cmt, &export_type_item.type_);
                let mut export_type_item = export_type_item.clone();
                export_type_item.type_ = type_;
                env.export_type_map_from_other_files
                    .insert(as_type.to_string(), export_type_item);
                env
            }
            None => env,
        }
    }

    // Mirrors compiler/gentype/EmitJs.ml:438-453: resolve the imported
    // module through ImportPath.to_cmt and Paths.get_cmt_file before reading
    // declarations from that typed artifact.
    let cmt_file = get_cmt_file(&crate::gentype::import_path::to_cmt(
        config,
        output_file_relative,
        &import_type.import_path,
    ));

    match (&import_type.as_type_name, cmt_file.as_str()) {
        (Some(as_type), cmt_file) if !cmt_file.is_empty() => {
            match env.cmt_to_export_type_map.get(cmt_file).cloned() {
                Some(export_type_map_from_cmt) => update_type_map_from_other_files(
                    config,
                    &import_type.type_name,
                    as_type,
                    &export_type_map_from_cmt,
                    env,
                ),
                None => {
                    let translation = input_cmt_translate_type_declarations(
                        config,
                        output_file_relative,
                        resolver,
                        cmt_file,
                    );
                    let type_declarations = translation.type_declarations;
                    let file = Path::new(cmt_file)
                        .file_name()
                        .and_then(|s| s.to_str())
                        .and_then(|s| s.rsplit_once('.').map(|(stem, _)| stem.to_string()))
                        .unwrap_or_else(|| cmt_file.to_string());
                    let export_type_map_from_cmt =
                        create_export_type_map(config, &file, true, &type_declarations);
                    let mut env = env;
                    env.cmt_to_export_type_map
                        .insert(cmt_file.to_string(), export_type_map_from_cmt.clone());
                    let env = update_type_map_from_other_files(
                        config,
                        &import_type.type_name,
                        as_type,
                        &export_type_map_from_cmt,
                        env,
                    );
                    let new_import_types = type_declarations
                        .iter()
                        .flat_map(|type_declaration| type_declaration.import_types.clone())
                        .collect::<Vec<_>>();
                    new_import_types.iter().fold(env, |env, new_import_type| {
                        read_cmt_files_recursively(
                            config,
                            env,
                            get_cmt_file,
                            input_cmt_translate_type_declarations,
                            output_file_relative,
                            resolver,
                            new_import_type,
                        )
                    })
                }
            }
        }
        _ => env,
    }
}

pub fn emit_import_type(
    config: &mut crate::gentype::config::T,
    emitters: crate::gentype::emitters::T,
    env: Env,
    get_cmt_file: &GetCmtFile<'_>,
    input_cmt_translate_type_declarations: &InputCmtTranslateTypeDeclarations<'_>,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_name_is_interface: &impl Fn(&Env, &str) -> bool,
    import_type: &code_item::ImportType,
) -> (Env, crate::gentype::emitters::T) {
    // Mirrors compiler/gentype/EmitJs.ml:486-500.
    let env = read_cmt_files_recursively(
        config,
        env,
        get_cmt_file,
        input_cmt_translate_type_declarations,
        output_file_relative,
        resolver,
        import_type,
    );
    let emitters = crate::gentype::emit_type::emit_import_type_as(
        emitters,
        config,
        &import_type.type_name,
        import_type.as_type_name.clone(),
        &|type_name| type_name_is_interface(&env, type_name),
        &import_type.import_path,
    );
    (env, emitters)
}

pub fn emit_import_types(
    config: &mut crate::gentype::config::T,
    emitters: crate::gentype::emitters::T,
    env: Env,
    get_cmt_file: &GetCmtFile<'_>,
    input_cmt_translate_type_declarations: &InputCmtTranslateTypeDeclarations<'_>,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_name_is_interface: &impl Fn(&Env, &str) -> bool,
    import_types: &[code_item::ImportType],
) -> (Env, crate::gentype::emitters::T) {
    // Mirrors compiler/gentype/EmitJs.ml:502-511.
    import_types
        .iter()
        .fold((env, emitters), |(env, emitters), import_type| {
            emit_import_type(
                config,
                emitters,
                env,
                get_cmt_file,
                input_cmt_translate_type_declarations,
                output_file_relative,
                resolver,
                type_name_is_interface,
                import_type,
            )
        })
}

pub fn get_annotated_typed_declarations(
    annotated_set: &BTreeSet<String>,
    type_declarations: &[code_item::TypeDeclaration],
) -> Vec<code_item::TypeDeclaration> {
    // Mirrors compiler/gentype/EmitJs.ml:513-537.
    type_declarations
        .iter()
        .filter_map(|type_declaration| {
            let mut type_declaration = type_declaration.clone();
            let name_in_annotated_set =
                annotated_set.contains(&crate::gentype::resolved_name::to_string(
                    &type_declaration
                        .export_from_type_declaration
                        .export_type
                        .resolved_type_name,
                ));
            if name_in_annotated_set {
                type_declaration.export_from_type_declaration.annotation =
                    crate::gentype::annotation::T::GenType;
            }
            match type_declaration.export_from_type_declaration.annotation
                != crate::gentype::annotation::T::NoGenType
            {
                true => Some(type_declaration),
                false => None,
            }
        })
        .collect()
}

pub fn propagate_annotation_to_sub_types(
    code_items: &[code_item::T],
    type_map: &code_item::ExportTypeMap,
) -> (code_item::ExportTypeMap, BTreeSet<String>) {
    // Mirrors compiler/gentype/EmitJs.ml:539-602.
    fn visit(
        type_map: &code_item::ExportTypeMap,
        annotated_set: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
        type_: &Type,
    ) {
        match type_ {
            Type::Ident(Ident {
                name: type_name,
                type_args,
                ..
            }) => {
                if visited.contains(type_name) {
                    return;
                }
                visited.insert(type_name.clone());
                for type_arg in type_args {
                    visit(type_map, annotated_set, visited, type_arg);
                }
                match type_map.get(type_name) {
                    Some(code_item::ExportTypeItem {
                        annotation:
                            crate::gentype::annotation::T::GenType
                            | crate::gentype::annotation::T::GenTypeOpaque,
                        ..
                    }) => {}
                    Some(code_item::ExportTypeItem {
                        type_,
                        annotation: crate::gentype::annotation::T::NoGenType,
                        ..
                    }) => {
                        if crate::gentype::debug::translation
                            .load(std::sync::atomic::Ordering::Relaxed)
                        {
                            crate::gentype::log_::item(&format!(
                                "Marking Type As Annotated {type_name}\n"
                            ));
                        }
                        annotated_set.insert(type_name.clone());
                        visit(type_map, annotated_set, visited, type_);
                    }
                    None => {
                        annotated_set.insert(type_name.clone());
                    }
                }
            }
            Type::Array(t, _) | Type::Dict(t) => visit(type_map, annotated_set, visited, t),
            Type::Function(Function {
                arg_types,
                ret_type,
                ..
            }) => {
                for ArgType { a_type, .. } in arg_types {
                    visit(type_map, annotated_set, visited, a_type);
                }
                visit(type_map, annotated_set, visited, ret_type);
            }
            Type::Object(_, fields) => {
                for Field { type_, .. } in fields {
                    visit(type_map, annotated_set, visited, type_);
                }
            }
            Type::Option(t) | Type::Null(t) | Type::Nullable(t) | Type::Promise(t) => {
                visit(type_map, annotated_set, visited, t)
            }
            Type::Tuple(inner_types) => {
                for type_ in inner_types {
                    visit(type_map, annotated_set, visited, type_);
                }
            }
            Type::TypeVar(_) => {}
            Type::Variant(variant) => {
                for type_ in &variant.inherits {
                    visit(type_map, annotated_set, visited, type_);
                }
                for payload in &variant.payloads {
                    visit(type_map, annotated_set, visited, &payload.t);
                }
            }
        }
    }

    let mut annotated_set = BTreeSet::new();
    let initial_annotated_types = type_map
        .values()
        .filter(|item| item.annotation == crate::gentype::annotation::T::GenType)
        .map(|item| item.type_.clone())
        .collect::<Vec<_>>();
    let types_of_exported_values = code_items
        .iter()
        .map(|code_item| match code_item {
            code_item::T::ExportValue(code_item::ExportValue { type_, .. })
            | code_item::T::ImportValue(code_item::ImportValue { type_, .. }) => type_.clone(),
        })
        .collect::<Vec<_>>();

    for type_ in initial_annotated_types
        .iter()
        .chain(types_of_exported_values.iter())
    {
        let mut visited = BTreeSet::new();
        visit(type_map, &mut annotated_set, &mut visited, type_);
    }

    let new_type_map = type_map
        .iter()
        .map(|(type_name, export_type_item)| {
            let mut export_type_item = export_type_item.clone();
            if annotated_set.contains(type_name) {
                export_type_item.annotation = crate::gentype::annotation::T::GenType;
            }
            (type_name.clone(), export_type_item)
        })
        .collect::<StringMap<_>>();
    (new_type_map, annotated_set)
}

#[allow(non_snake_case)]
pub fn emit_translation_as_string(
    config: &mut crate::gentype::config::T,
    file_name: &crate::gentype::module_name::T,
    get_cmt_file: &GetCmtFile<'_>,
    input_cmt_translate_type_declarations: &InputCmtTranslateTypeDeclarations<'_>,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    translation: &crate::gentype::translation::T,
) -> String {
    // Mirrors compiler/gentype/EmitJs.ml:604-711.
    let initial_env = Env {
        requires: BTreeMap::new(),
        requires_early: BTreeMap::new(),
        cmt_to_export_type_map: StringMap::new(),
        export_type_map_from_other_files: StringMap::new(),
        imported_value_or_component: false,
    };
    let (export_type_map, annotated_set) = propagate_annotation_to_sub_types(
        &translation.code_items,
        &create_export_type_map(
            config,
            &crate::gentype::module_name::to_string(file_name),
            false,
            &translation.type_declarations,
        ),
    );
    let annotated_type_declarations =
        get_annotated_typed_declarations(&annotated_set, &translation.type_declarations);
    let import_types_from_type_declarations = annotated_type_declarations
        .iter()
        .flat_map(|type_declaration| type_declaration.import_types.clone())
        .collect::<Vec<_>>();
    let export_from_type_declarations = annotated_type_declarations
        .iter()
        .map(|type_declaration| type_declaration.export_from_type_declaration.clone())
        .collect::<Vec<_>>();
    let type_name_is_interface_for_env = |env: &Env, type_name: &str| {
        type_name_is_interface(
            &export_type_map,
            &env.export_type_map_from_other_files,
            type_name,
        )
    };
    let lookupId_ = |env: &Env, s: &str| {
        export_type_map
            .get(s)
            .or_else(|| env.export_type_map_from_other_files.get(s))
            .cloned()
    };

    let emitters = crate::gentype::emitters::initial();
    let mut module_items_emitter = crate::gentype::export_module::create_module_items_emitter();
    let env = initial_env;

    let mut import_types = import_types_from_type_declarations;
    import_types.extend(translation.import_types.clone());
    import_types.sort_by(crate::gentype::translation::import_type_compare);
    import_types.dedup_by(|i1, i2| {
        crate::gentype::translation::import_type_compare(i1, i2) == std::cmp::Ordering::Equal
    });
    let (env, emitters) = emit_import_types(
        config,
        emitters,
        env,
        get_cmt_file,
        input_cmt_translate_type_declarations,
        output_file_relative,
        resolver,
        &type_name_is_interface_for_env,
        &import_types,
    );
    let env_for_type_declarations = env.clone();
    let (env, emitters) = emit_export_from_type_declarations(
        config,
        emitters,
        env,
        &|type_name| type_name_is_interface_for_env(&env_for_type_declarations, type_name),
        &export_from_type_declarations,
    );

    let env_for_code_items = env.clone();
    let inline_one_level = |type_: &Type| match type_ {
        Type::Ident(Ident {
            builtin: false,
            name,
            type_args,
        }) => {
            let Some(code_item::ExportTypeItem {
                type_, type_vars, ..
            }) = lookupId_(&env_for_code_items, name)
            else {
                // Mirrors compiler/gentype/EmitJs.ml:662-678: a missing
                // export type while inlining is caught as Not_found and leaves
                // the original type unchanged.
                return type_.clone();
            };
            let pairs = type_vars
                .iter()
                .cloned()
                .zip(type_args.iter().cloned())
                .collect::<Vec<_>>();
            crate::gentype::type_vars::substitute(&type_, &|type_var| {
                pairs
                    .iter()
                    .find(|(type_var1, _)| type_var == type_var1)
                    .map(|(_, type_argument)| type_argument.clone())
            })
        }
        _ => type_.clone(),
    };
    let (env, emitters) = emit_code_items(
        config,
        output_file_relative,
        emitters,
        &mut module_items_emitter,
        env,
        file_name,
        resolver,
        &|type_name| type_name_is_interface_for_env(&env_for_code_items, type_name),
        &inline_one_level,
        &translation.code_items,
    );
    let emitters = match config.emit_import_react {
        true => crate::gentype::emit_type::emit_import_react(emitters),
        false => emitters,
    };
    let env = match config.emit_import_curry {
        true => require_module(
            true,
            env,
            crate::gentype::import_path::bs_curry_path(config),
            &crate::gentype::module_name::curry.to_string(),
        ),
        false => env,
    };
    let final_env = env.clone();
    let emitters = crate::gentype::export_module::emit_all_module_items(
        config,
        emitters,
        file_name,
        &module_items_emitter,
    );
    crate::gentype::emitters::to_string(
        "\n\n",
        emit_requires(
            final_env.imported_value_or_component,
            false,
            config,
            &final_env.requires,
            emit_requires(false, true, config, &final_env.requires_early, emitters),
        ),
    )
}
