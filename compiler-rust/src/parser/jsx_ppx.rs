//! JSX PPX transformation
//!
//! This module transforms JSX syntax into React function calls, matching the OCaml
//! JSX v4 PPX behavior. The transformation is applied after parsing.
//!
//! Transformations:
//! - `<></>` -> `React.jsx(React.jsxFragment, {})`
//! - `<div />` -> `ReactDOM.jsx("div", {})`
//! - `<Component />` -> `React.jsx(Component.make, {})`
//! - Multiple children use `jsxs` instead of `jsx`
//! - Key props use `jsxKeyed`/`jsxsKeyed` instead
//! - `@react.component` transforms functions to accept props record

use std::{borrow::Cow, fmt};

use super::ast::*;
use super::longident::Longident;
use crate::parse_arena::{CoreTypeIdx, ExprIdx, LidentIdx, Located, ParseArena, StrIdx};

/// Component description type - mirrors OCaml's componentDescription
#[derive(Debug, Clone, Copy, PartialEq)]
enum ComponentDescription {
    LowercasedComponent,
    UppercasedComponent,
    FragmentComponent,
}

/// JSX configuration from @@jsxConfig attribute
#[derive(Debug, Clone)]
pub struct JsxConfig {
    /// JSX version (4 for modern JSX, -1 for preserve/no transform)
    pub version: i32,
    /// Module name for JSX functions (default: "React")
    pub module_name: String,
    /// Nested module path for component naming
    pub nested_modules: Vec<String>,
    /// Whether a component has already been defined in this scope
    pub has_component: bool,
    /// File name (without extension, capitalized) for module naming
    pub file_name: String,
    /// First fatal PPX diagnostic found while transforming.
    pub fatal_error: Option<JsxPreprocessorError>,
    /// Per expression index: 0 unknown, 1 its subtree is left unchanged by
    /// `transform_expression`, 2 it may change.
    unchanged_memo: Vec<u8>,
    /// OCaml `empty_loc = Location.in_file file_name` (jsx_v4.ml:1021-1022):
    /// the location of the nodes `map_binding` generates for a component.
    pub empty_loc: Location,
}

impl Default for JsxConfig {
    fn default() -> Self {
        JsxConfig {
            version: -1, // Default: no transformation
            module_name: "React".to_string(),
            nested_modules: vec![],
            has_component: false,
            file_name: String::new(),
            fatal_error: None,
            unchanged_memo: Vec::new(),
            empty_loc: Location::none(),
        }
    }
}

/// Extract capitalized file name from a file path
fn filename_from_loc(loc: &Location, arena: &ParseArena) -> String {
    let file_name_idx = arena.loc_start(*loc).file_name;
    let file_name = arena.get_string(file_name_idx);
    if file_name.is_empty() {
        return String::new();
    }
    // Get basename and remove extension
    let basename = std::path::Path::new(file_name)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or(file_name);
    // Capitalize first character
    let mut chars = basename.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

/// Extracted argument info from a function
#[derive(Debug, Clone)]
struct ExtractedArg {
    /// The argument label
    label: ArgLabel,
    /// Default value if optional with default
    default: Option<Expression>,
    /// The pattern
    pattern: Pattern,
    /// Alias name for the argument
    alias: String,
    /// Location
    loc: Location,
    /// Type constraint if any
    type_: Option<CoreType>,
}

/// Named type info for props
#[derive(Debug, Clone)]
struct NamedType {
    is_optional: bool,
    label: String,
    attrs: Attributes,
    loc: Location,
    /// The interior type - Ptyp_any if no explicit annotation
    interior_type: CoreType,
}

/// Warning emitted by JSX transformation, mapped to warning 22 (Preprocessor warning).
#[derive(Debug, Clone)]
pub struct JsxPreprocessorWarning {
    pub start_pos: crate::location::Position,
    pub end_pos: crate::location::Position,
    pub message: String,
}

/// Fatal JSX PPX diagnostic.
#[derive(Debug, Clone)]
pub struct JsxPreprocessorError {
    pub loc: Location,
    pub message: String,
    pub message_style: JsxPreprocessorMessageStyle,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JsxPreprocessorMessageStyle {
    PrefixedLines,
    FirstLineOnlyPrefix,
}

impl fmt::Display for JsxPreprocessorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for JsxPreprocessorError {}

pub type JsxPreprocessorResult<T> = Result<T, JsxPreprocessorError>;

const REACT_COMPONENT_DESTRUCTURE_MSG: &str = "JSX component calls cannot be destructured.";
const MULTIPLE_COMPONENT_DEFINITIONS_MSG: &str = "Only one component definition is allowed for each module. Move to a submodule or other file if necessary.";
const COMPONENT_WITH_PROPS_EXTERNAL_MSG: &str = "Components cannot be defined as externals when using @react.componentWithProps.\n\nIf you intended to define an external for a React component using a props type,\nuse the type React.component<props> instead.\nAlternatively, use @react.component for an external definition with labeled arguments.";
const COMPONENT_WITH_PROPS_FORWARD_REF_MSG: &str = "Components using React.forwardRef cannot use @react.componentWithProps. Use @react.component instead.";
const COMPONENT_KEY_PROP_MSG: &str = "Key cannot be accessed inside of a component. Don't worry - you can always key a component from its parent!";
const COMPONENT_DUPLICATE_PROP_MSG_PREFIX: &str = "The prop `";
const COMPONENT_DUPLICATE_PROP_MSG_SUFFIX: &str = "` is defined several times in this component.";
const COMPONENT_PROPS_NEED_LABELLED_MSG: &str = "React: props need to be labelled arguments.\nIf you are working with refs be sure to wrap with React.forwardRef.\nIf your component doesn't have any props use () or _ instead of a name.";
const COMPONENT_CALL_NEEDS_FUNCTION_MSG: &str = "JSX component calls can only be on function definitions or component wrappers (forwardRef, memo).";
const STRING_INT_ATTR_UNSUPPORTED_MSG: &str = "@string and @int attributes not supported. See https://github.com/rescript-lang/rescript-compiler/issues/5724";
const COMPONENT_REF_PLAIN_ARGS_MSG: &str =
    "React: react.component refs only support plain arguments and type annotations.";
const JSX_SPREAD_AFTER_PROP_MSG: &str =
    "JSX: use {...p} {x: v} not {x: v} {...p} \n   multiple spreads {...p} {...p} not allowed.";

// ============================================================================
// Public API
// ============================================================================

/// Transform a structure, applying JSX PPX transformations.
pub fn transform_structure_result(
    structure: Structure,
    initial_version: i32,
    initial_module: &str,
    arena: &mut ParseArena,
) -> JsxPreprocessorResult<Structure> {
    let (structure, _) = transform_structure_with_warnings_result(
        structure,
        initial_version,
        initial_module,
        arena,
    )?;
    Ok(structure)
}

/// Transform a structure and collect JSX preprocessor warnings.
pub fn transform_structure_with_warnings_result(
    structure: Structure,
    initial_version: i32,
    initial_module: &str,
    arena: &mut ParseArena,
) -> JsxPreprocessorResult<(Structure, Vec<JsxPreprocessorWarning>)> {
    let (result, warnings) =
        transform_structure_collecting_warnings(structure, initial_version, initial_module, arena);
    result.map(|structure| (structure, warnings))
}

/// Like [`transform_structure_with_warnings_result`], but also returns the
/// warnings reported before a fatal error: OCaml prints each warning as it is
/// raised (`Location.prerr_warning`), before the error escapes.
pub fn transform_structure_collecting_warnings(
    structure: Structure,
    initial_version: i32,
    initial_module: &str,
    arena: &mut ParseArena,
) -> (
    JsxPreprocessorResult<Structure>,
    Vec<JsxPreprocessorWarning>,
) {
    // Extract file name from first item's location
    let file_name = structure
        .first()
        .map(|item| filename_from_loc(&item.pstr_loc, arena))
        .unwrap_or_default();

    // `Location.in_file file_name`: one position shared by start and end.
    let empty_loc = {
        let file_name_idx = arena.intern_string(&file_name);
        let pos = arena.push_pos(file_name_idx, 1, 0, -1);
        arena.push_loc(pos, pos, true)
    };
    let mut config = JsxConfig {
        version: initial_version,
        module_name: initial_module.to_string(),
        file_name,
        empty_loc,
        ..Default::default()
    };

    let mut warnings = vec![];
    let mut result = vec![];
    for item in structure {
        let items = transform_structure_item_multi(item, &mut config, arena, &mut warnings);
        if let Some(error) = config.fatal_error.take() {
            return (Err(error), warnings);
        }
        result.extend(items);
    }
    (Ok(result), warnings)
}

/// Transform a signature, applying JSX PPX transformations.
pub fn transform_signature_result(
    signature: Signature,
    initial_version: i32,
    initial_module: &str,
    arena: &mut ParseArena,
) -> JsxPreprocessorResult<Signature> {
    let (signature, _) = transform_signature_with_warnings_result(
        signature,
        initial_version,
        initial_module,
        arena,
    )?;
    Ok(signature)
}

/// Transform a signature and collect JSX preprocessor warnings.
pub fn transform_signature_with_warnings_result(
    signature: Signature,
    initial_version: i32,
    initial_module: &str,
    arena: &mut ParseArena,
) -> JsxPreprocessorResult<(Signature, Vec<JsxPreprocessorWarning>)> {
    // Extract file name from first item's location
    let file_name = signature
        .first()
        .map(|item| filename_from_loc(&item.psig_loc, arena))
        .unwrap_or_default();

    // `Location.in_file file_name`: one position shared by start and end.
    let empty_loc = {
        let file_name_idx = arena.intern_string(&file_name);
        let pos = arena.push_pos(file_name_idx, 1, 0, -1);
        arena.push_loc(pos, pos, true)
    };
    let mut config = JsxConfig {
        version: initial_version,
        module_name: initial_module.to_string(),
        file_name,
        empty_loc,
        ..Default::default()
    };

    let mut result = vec![];
    let mut warnings = vec![];
    for item in signature {
        let items = transform_signature_item_multi(item, &mut config, arena, &mut warnings);
        if let Some(error) = config.fatal_error.take() {
            return Err(error);
        }
        result.extend(items);
    }
    Ok((result, warnings))
}

// ============================================================================
// Structure Item Transformation
// ============================================================================

/// Transform a structure item, potentially returning multiple items
/// (e.g., props type + transformed function)
fn transform_structure_item_multi(
    item: StructureItem,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> Vec<StructureItem> {
    // Check for @@jsxConfig attribute
    if let StructureItemDesc::Pstr_attribute(attr) = &*item.pstr_desc {
        if arena.get_string(attr.0.txt) == "jsxConfig" {
            update_config_from_attribute(arena, attr, config);
        }
        return vec![item];
    }

    // Only transform if version is 4
    if config.version != 4 {
        return vec![item];
    }

    // Handle Pstr_value with potential @react.component
    if let StructureItemDesc::Pstr_value(val_inner) = *item.pstr_desc {
        let (rec_flag, bindings) = *val_inner;
        return transform_value_bindings(
            rec_flag,
            bindings,
            &item.pstr_loc,
            config,
            arena,
            warnings,
        );
    }

    // Handle Pstr_primitive (external) with potential @react.component
    if let StructureItemDesc::Pstr_primitive(vd) = &*item.pstr_desc {
        if reject_leftover_component_attrs(arena, &vd.pval_attributes, config) {
            return vec![item];
        }
        match vd.pval_jsx_component.as_deref().map(|c| &c.pjc_kind) {
            None => {}
            Some(JsxComponentKind::WithProps) => {
                set_fatal_error_with_style(
                    config,
                    item.pstr_loc,
                    COMPONENT_WITH_PROPS_EXTERNAL_MSG,
                    JsxPreprocessorMessageStyle::FirstLineOnlyPrefix,
                );
                return vec![item];
            }
            Some(JsxComponentKind::Labelled(_)) => {
                return transform_react_component_external(
                    (**vd).clone(),
                    &item.pstr_loc,
                    config,
                    arena,
                );
            }
        }
    }

    // Handle module definitions (for nested module tracking)
    if let StructureItemDesc::Pstr_module(mb) = *item.pstr_desc {
        let transformed = transform_module_binding_with_tracking(*mb, config, arena, warnings);
        return vec![StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_module(Box::new(transformed))),
            pstr_loc: item.pstr_loc,
        }];
    }

    // Default: just transform expressions within
    vec![StructureItem {
        pstr_desc: Box::new(transform_structure_item_desc(
            *item.pstr_desc,
            config,
            arena,
            warnings,
        )),
        pstr_loc: item.pstr_loc,
    }]
}

fn transform_module_binding_with_tracking(
    mb: ModuleBinding,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> ModuleBinding {
    // Track nested module name
    let module_name = arena.get_string(mb.pmb_name.txt).to_string();
    // jsx_v4.ml:1374-1382 only tracks the name; `has_component` is saved and
    // reset by the structure/signature mapper (jsx_ppx.ml:101-123).
    config.nested_modules.push(module_name);

    let transformed = transform_module_binding(mb, config, arena, warnings);

    // Pop the module name
    config.nested_modules.pop();

    transformed
}

/// Transform value bindings, handling @react.component
fn transform_value_bindings(
    rec_flag: RecFlag,
    bindings: Vec<ValueBinding>,
    loc: &Location,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> Vec<StructureItem> {
    let mut props_types = vec![];
    let mut transformed_bindings = vec![];
    let mut new_bindings = vec![];

    for binding in bindings {
        // jsx_v4.ml map_binding: reject leftover annotations, then dispatch
        // on the binding's component node.
        if reject_leftover_component_attrs(arena, &binding.pvb_attributes, config) {
            transformed_bindings.push(binding);
            continue;
        }
        let kind = binding
            .pvb_jsx_component
            .as_deref()
            .map(|c| c.pjc_kind.clone());
        if let Some(JsxComponentKind::Labelled(_)) = kind {
            // Transform @react.component binding
            let (props_type, transformed, new_binding) =
                transform_react_component_binding(binding, rec_flag, loc, config, arena, warnings);

            if let Some(pt) = props_type {
                props_types.push(pt);
            }
            transformed_bindings.push(transformed);
            if let Some(nb) = new_binding {
                new_bindings.push(nb);
            }
        } else if let Some(JsxComponentKind::WithProps) = kind {
            // Transform @react.componentWithProps binding
            let (transformed, new_binding) =
                transform_react_component_with_props_binding(binding, rec_flag, loc, config, arena);

            transformed_bindings.push(transformed);
            if let Some(nb) = new_binding {
                new_bindings.push(nb);
            }
        } else {
            // Just transform expressions within
            transformed_bindings.push(transform_value_binding(binding, config, arena));
        }
    }

    let mut result = props_types;
    result.push(StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
            rec_flag,
            transformed_bindings,
        )))),
        pstr_loc: *loc,
    });

    if !new_bindings.is_empty() {
        // jsx_v4.ml:1045-1052: `{pstr_loc = empty_loc; ...}`.
        result.push(StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
                RecFlag::Nonrecursive,
                new_bindings,
            )))),
            pstr_loc: config.empty_loc,
        });
    }

    result
}

/// Detect component wrappers and extract the inner function expression.
/// Returns `(binding_wrapper, has_forward_ref, internal_expression)`.
///
/// `binding_wrapper` preserves a single outer application wrapper such as
/// `React.memo(...)` or `React.forwardRef(...)` so the generated public binding
/// can be wrapped the same way OCaml's JSX PPX does.
///
/// `internal_expression` rebuilds structural wrappers like `let` and `sequence`
/// around the transformed inner function, matching OCaml's `modified_binding`.
fn spelunk_for_fun_expression(
    arena: &mut ParseArena,
    expr_idx: ExprIdx,
) -> (Option<Expression>, bool, Expression) {
    let expr = arena.get_expr(expr_idx).clone();
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => spelunk_for_fun_expression(arena, braces.expr),
        // let make = (~prop) => ...
        ExpressionDesc::Pexp_fun(_) | ExpressionDesc::Pexp_newtype(_) => (None, false, expr),
        // let make = {let foo = bar in (~prop) => ...}
        ExpressionDesc::Pexp_let(inner) => {
            let (rec_flag, bindings, body_idx) = &**inner;
            let (binding_wrapper, has_forward_ref, inner_expr) =
                spelunk_for_fun_expression(arena, *body_idx);
            let inner_expr_idx = arena.push_expr(inner_expr);
            (
                binding_wrapper,
                has_forward_ref,
                Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                        *rec_flag,
                        bindings.clone(),
                        inner_expr_idx,
                    )))),
                    pexp_loc: expr.pexp_loc,
                    pexp_attributes: expr.pexp_attributes.clone(),
                },
            )
        }
        // let make = React.memo((~prop) => ...) / React.forwardRef((~prop) => ...)
        ExpressionDesc::Pexp_apply(apply_inner)
            if apply_inner.args.len() == 1
                && matches!(&apply_inner.args[0].0, ArgLabel::Nolabel) =>
        {
            let PexpApply { funct, args, .. } = &**apply_inner;
            let (_, _, inner_expr) = spelunk_for_fun_expression(arena, args[0].1);
            let funct_expr = arena.get_expr(*funct).clone();
            let has_forward_ref = is_forward_ref(arena, &funct_expr);
            (Some(funct_expr), has_forward_ref, inner_expr)
        }
        ExpressionDesc::Pexp_sequence(wrapper_expr_idx, inner_idx) => {
            let (binding_wrapper, has_forward_ref, inner_expr) =
                spelunk_for_fun_expression(arena, *inner_idx);
            let wrapper_expr_idx = *wrapper_expr_idx;
            let inner_expr_idx = arena.push_expr(inner_expr);
            (
                binding_wrapper,
                has_forward_ref,
                Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_sequence(
                        wrapper_expr_idx,
                        inner_expr_idx,
                    )),
                    pexp_loc: expr.pexp_loc,
                    pexp_attributes: expr.pexp_attributes.clone(),
                },
            )
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (inner_idx, _) = &**inner;
            spelunk_for_fun_expression(arena, *inner_idx)
        }
        _ => (None, false, expr),
    }
}

/// Transform a @react.component binding
fn transform_react_component_binding(
    binding: ValueBinding,
    rec_flag: RecFlag,
    pstr_loc: &Location,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> (Option<StructureItem>, ValueBinding, Option<ValueBinding>) {
    check_multiple_components(config, *pstr_loc);

    // Get function name and location from pattern
    let binding_pat = arena.get_pat(binding.pvb_pat).clone();
    let fn_name = get_fn_name(arena, config, &binding_pat, config.empty_loc);
    let fn_name_loc = get_fn_name_loc(&binding_pat);
    let original_binding_loc = binding.pvb_loc;

    // jsx_v4.ml:586-592: `modified_binding` (props must be labelled), then
    // `recursively_transform_named_args_for_make (modified_binding_old binding)`.
    if let Some(loc) = component_props_need_labelled_error_loc(arena, binding.pvb_expr, false) {
        set_fatal_error(config, loc, COMPONENT_PROPS_NEED_LABELLED_MSG);
    } else if let Some(loc) = component_call_needs_function_error_loc(arena, binding.pvb_expr) {
        set_fatal_error(config, loc, COMPONENT_CALL_NEEDS_FUNCTION_MSG);
    }
    let named_args_expr = modified_binding_old_expr(arena, binding.pvb_expr);

    // Check for sharedProps: @react.component(:sharedProps<T>)
    let core_type_of_attr = core_type_of_component(arena, binding.pvb_jsx_component.as_deref());
    let typ_vars_of_core_type: Vec<CoreType> = core_type_of_attr
        .as_ref()
        .map(|typ| typ_vars_of_core_type(arena, typ))
        .unwrap_or_default();

    // Detect component wrappers (e.g. React.memo / React.forwardRef) and get
    // the rebuilt internal expression used for the implementation binding.
    let (binding_wrapper_expr, has_forward_ref, inner_expr) =
        spelunk_for_fun_expression(arena, binding.pvb_expr);

    // Detect if function is async
    let is_async = is_async_function(arena, binding.pvb_expr);

    // Filter out @react.component attribute
    let filtered_attrs: Attributes = binding.pvb_attributes.clone();

    // Extract labeled arguments from the function (use inner expression to handle forwardRef)
    let (args, mut newtypes, _, jsx_warnings, named_args_error) =
        recursively_extract_named_args(arena, &named_args_expr);
    if let Some(constraint) = arena.value_constraint(binding.pvb_pat) {
        let mut constrained_newtypes = constraint
            .pvc_newtypes
            .iter()
            .cloned()
            .map(|name| (name, Attributes::new()))
            .collect::<Vec<_>>();
        constrained_newtypes.append(&mut newtypes);
        newtypes = constrained_newtypes;
    }
    warnings.extend(jsx_warnings);
    if let Some((loc, message)) = named_args_error {
        set_fatal_error(config, loc, message);
    }

    // Build named type list for props
    let named_type_list: Vec<NamedType> = args
        .iter()
        .filter_map(|arg| arg_to_type(arena, arg))
        .collect();

    // Create props type - either record or abstract with manifest (for sharedProps)
    let props_type = if let Some(manifest) = &core_type_of_attr {
        make_props_abstract_type(arena, "props", pstr_loc, manifest, &typ_vars_of_core_type)
    } else {
        make_props_record_type(
            arena,
            config,
            "props",
            pstr_loc,
            &named_type_list,
            has_forward_ref,
        )
    };

    // Build the internal expression pattern (use inner expression to handle forwardRef)
    let (patterns_with_label, patterns_with_nolabel, expression) =
        build_props_pattern_and_body(&inner_expr, &args, config, arena);

    // Create record pattern: {a, b, _}: props<'a, 'b>
    let record_pattern = if patterns_with_label.is_empty() {
        Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_any),
            ppat_loc: empty_loc(),
            ppat_attributes: Attributes::new(),
        }
    } else {
        Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_record(Box::new((
                patterns_with_label,
                ClosedFlag::Open,
                None,
            )))),
            ppat_loc: empty_loc(),
            ppat_attributes: Attributes::new(),
        }
    };

    // Constrain pattern with props type
    // For sharedProps, use Ptyp_any as type params; otherwise use named_type_list
    let props_type_params: Vec<CoreType> = if core_type_of_attr.is_some() {
        // For sharedProps, use empty params or single Ptyp_any if typ_vars exist
        if typ_vars_of_core_type.is_empty() {
            vec![]
        } else {
            vec![CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
                ptyp_loc: empty_loc(),
                ptyp_attributes: Attributes::new(),
            }]
        }
    } else {
        // jsx_v4.ml:788-792.
        named_type_list
            .iter()
            .filter_map(|nt| make_props_type_param(arena, nt, true, has_forward_ref))
            .collect()
    };

    let props_str_idx = arena.intern_string("props");
    let props_lid_idx = arena.push_longident(Longident::Lident(props_str_idx));
    let props_type_params_idx: Vec<_> = props_type_params
        .iter()
        .map(|ct| arena.push_core_type(ct.clone()))
        .collect();
    let props_constr = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Loc {
                txt: props_lid_idx,
                loc: config.empty_loc,
            },
            props_type_params_idx,
        )))),
        ptyp_loc: config.empty_loc,
        ptyp_attributes: Attributes::new(),
    };

    let record_pattern_idx = arena.push_pat(record_pattern);
    let props_constr_idx = arena.push_core_type(props_constr);
    let constrained_pattern = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
            record_pattern_idx,
            props_constr_idx,
        )))),
        ppat_loc: empty_loc(),
        ppat_attributes: Attributes::new(),
    };

    // jsx_v4.ml:754-790: `(props, ...nolabel_params) => expression`, where a
    // `ref` variable parameter is constrained to `Stdlib.Nullable.t<'ref>`.
    let nolabel_params: Vec<Pattern> = patterns_with_nolabel
        .into_iter()
        .map(|pattern| {
            let is_ref_var = matches!(
                &*pattern.ppat_desc,
                PatternDesc::Ppat_var(name) if arena.get_string(name.txt) == "ref"
            );
            if !is_ref_var {
                return pattern;
            }
            // `ref_type Location.none`.
            let ref_type_var = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Borrowed("ref")))),
                ptyp_loc: empty_loc(),
                ptyp_attributes: Attributes::new(),
            };
            let js_idx = arena.intern_string("Stdlib");
            let nullable_idx = arena.intern_string("Nullable");
            let t_idx = arena.intern_string("t");
            let js_nullable_t_lid = arena.push_longident(Longident::Ldot(
                Box::new(Longident::Ldot(
                    Box::new(Longident::Lident(js_idx)),
                    nullable_idx,
                )),
                t_idx,
            ));
            let ref_type_var_idx = arena.push_core_type(ref_type_var);
            let js_nullable_t = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                    Loc {
                        txt: js_nullable_t_lid,
                        loc: empty_loc(),
                    },
                    vec![ref_type_var_idx],
                )))),
                ptyp_loc: empty_loc(),
                ptyp_attributes: Attributes::new(),
            };
            let pattern_idx = arena.push_pat(pattern);
            let js_nullable_t_idx = arena.push_core_type(js_nullable_t);
            Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
                    pattern_idx,
                    js_nullable_t_idx,
                )))),
                ppat_loc: empty_loc(),
                ppat_attributes: Attributes::new(),
            }
        })
        .collect();

    let total_arity = 1 + nolabel_params.len();
    let expression_idx = arena.push_expr(expression);
    let constrained_pattern_idx = arena.push_pat(constrained_pattern);
    let arity = arena.push_arity(Some(total_arity as i32));
    if !nolabel_params.is_empty() {
        let unknown_arity = arena.push_arity(None);
        let mut params = vec![crate::parser::ast::FunParam {
            p_attrs: Attributes::new(),
            p_lbl: ArgLabel::Nolabel,
            p_default: None,
            p_pat: constrained_pattern_idx,
        }];
        for pattern in nolabel_params {
            params.push(crate::parser::ast::FunParam {
                p_attrs: Attributes::new(),
                p_lbl: ArgLabel::Nolabel,
                p_default: None,
                p_pat: arena.push_pat(pattern),
            });
        }
        arena.set_nary_fun_params(arity, params, unknown_arity);
    }
    // OCaml `Exp.fun_ ~async ~newtypes (props_param :: nolabel_params)` has no
    // location or attributes of its own.
    let inner_func_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: ArgLabel::Nolabel,
            default: None,
            lhs: constrained_pattern_idx,
            rhs: expression_idx,
            arity,
            is_async,
        }))),
        pexp_loc: empty_loc(),
        pexp_attributes: Attributes::new(),
    };

    // Current Parsetree stores locally abstract types directly on the n-ary
    // function rather than as nested Pexp_newtype wrappers.
    let func_expr = inner_func_expr;
    if let ExpressionDesc::Pexp_fun(fun) = &*func_expr.pexp_desc
        && !newtypes.is_empty()
    {
        arena.set_nary_fun_newtypes(fun.lhs, newtypes);
    }

    // Create the full module name for the component
    let full_module_name = make_module_name(config, &fn_name);

    // Create wrapper expression: let "ModuleName" = props => ...; "ModuleName"
    // For forwardRef, wrapper needs to handle ref too
    let full_expression = if full_module_name.is_empty() {
        func_expr.clone()
    } else {
        // For forwardRef without a file_name, add "ForwardRef$" prefix with nested modules in order
        // For forwardRef with file_name, use the regular full_module_name
        let binding_name = if has_forward_ref && config.file_name.is_empty() {
            let nested = &config.nested_modules;
            if nested.is_empty() {
                "ForwardRef".to_string()
            } else {
                format!("ForwardRef${}", nested.join("$"))
            }
        } else {
            full_module_name.clone()
        };

        // For sharedProps without type variables, the wrapper should NOT have a props type constraint
        // For sharedProps WITH type variables, or non-sharedProps, it should have the constraint
        let has_props_constraint = !named_type_list.is_empty()
            && (core_type_of_attr.is_none() || !typ_vars_of_core_type.is_empty());

        let binding_name_idx = arena.push_interned_string(&binding_name);
        let binding_expr_attrs = arena.get_expr(binding.pvb_expr).pexp_attributes.clone();
        let generated_wrapper_expr = make_props_wrapper_expr_with_ref(
            arena,
            &fn_name,
            rec_flag,
            config,
            has_props_constraint,
            has_forward_ref,
            is_async,
            binding_expr_attrs,
        );
        let inner_binding = ValueBinding {
            pvb_jsx_component: None,
            pvb_pat: arena.push_pat(Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                    txt: binding_name_idx,
                    loc: config.empty_loc,
                })),
                ppat_loc: config.empty_loc,
                ppat_attributes: Attributes::new(),
            }),
            // OCaml line 632: ~attrs:binding.pvb_expr.pexp_attributes
            pvb_expr: arena.push_expr(generated_wrapper_expr),
            pvb_attributes: Attributes::new(),
            pvb_loc: config.empty_loc,
        };

        let binding_str_idx = arena.push_interned_string(&binding_name);
        let binding_lid_idx = arena.push_longident(Longident::Lident(binding_str_idx));
        let ident_expr_idx = arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                txt: binding_lid_idx,
                loc: config.empty_loc,
            })),
            pexp_loc: *pstr_loc,
            pexp_attributes: Attributes::new(),
        });
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                RecFlag::Nonrecursive,
                vec![inner_binding],
                ident_expr_idx,
            )))),
            pexp_loc: empty_loc(),
            pexp_attributes: Attributes::new(),
        }
    };

    // Match jsx_v4.ml: coerce generated non-forwardRef wrappers through the
    // configured JSX module's component identity before restoring wrappers
    // such as React.memo. ForwardRef already performs the component coercion.
    let full_expression = if has_forward_ref {
        full_expression
    } else {
        jsx_component_expr(arena, config, config.empty_loc, full_expression)
    };

    let final_full_expression = if let Some(wrapper_expr) = binding_wrapper_expr {
        let wrapper_idx = arena.push_expr(wrapper_expr);
        let full_expression_idx = arena.push_expr(full_expression);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: wrapper_idx,
                args: vec![(ArgLabel::Nolabel, full_expression_idx)],
                partial: false,
                transformed_jsx: false,
            }))),
            // OCaml uses ghost location for the outer Pexp_apply wrapper.
            pexp_loc: empty_loc(),
            pexp_attributes: Attributes::new(),
        }
    } else {
        full_expression
    };

    // jsx_v4.ml keeps the implementation and public component wrapper as
    // separate bindings for both recursive and nonrecursive declarations. A
    // recursive self-reference therefore continues to denote the implementation
    // function while the following binding shadows it with the component value.
    let fn_name_idx = arena.push_interned_string(&fn_name);
    let transformed_binding = ValueBinding {
        pvb_jsx_component: None,
        pvb_pat: arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                txt: fn_name_idx,
                loc: empty_loc(),
            })),
            ppat_loc: empty_loc(),
            ppat_attributes: Attributes::new(),
        }),
        pvb_expr: arena.push_expr(func_expr),
        pvb_attributes: filtered_attrs.clone(),
        pvb_loc: config.empty_loc,
    };

    let new_binding = if !full_module_name.is_empty() {
        let fn_name_idx = arena.push_interned_string(&fn_name);
        Some(ValueBinding {
            pvb_jsx_component: None,
            pvb_pat: arena.push_pat(Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                    txt: fn_name_idx,
                    loc: fn_name_loc,
                })),
                ppat_loc: fn_name_loc,
                ppat_attributes: Attributes::new(),
            }),
            pvb_expr: arena.push_expr(final_full_expression),
            pvb_attributes: filtered_attrs,
            // jsx_v4.ml:419-424 `Vb.mk ~loc:binding_loc`: the component
            // binding's own location, not its `let rec ... and` group's.
            pvb_loc: original_binding_loc,
        })
    } else {
        None
    };

    (Some(props_type), transformed_binding, new_binding)
}

/// Transform a @react.componentWithProps binding
/// This is different from @react.component - it uses an existing props type
/// and doesn't create a new props type declaration
fn transform_react_component_with_props_binding(
    binding: ValueBinding,
    rec_flag: RecFlag,
    _pstr_loc: &Location,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
) -> (ValueBinding, Option<ValueBinding>) {
    // Get function name and location from pattern
    let binding_pat = arena.get_pat(binding.pvb_pat);
    let fn_name = get_fn_name(arena, config, binding_pat, binding_pat.ppat_loc);
    let _fn_name_loc = get_fn_name_loc(arena.get_pat(binding.pvb_pat));
    let internal_fn_name = format!("{}$Internal", fn_name);
    let full_module_name = make_module_name(config, &fn_name);

    if let Some(loc) = component_with_props_forward_ref_error_loc(arena, binding.pvb_expr) {
        set_fatal_error(config, loc, COMPONENT_WITH_PROPS_FORWARD_REF_MSG);
    }

    // Check if async
    let is_async = is_async_function(arena, binding.pvb_expr);

    // Filter out @react.componentWithProps attribute
    let filtered_attrs: Attributes = binding.pvb_attributes.clone();

    // Create props pattern based on the original function's pattern
    let binding_expr = arena.get_expr(binding.pvb_expr).clone();
    let props_pattern = make_with_props_pattern(arena, &binding_expr, config.empty_loc);

    // Create the applied expression: fnName(props) or fnName$Internal(props)
    let called_fn_name = match rec_flag {
        RecFlag::Recursive => internal_fn_name.clone(),
        RecFlag::Nonrecursive => fn_name.clone(),
    };

    let called_fn_str_idx = arena.push_interned_string(&called_fn_name);
    let called_fn_lid = arena.push_longident(Longident::Lident(called_fn_str_idx));
    let props_str_idx = arena.intern_string("props");
    let props_lid = arena.push_longident(Longident::Lident(props_str_idx));
    let funct_idx = arena.push_expr(Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
            txt: called_fn_lid,
            loc: config.empty_loc,
        })),
        pexp_loc: empty_loc(),
        pexp_attributes: Attributes::new(),
    });
    let applied_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: funct_idx,
            args: vec![(
                ArgLabel::Nolabel,
                arena.push_expr(Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                        txt: props_lid,
                        loc: config.empty_loc,
                    })),
                    pexp_loc: empty_loc(),
                    pexp_attributes: Attributes::new(),
                }),
            )],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: empty_loc(),
        pexp_attributes: Attributes::new(),
    };

    // Handle async wrapping if needed
    let applied_expr = if is_async {
        wrap_with_jsx_promise(arena, applied_expr)
    } else {
        applied_expr
    };

    // Wrap with React.element return type constraint
    let constrained_expr = constrain_jsx_return(arena, applied_expr, config);

    // Create wrapper expression: props => constrained_expr
    let constrained_expr_idx = arena.push_expr(constrained_expr);
    let wrapper_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: ArgLabel::Nolabel,
            default: None,
            lhs: arena.push_pat(props_pattern),
            rhs: constrained_expr_idx,
            arity: arena.push_arity(Some(1)),
            is_async: false,
        }))),
        pexp_loc: empty_loc(),
        pexp_attributes: arena.get_expr(binding.pvb_expr).pexp_attributes.clone(),
    };

    // Create let binding: let full_module_name = wrapper_expr in full_module_name
    let full_module_name_idx = arena.push_interned_string(&full_module_name);
    let full_module_name_idx2 = arena.push_interned_string(&full_module_name);
    let internal_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
            RecFlag::Nonrecursive,
            vec![ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: arena.push_pat(Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                        txt: full_module_name_idx,
                        loc: config.empty_loc,
                    })),
                    ppat_loc: empty_loc(),
                    ppat_attributes: Attributes::new(),
                }),
                pvb_expr: arena.push_expr(wrapper_expr),
                pvb_attributes: Attributes::new(),
                pvb_loc: empty_loc(),
            }],
            {
                let lid = arena.push_longident(Longident::Lident(full_module_name_idx2));
                arena.push_expr(Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                        txt: lid,
                        loc: config.empty_loc,
                    })),
                    pexp_loc: empty_loc(),
                    pexp_attributes: Attributes::new(),
                })
            },
        )))),
        pexp_loc: empty_loc(),
        pexp_attributes: Attributes::new(),
    };

    // jsx_v4.ml's componentWithProps path applies the same component identity
    // coercion to its generated wrapper.
    let internal_expr = jsx_component_expr(arena, config, config.empty_loc, internal_expr);

    // Create the new binding: `Vb.mk ~attrs (Pat.var {txt = fn_name; loc})`
    // (jsx_v4.ml:872-874) gives only the name the `empty_loc` location.
    let fn_name_idx = arena.push_interned_string(&fn_name);
    let new_binding = ValueBinding {
        pvb_jsx_component: None,
        pvb_pat: arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                txt: fn_name_idx,
                loc: config.empty_loc,
            })),
            ppat_loc: empty_loc(),
            ppat_attributes: Attributes::new(),
        }),
        pvb_expr: arena.push_expr(internal_expr),
        pvb_attributes: filtered_attrs.clone(),
        pvb_loc: empty_loc(),
    };

    // Handle recursive vs non-recursive
    match rec_flag {
        RecFlag::Recursive => {
            // For recursive: modify original binding to be internal, add new binding
            let internal_fn_name_idx = arena.push_string(internal_fn_name);
            let original_expr = arena.get_expr(binding.pvb_expr).clone();
            let transformed_original = transform_expression(original_expr, config, arena);
            let modified_binding = ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: arena.push_pat(Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                        txt: internal_fn_name_idx,
                        loc: empty_loc(),
                    })),
                    ppat_loc: empty_loc(),
                    ppat_attributes: Attributes::new(),
                }),
                pvb_expr: arena.push_expr(transformed_original),
                pvb_attributes: filtered_attrs,
                pvb_loc: binding.pvb_loc,
            };
            (modified_binding, Some(new_binding))
        }
        RecFlag::Nonrecursive => {
            // For non-recursive: wrap the function body with React.element constraint
            let transformed_expr =
                transform_expression(arena.get_expr(binding.pvb_expr).clone(), config, arena);
            let constrained_expr =
                wrap_function_body_with_constraint(arena, transformed_expr, config);
            // OCaml line 905-909: clear pexp_attributes (they were moved to wrapper_expr)
            let constrained_expr = Expression {
                pexp_attributes: Attributes::new(),
                ..constrained_expr
            };
            let modified_binding = ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: binding.pvb_pat,
                pvb_expr: arena.push_expr(constrained_expr),
                pvb_attributes: filtered_attrs,
                pvb_loc: binding.pvb_loc,
            };
            (modified_binding, Some(new_binding))
        }
    }
}

/// Wrap the innermost body of a function expression with constrain_jsx_return
fn wrap_function_body_with_constraint(
    arena: &mut ParseArena,
    expr: Expression,
    config: &JsxConfig,
) -> Expression {
    match *expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun {
                arg_label,
                default,
                lhs,
                rhs,
                arity,
                is_async,
            } = *inner;
            // Recursively wrap the body
            let rhs_expr = arena.get_expr(rhs).clone();
            let wrapped_rhs = wrap_function_body_with_constraint(arena, rhs_expr, config);
            let wrapped_rhs_idx = arena.push_expr(wrapped_rhs);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label,
                    default,
                    lhs,
                    rhs: wrapped_rhs_idx,
                    arity,
                    is_async,
                }))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes,
            }
        }
        _ => {
            // This is the innermost body - wrap it with React.element constraint
            constrain_jsx_return(arena, expr, config)
        }
    }
}

/// Create props pattern for componentWithProps based on the original function's pattern
fn make_with_props_pattern(arena: &mut ParseArena, expr: &Expression, loc: Location) -> Pattern {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun { ref lhs, .. } = **inner;
            let lhs = arena.get_pat(*lhs);
            match &*lhs.ppat_desc {
                PatternDesc::Ppat_constraint(inner) => {
                    let (_, ref typ_idx) = **inner;
                    let has_props_constraint_args = {
                        let typ = arena.get_core_type(*typ_idx);
                        match &*typ.ptyp_desc {
                            CoreTypeDesc::Ptyp_constr(inner)
                                if arena.is_lident(inner.0.txt, "props") =>
                            {
                                Some(!inner.1.is_empty())
                            }
                            _ => None,
                        }
                    };

                    match has_props_constraint_args {
                        Some(has_args) => {
                            let props_str_idx = arena.intern_string("props");
                            let props_lid = arena.push_longident(Longident::Lident(props_str_idx));
                            let inner_pat_name = arena.intern_string("props");
                            let inner_pat_idx = arena.push_pat(Pattern {
                                ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                                    txt: inner_pat_name,
                                    loc,
                                })),
                                ppat_loc: empty_loc(),
                                ppat_attributes: Attributes::new(),
                            });
                            let props_type_args = if has_args {
                                let any_type_idx = arena.push_core_type(CoreType {
                                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
                                    ptyp_loc: empty_loc(),
                                    ptyp_attributes: Attributes::new(),
                                });
                                vec![any_type_idx]
                            } else {
                                vec![]
                            };
                            let props_type_idx = arena.push_core_type(CoreType {
                                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                                    Loc {
                                        txt: props_lid,
                                        loc,
                                    },
                                    props_type_args,
                                )))),
                                ptyp_loc: empty_loc(),
                                ptyp_attributes: Attributes::new(),
                            });
                            Pattern {
                                ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
                                    inner_pat_idx,
                                    props_type_idx,
                                )))),
                                ppat_loc: empty_loc(),
                                ppat_attributes: Attributes::new(),
                            }
                        }
                        None => simple_props_pattern(arena, loc),
                    }
                }
                _ => simple_props_pattern(arena, loc),
            }
        }
        _ => simple_props_pattern(arena, loc),
    }
}

fn simple_props_pattern(arena: &mut ParseArena, loc: Location) -> Pattern {
    let props_str_idx = arena.intern_string("props");
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
            txt: props_str_idx,
            loc,
        })),
        ppat_loc: empty_loc(),
        ppat_attributes: Attributes::new(),
    }
}

/// Wrap expression with Jsx.promise for async components
fn wrap_with_jsx_promise(arena: &mut ParseArena, expr: Expression) -> Expression {
    let jsx_idx = arena.intern_string("Jsx");
    let promise_idx = arena.intern_string("promise");
    let promise_lid = arena.push_longident(Longident::Ldot(
        Box::new(Longident::Lident(jsx_idx)),
        promise_idx,
    ));
    let funct_idx = arena.push_expr(Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
            txt: promise_lid,
            loc: empty_loc(),
        })),
        pexp_loc: empty_loc(),
        pexp_attributes: Attributes::new(),
    });
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: funct_idx,
            args: vec![(ArgLabel::Nolabel, arena.push_expr(expr))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: empty_loc(),
        pexp_attributes: Attributes::new(),
    }
}

/// Check if expression is an async function
fn is_async_function(arena: &ParseArena, expr_idx: ExprIdx) -> bool {
    let expr = arena.get_expr(expr_idx);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun { ref is_async, .. } = **inner;
            *is_async
        }
        ExpressionDesc::Pexp_braces(braces) => is_async_function(arena, braces.expr),
        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref inner_idx, _) = **inner;
            is_async_function(arena, *inner_idx)
        }
        _ => false,
    }
}

/// Create wrapper expression with forwardRef support: (props, ref) => fnName(props, ref)
/// expr_attrs: the original expression's attributes (e.g., @directive) to put on the outer Pexp_fun
/// For recursive components, calls fn_name$Internal instead of fn_name
fn make_props_wrapper_expr_with_ref(
    arena: &mut ParseArena,
    fn_name: &str,
    rec_flag: RecFlag,
    _config: &JsxConfig,
    has_props: bool,
    has_forward_ref: bool,
    is_async: bool,
    expr_attrs: Attributes,
) -> Expression {
    let props_str_idx_pat = arena.intern_string("props");
    let props_pattern = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
            txt: props_str_idx_pat,
            loc: empty_loc(),
        })),
        ppat_loc: empty_loc(),
        ppat_attributes: Attributes::new(),
    };

    // Only constrain with props<_> if there are props
    let final_pattern = if has_props {
        let props_str_idx = arena.intern_string("props");
        let any_type_idx = arena.push_core_type(CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
            ptyp_loc: empty_loc(),
            ptyp_attributes: Attributes::new(),
        });
        let props_type = CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                Loc {
                    txt: arena.push_longident(Longident::Lident(props_str_idx)),
                    loc: empty_loc(),
                },
                vec![any_type_idx],
            )))),
            ptyp_loc: empty_loc(),
            ptyp_attributes: Attributes::new(),
        };
        let props_pattern_idx = arena.push_pat(props_pattern);
        let props_type_idx = arena.push_core_type(props_type);
        Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
                props_pattern_idx,
                props_type_idx,
            )))),
            ppat_loc: empty_loc(),
            ppat_attributes: Attributes::new(),
        }
    } else {
        props_pattern
    };

    // Build arguments for the apply expression
    let props_str_idx2 = arena.intern_string("props");
    let props_lid2 = arena.push_longident(Longident::Lident(props_str_idx2));
    let mut apply_args = vec![(
        ArgLabel::Nolabel,
        arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                txt: props_lid2,
                loc: empty_loc(),
            })),
            pexp_loc: empty_loc(),
            pexp_attributes: Attributes::new(),
        }),
    )];

    // For forwardRef, add ref argument
    if has_forward_ref {
        let ref_str_idx = arena.intern_string("ref");
        let ref_lid = arena.push_longident(Longident::Lident(ref_str_idx));
        apply_args.push((
            ArgLabel::Nolabel,
            arena.push_expr(Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                    txt: ref_lid,
                    loc: empty_loc(),
                })),
                pexp_loc: empty_loc(),
                pexp_attributes: Attributes::new(),
            }),
        ));
    }

    // The implementation binding keeps `fn_name` for recursive components too;
    // the following public wrapper binding shadows it.
    let _ = rec_flag;
    let fn_str_idx2 = arena.push_interned_string(fn_name);
    let fn_lid = arena.push_longident(Longident::Lident(fn_str_idx2));
    let funct_idx = arena.push_expr(Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
            txt: fn_lid,
            loc: empty_loc(),
        })),
        pexp_loc: empty_loc(),
        pexp_attributes: Attributes::new(),
    });
    let apply_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: funct_idx,
            args: apply_args,
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: empty_loc(),
        pexp_attributes: Attributes::new(),
    };

    // Wrap with Jsx.promise for async components
    let apply_expr = if is_async {
        wrap_with_jsx_promise(arena, apply_expr)
    } else {
        apply_expr
    };

    let total_arity = if has_forward_ref { 2 } else { 1 };

    // For forwardRef, wrap with an additional ref parameter
    let inner_expr = if has_forward_ref {
        let ref_str_idx_pat = arena.intern_string("ref");
        let ref_pattern = Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                txt: ref_str_idx_pat,
                loc: empty_loc(),
            })),
            ppat_loc: empty_loc(),
            ppat_attributes: Attributes::new(),
        };
        let apply_expr_idx = arena.push_expr(apply_expr);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label: ArgLabel::Nolabel,
                default: None,
                lhs: arena.push_pat(ref_pattern),
                rhs: apply_expr_idx,
                arity: arena.push_arity(None),
                is_async: false,
            }))),
            pexp_loc: empty_loc(),
            pexp_attributes: Attributes::new(),
        }
    } else {
        apply_expr
    };

    // The wrapper expression does NOT have is_async (OCaml line 632 uses Exp.fun_ without ~async)
    // The is_async parameter is only used for wrapping with Jsx.promise
    // OCaml line 632: ~attrs:binding.pvb_expr.pexp_attributes
    let inner_expr_idx = arena.push_expr(inner_expr);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: ArgLabel::Nolabel,
            default: None,
            lhs: arena.push_pat(final_pattern),
            rhs: inner_expr_idx,
            arity: arena.push_arity(Some(total_arity)),
            is_async: false,
        }))),
        pexp_loc: empty_loc(),
        pexp_attributes: expr_attrs,
    }
}

/// Strip Ppat_constraint from a pattern, EXCEPT for Ptyp_package constraints (first-class modules)
/// Matches OCaml's strip_constraint_unpack
fn strip_pattern_constraint(arena: &ParseArena, pat: &Pattern) -> Pattern {
    match &*pat.ppat_desc {
        PatternDesc::Ppat_constraint(inner) => {
            let (ref inner_idx, ref core_type_idx) = **inner;
            let core_type = arena.get_core_type(*core_type_idx);
            // Keep first-class module constraints (Ptyp_package)
            if matches!(*core_type.ptyp_desc, CoreTypeDesc::Ptyp_package(..)) {
                pat.clone()
            } else {
                // Recursively strip other constraints
                let inner_pat = arena.get_pat(*inner_idx);
                strip_pattern_constraint(arena, inner_pat)
            }
        }
        _ => pat.clone(),
    }
}

/// The parameters OCaml `returned_expression` (jsx_v4.ml:677-752) collects from
/// the component function.
#[derive(Default)]
struct ReturnedParams {
    /// Labelled/optional parameters, in source order: label, pattern, default.
    with_label: Vec<(ArgLabel, Pattern, bool)>,
    /// Unlabelled variable parameters (`ref`, ...), in source order.
    with_nolabel: Vec<Pattern>,
}

/// OCaml `returned_expression`/`returned_expression_params`: walk the
/// component function's parameters until a `()` parameter, collecting the
/// labelled ones and the unlabelled variables, and return the remaining body
/// (a function of the parameters after `()`, if any).
fn returned_expression(
    arena: &mut ParseArena,
    expr: &Expression,
    params_acc: &mut ReturnedParams,
) -> Expression {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_constraint(inner) => {
            let inner = arena.get_expr(inner.0).clone();
            returned_expression(arena, &inner, params_acc)
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let body = arena.get_expr(inner.1).clone();
            returned_expression(arena, &body, params_acc)
        }
        ExpressionDesc::Pexp_fun(fun) => {
            let params = arena.nary_fun_params(fun).into_owned();
            let body_idx = arena.nary_fun_body(fun);
            for (index, param) in params.iter().enumerate() {
                let pattern = arena.get_pat(param.p_pat).clone();
                if matches!(
                    &*pattern.ppat_desc,
                    PatternDesc::Ppat_construct(lid, _) if arena.is_lident(lid.txt, "()")
                ) {
                    let rest = &params[index + 1..];
                    if rest.is_empty() {
                        return arena.get_expr(body_idx).clone();
                    }
                    // `Ast_helper.Exp.fun_ rest body`.
                    let arity = arena.push_arity(Some(rest.len() as i32));
                    let unknown_arity = arena.push_arity(None);
                    arena.set_nary_fun_params(arity, rest.to_vec(), unknown_arity);
                    return Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                            arg_label: rest[0].p_lbl,
                            default: rest[0].p_default,
                            lhs: rest[0].p_pat,
                            rhs: body_idx,
                            arity,
                            is_async: false,
                        }))),
                        pexp_loc: empty_loc(),
                        pexp_attributes: Attributes::new(),
                    };
                }
                if is_labelled(&param.p_lbl) || is_optional(&param.p_lbl) {
                    params_acc
                        .with_label
                        .push((param.p_lbl, pattern, param.p_default.is_some()));
                } else if pattern_is_plain_name_or_constraint(&pattern, arena) {
                    params_acc.with_nolabel.push(pattern);
                }
            }
            let body = arena.get_expr(body_idx).clone();
            returned_expression(arena, &body, params_acc)
        }
        _ => expr.clone(),
    }
}

/// Build the props record pattern fields, the unlabelled parameters and the
/// body of the component implementation (jsx_v4.ml:677-790).
fn build_props_pattern_and_body(
    expr: &Expression,
    args: &[ExtractedArg],
    config: &mut JsxConfig,
    arena: &mut ParseArena,
) -> (Vec<PatternRecordField>, Vec<Pattern>, Expression) {
    let mut params = ReturnedParams::default();
    let body = returned_expression(arena, expr, &mut params);

    let mut patterns = vec![];
    for (arg_label, pattern, has_default) in &params.with_label {
        let label = get_label(arena, arg_label);

        // OCaml strips constraint from pattern when building record field
        let base_pat = strip_pattern_constraint(arena, pattern);

        // For args with a default value, OCaml replaces the entire pattern
        // with a fresh `Pat.var "__<label>"` (jsx_v4.ml `pattern_with_safe_label`).
        // This avoids ident-name collisions and, critically, keeps the props
        // record field bound to `__<label>` regardless of any `~name as alias`
        // renaming. The original pattern (alias and all) is bound later via
        // `add_default_value_matches`.
        let mut pat = if *has_default {
            let prefixed_str_idx = arena.push_string(format!("__{}", label));
            Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                    txt: prefixed_str_idx,
                    loc: base_pat.ppat_loc,
                })),
                // OCaml compiler/syntax/src/jsx_v4.ml:693-700 calls Pat.var
                // without an outer ~loc, so Ast_helper.Pat.var uses
                // Location.none for ppat_loc while the inner variable loc
                // comes from Location.mkloc.
                ppat_loc: empty_loc(),
                ppat_attributes: Attributes::new(),
            }
        } else {
            base_pat
        };

        // Preserve original pattern attributes (OCaml does: pattern_with_safe_label with ppat_attributes = pattern.ppat_attributes)
        pat.ppat_attributes = pattern.ppat_attributes.clone();

        let label_str_idx = arena.push_interned_string(&label);
        patterns.push(PatternRecordField {
            lid: Loc {
                txt: arena.push_longident(Longident::Lident(label_str_idx)),
                loc: pattern.ppat_loc,
            },
            pat: arena.push_pat(pat),
            opt: is_optional(arg_label),
        });
    }

    let transformed_body = transform_expression(body, config, arena);

    // Constrain return type to React.element
    let constrained_body = constrain_jsx_return(arena, transformed_body, config);

    // Add default value handling
    let final_body = add_default_value_matches(arena, constrained_body, args);

    (patterns, params.with_nolabel, final_body)
}

/// Add pattern matching for optional props with default values
fn add_default_value_matches(
    arena: &mut ParseArena,
    mut expr: Expression,
    args: &[ExtractedArg],
) -> Expression {
    for arg in args.iter().rev() {
        if let Some(default) = &arg.default {
            // Mirrors OCaml jsx_v4.ml's vb_match (post #8296). Emits two
            // nested lets:
            //   let __<label>_value = match __<label> { Some(v) => v | None => default }
            //   let <pattern> = __<label>_value
            //   <expr>
            // The intermediate `__X_value` binding lets first-class module
            // unpack patterns survive on the inner let.
            let label_name = get_label(arena, &arg.label);
            let prefixed = format!("__{}", label_name);
            let resolved_name = format!("__{}_value", label_name);

            let prefixed_str_idx = arena.push_string(prefixed);
            let some_str_idx = arena.intern_string("Some");
            let none_str_idx = arena.intern_string("None");
            let label_name_str_idx = arena.push_interned_string(&label_name);
            let label_name_str_idx2 = arena.push_interned_string(&label_name);
            let scrutinee_lid = arena.push_longident(Longident::Lident(prefixed_str_idx));
            let match_scrutinee_idx = arena.push_expr(Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                    txt: scrutinee_lid,
                    loc: empty_loc(),
                })),
                pexp_loc: empty_loc(),
                pexp_attributes: Attributes::new(),
            });
            let some_inner_pat_idx = arena.push_pat(Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                    txt: label_name_str_idx2,
                    loc: empty_loc(),
                })),
                ppat_loc: empty_loc(),
                ppat_attributes: Attributes::new(),
            });
            let some_lid = arena.push_longident(Longident::Lident(some_str_idx));
            let label_name_lid = arena.push_longident(Longident::Lident(label_name_str_idx));
            let none_lid = arena.push_longident(Longident::Lident(none_str_idx));
            let match_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_match(Box::new((
                    match_scrutinee_idx,
                    vec![
                        Case {
                            pc_bar: None,
                            pc_lhs: arena.push_pat(Pattern {
                                ppat_desc: Box::new(PatternDesc::Ppat_construct(
                                    Loc {
                                        txt: some_lid,
                                        loc: empty_loc(),
                                    },
                                    ctor_args(vec![some_inner_pat_idx], empty_loc()),
                                )),
                                ppat_loc: empty_loc(),
                                ppat_attributes: Attributes::new(),
                            }),
                            pc_guard: None,
                            pc_rhs: arena.push_expr(Expression {
                                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                                    txt: label_name_lid,
                                    loc: empty_loc(),
                                })),
                                pexp_loc: empty_loc(),
                                pexp_attributes: Attributes::new(),
                            }),
                        },
                        Case {
                            pc_bar: None,
                            pc_lhs: arena.push_pat(Pattern {
                                ppat_desc: Box::new(PatternDesc::Ppat_construct(
                                    Loc {
                                        txt: none_lid,
                                        loc: empty_loc(),
                                    },
                                    ctor_args(Vec::new(), empty_loc()),
                                )),
                                ppat_loc: empty_loc(),
                                ppat_attributes: Attributes::new(),
                            }),
                            pc_guard: None,
                            pc_rhs: arena.push_expr(default.clone()),
                        },
                    ],
                )))),
                pexp_loc: empty_loc(),
                pexp_attributes: Attributes::new(),
            };

            // Outer binding: let __<label>_value = match __<label> { ... }
            let resolved_str_idx = arena.push_string(resolved_name.clone());
            let value_binding = ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: arena.push_pat(Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_var(Loc {
                        txt: resolved_str_idx,
                        loc: arg.loc,
                    })),
                    ppat_loc: empty_loc(),
                    ppat_attributes: Attributes::new(),
                }),
                pvb_expr: arena.push_expr(match_expr),
                pvb_attributes: Attributes::new(),
                pvb_loc: empty_loc(),
            };

            // Inner binding: let <pattern> = __<label>_value
            let resolved_lid_str_idx = arena.intern_string(&resolved_name);
            let resolved_lid = arena.push_longident(Longident::Lident(resolved_lid_str_idx));
            let resolved_ident_idx = arena.push_expr(Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                    txt: resolved_lid,
                    loc: empty_loc(),
                })),
                pexp_loc: empty_loc(),
                pexp_attributes: Attributes::new(),
            });
            let inner_binding = ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: arena.push_pat(arg.pattern.clone()),
                pvb_expr: resolved_ident_idx,
                pvb_attributes: Attributes::new(),
                pvb_loc: empty_loc(),
            };

            let expr_idx = arena.push_expr(expr);
            let inner_let = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                    RecFlag::Nonrecursive,
                    vec![inner_binding],
                    expr_idx,
                )))),
                pexp_loc: empty_loc(),
                pexp_attributes: Attributes::new(),
            };
            let inner_let_idx = arena.push_expr(inner_let);
            expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                    RecFlag::Nonrecursive,
                    vec![value_binding],
                    inner_let_idx,
                )))),
                pexp_loc: empty_loc(),
                pexp_attributes: Attributes::new(),
            };
        }
    }
    expr
}

// ============================================================================
// Signature Item Transformation
// ============================================================================

fn transform_signature_item_multi(
    item: SignatureItem,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> Vec<SignatureItem> {
    // Check for @@jsxConfig attribute
    if let SignatureItemDesc::Psig_attribute(attr) = &*item.psig_desc {
        if arena.get_string(attr.0.txt) == "jsxConfig" {
            update_config_from_attribute(arena, attr, config);
        }
        return vec![item];
    }

    // Only transform if version is 4
    if config.version != 4 {
        return vec![item];
    }

    // Handle Psig_value with potential @react.component
    if let SignatureItemDesc::Psig_value(vd) = &*item.psig_desc {
        if reject_leftover_component_attrs(arena, &vd.pval_attributes, config) {
            return vec![item];
        }
        // `@react.componentWithProps` on a signature item has always been
        // left alone.
        if let Some(JsxComponentKind::Labelled(_)) =
            vd.pval_jsx_component.as_deref().map(|c| &c.pjc_kind)
        {
            return transform_react_component_sig((**vd).clone(), &item.psig_loc, config, arena);
        }
    }

    vec![SignatureItem {
        psig_desc: Box::new(transform_signature_item_desc(
            *item.psig_desc,
            config,
            arena,
            warnings,
        )),
        psig_loc: item.psig_loc,
    }]
}

fn transform_react_component_sig(
    vd: ValueDescription,
    loc: &Location,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
) -> Vec<SignatureItem> {
    check_multiple_components(config, *loc);
    if let Some(loc) = string_int_attribute_loc_in_core_type(arena, &vd.pval_type) {
        set_fatal_error(config, loc, STRING_INT_ATTR_UNSUPPORTED_MSG);
    }

    // Check for sharedProps: @react.component(:sharedProps<T>)
    let core_type_of_attr = core_type_of_component(arena, vd.pval_jsx_component.as_deref());
    let typ_vars_of_core_type: Vec<CoreType> = core_type_of_attr
        .as_ref()
        .map(|typ| typ_vars_of_core_type(arena, typ))
        .unwrap_or_default();

    // Extract prop types from the function type
    let prop_types = collect_prop_types(arena, arena.get_core_type(vd.pval_type));
    let named_type_list: Vec<NamedType> = prop_types
        .into_iter()
        .filter_map(|(label, attrs, loc, typ)| {
            let label_str = get_label(arena, &label);
            if label_str.is_empty() {
                None
            } else {
                Some(NamedType {
                    is_optional: is_optional(&label),
                    label: label_str,
                    attrs,
                    loc,
                    interior_type: arena.get_core_type(typ).clone(),
                })
            }
        })
        .collect();

    // Create props type - either record or abstract with manifest (for sharedProps)
    // For sharedProps signatures, don't add the live/jsxComponentProps attributes
    let props_type = if let Some(manifest) = &core_type_of_attr {
        // sharedProps signature: no extra attributes
        make_props_abstract_type_sig(arena, "props", loc, manifest, &typ_vars_of_core_type)
    } else {
        make_props_record_type_sig(arena, config, "props", loc, &named_type_list)
    };

    // Filter attributes
    let filtered_attrs: Attributes = vd.pval_attributes.clone();

    // Create props type ref with appropriate type params
    // For sharedProps without type variables: no type args
    // For sharedProps with type variables: use Ptyp_any for each type var
    // For non-sharedProps: use the interior types
    let props_type_params: Vec<CoreTypeIdx> = if core_type_of_attr.is_some() {
        if typ_vars_of_core_type.is_empty() {
            // sharedProps without type vars: no type arguments
            vec![]
        } else {
            // sharedProps with type vars: use Ptyp_any for each type var
            typ_vars_of_core_type
                .iter()
                .map(|_| {
                    arena.push_core_type(CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
                        ptyp_loc: empty_loc(),
                        ptyp_attributes: Attributes::new(),
                    })
                })
                .collect()
        }
    } else {
        // jsx_v4.ml:986 / 1080: `make_props_type_params named_type_list`.
        named_type_list
            .iter()
            .filter_map(|nt| make_props_type_param(arena, nt, false, false))
            .collect::<Vec<_>>()
            .into_iter()
            .map(|ct| arena.push_core_type(ct))
            .collect()
    };

    // Create new value description with component type
    // OCaml: Typ.constr (Location.mkloc (Lident "props") psig_loc) params
    // Typ.constr without ~loc uses Location.none for ptyp_loc
    let props_str_idx = arena.intern_string("props");
    let props_type_ref = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Loc {
                txt: arena.push_longident(Longident::Lident(props_str_idx)),
                loc: *loc,
            }, // longident uses psig_loc
            props_type_params,
        )))),
        ptyp_loc: empty_loc(), // OCaml: Typ.constr without ~loc defaults to Location.none
        ptyp_attributes: Attributes::new(),
    };

    // OCaml: {pval_type with ptyp_desc = new_external_type}
    // This preserves pval_type's original ptyp_loc
    let react_str_idx = arena.intern_string("React");
    let component_str_idx = arena.intern_string("component");
    let props_type_ref_idx = arena.push_core_type(props_type_ref);
    let component_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Loc {
                txt: arena.push_longident(Longident::Ldot(
                    Box::new(Longident::Lident(react_str_idx)),
                    component_str_idx,
                )),
                loc: *loc, // OCaml: {loc = psig_loc; txt = ...}
            },
            vec![props_type_ref_idx],
        )))),
        ptyp_loc: arena.get_core_type(vd.pval_type).ptyp_loc, // OCaml: {pval_type with ...} preserves ptyp_loc
        ptyp_attributes: Attributes::new(),
    };

    let new_vd = ValueDescription {
        pval_jsx_component: None,
        pval_name: vd.pval_name,
        pval_type: arena.push_core_type(component_type),
        pval_prim: vd.pval_prim,
        pval_attributes: filtered_attrs,
        pval_loc: vd.pval_loc,
    };

    vec![
        props_type,
        SignatureItem {
            psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(new_vd))),
            psig_loc: *loc,
        },
    ]
}

/// Transform @react.component on external declaration
fn transform_react_component_external(
    vd: ValueDescription,
    loc: &Location,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    check_multiple_components(config, *loc);
    if let Some(loc) = string_int_attribute_loc_in_core_type(arena, &vd.pval_type) {
        set_fatal_error(config, loc, STRING_INT_ATTR_UNSUPPORTED_MSG);
    }

    // Check for sharedProps: @react.component(:sharedProps<T>)
    let core_type_of_attr = core_type_of_component(arena, vd.pval_jsx_component.as_deref());
    let typ_vars_of_core_type: Vec<CoreType> = core_type_of_attr
        .as_ref()
        .map(|typ| typ_vars_of_core_type(arena, typ))
        .unwrap_or_default();

    // Extract prop types from the function type
    let prop_types = collect_prop_types(arena, arena.get_core_type(vd.pval_type));
    let named_type_list: Vec<NamedType> = prop_types
        .into_iter()
        .filter_map(|(label, attrs, loc, typ)| {
            let label_str = get_label(arena, &label);
            if label_str.is_empty() {
                None
            } else {
                Some(NamedType {
                    is_optional: is_optional(&label),
                    label: label_str,
                    attrs,
                    loc,
                    interior_type: arena.get_core_type(typ).clone(),
                })
            }
        })
        .collect();

    // Create props type - either record or abstract with manifest (for sharedProps)
    // For sharedProps externals, don't add the live/jsxComponentProps attributes
    let props_type = if let Some(manifest) = &core_type_of_attr {
        // sharedProps external: no extra attributes
        make_props_abstract_type(arena, "props", loc, manifest, &typ_vars_of_core_type)
    } else {
        // regular external: add live attribute
        make_props_record_type_with_live(arena, config, "props", loc, &named_type_list)
    };

    // Filter attributes (remove @react.component)
    let filtered_attrs: Attributes = vd.pval_attributes.clone();

    // Create props type ref with appropriate type params
    // For sharedProps without type variables: no type args
    // For sharedProps with type variables: use Ptyp_any for each type var
    // For non-sharedProps: use the interior types
    let props_type_params: Vec<CoreTypeIdx> = if core_type_of_attr.is_some() {
        if typ_vars_of_core_type.is_empty() {
            // sharedProps without type vars: no type arguments
            vec![]
        } else {
            // sharedProps with type vars: use Ptyp_any for each type var
            typ_vars_of_core_type
                .iter()
                .map(|_| {
                    arena.push_core_type(CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
                        ptyp_loc: empty_loc(),
                        ptyp_attributes: Attributes::new(),
                    })
                })
                .collect()
        }
    } else {
        // jsx_v4.ml:986 / 1080: `make_props_type_params named_type_list`.
        named_type_list
            .iter()
            .filter_map(|nt| make_props_type_param(arena, nt, false, false))
            .collect::<Vec<_>>()
            .into_iter()
            .map(|ct| arena.push_core_type(ct))
            .collect()
    };

    // OCaml uses the external's full location for the props type and its longident
    let props_str_idx = arena.intern_string("props");
    let props_type_ref = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Loc {
                txt: arena.push_longident(Longident::Lident(props_str_idx)),
                loc: *loc,
            },
            props_type_params,
        )))),
        ptyp_loc: *loc,
        ptyp_attributes: Attributes::new(),
    };

    // OCaml uses the original return type's location for the outer core_type,
    // and the external's full location for the longident
    let component_str_idx = arena.intern_string("component");
    let props_type_ref_idx = arena.push_core_type(props_type_ref);
    let component_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Loc {
                txt: module_access_name_with_idx(arena, config, component_str_idx),
                loc: *loc,
            },
            vec![props_type_ref_idx],
        )))),
        ptyp_loc: arena.get_core_type(vd.pval_type).ptyp_loc,
        ptyp_attributes: Attributes::new(),
    };

    let new_vd = ValueDescription {
        pval_jsx_component: None,
        pval_name: vd.pval_name,
        pval_type: arena.push_core_type(component_type),
        pval_prim: vd.pval_prim,
        pval_attributes: filtered_attrs,
        pval_loc: vd.pval_loc,
    };

    vec![
        props_type,
        StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(new_vd))),
            pstr_loc: *loc,
        },
    ]
}

/// Create props record type with @live attribute (for externals)
fn make_props_record_type_with_live(
    arena: &mut ParseArena,
    config: &mut JsxConfig,
    name: &str,
    loc: &Location,
    named_types: &[NamedType],
) -> StructureItem {
    set_duplicate_label_error(config, named_types);

    let label_decls: Vec<LabelDeclaration> = named_types
        .iter()
        .map(|nt| {
            // OCaml uses ghost location for the Ptyp_var inside label declarations
            let type_var = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(
                    safe_type_from_value(&nt.label),
                )))),
                ptyp_loc: empty_loc(),
                ptyp_attributes: Attributes::new(),
            };

            // Key prop is always optional in type declaration (OCaml: if label = "key" then ~optional:true)
            let is_optional = if nt.label == "key" {
                true
            } else {
                nt.is_optional
            };

            let label_idx = arena.push_interned_string(&nt.label);
            let typ_idx = arena.push_core_type(type_var);
            crate::ast_helper_type::field(
                arena,
                nt.loc,
                nt.attrs.clone(),
                MutableFlag::Immutable,
                is_optional,
                None,
                Loc {
                    txt: label_idx,
                    loc: nt.loc,
                },
                typ_idx,
            )
        })
        .collect();

    // Type parameters - these keep the real location (OCaml uses real locs for ptype_params)
    let type_params: Vec<(CoreTypeIdx, Variance)> = named_types
        .iter()
        .filter(|nt| nt.label != "key")
        .map(|nt| {
            let var = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(
                    safe_type_from_value(&nt.label),
                )))),
                ptyp_loc: nt.loc,
                ptyp_attributes: Attributes::new(),
            };
            (arena.push_core_type(var), Variance::Invariant)
        })
        .collect();

    // Create @res.jsxComponentProps and @live attributes
    let jsx_props_idx = arena.intern("res.jsxComponentProps");
    let live_idx = arena.intern("live");
    let jsx_props_attr = (
        Loc {
            txt: jsx_props_idx,
            loc: empty_loc(),
        },
        Payload::PStr(Box::default()),
    );
    let live_attr = (
        Loc {
            txt: live_idx,
            loc: empty_loc(),
        },
        Payload::PStr(Box::default()),
    );

    // OCaml uses ghost location for the generated props type structure_item
    let name_idx = arena.intern(name);
    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_type(Box::new((
            RecFlag::Nonrecursive,
            vec![TypeDeclaration {
                ptype_name: Loc {
                    txt: name_idx,
                    loc: *loc,
                },
                ptype_params: type_params,
                ptype_cstrs: vec![],
                ptype_kind: TypeKind::Ptype_record(label_decls),
                ptype_private: PrivateFlag::Public,
                ptype_manifest: None,
                ptype_origin: TypeDeclarationOrigin::Declared,
                ptype_attributes: Attributes::from_vec(vec![jsx_props_attr, live_attr]),
                ptype_loc: *loc,
            }],
        )))),
        pstr_loc: empty_loc(),
    }
}

/// Collect prop types from a function type
fn collect_prop_types(
    arena: &ParseArena,
    typ: &CoreType,
) -> Vec<(ArgLabel, Attributes, Location, CoreTypeIdx)> {
    let mut types = vec![];
    collect_prop_types_rec(arena, typ, &mut types);
    types
}

fn collect_prop_types_rec(
    arena: &ParseArena,
    typ: &CoreType,
    types: &mut Vec<(ArgLabel, Attributes, Location, CoreTypeIdx)>,
) {
    if let CoreTypeDesc::Ptyp_arrow(ptyp_inner) = &*typ.ptyp_desc {
        let (ref first_arg, ref ret_idx, ref arity) = **ptyp_inner;
        let ret = arena.get_core_type(*ret_idx);
        let ret_is_arrow = matches!(*ret.ptyp_desc, CoreTypeDesc::Ptyp_arrow(_));
        let args = arena.nary_arrow_args(first_arg, *arity);
        let last = args.len().saturating_sub(1);
        for (index, arg) in args.iter().enumerate() {
            // jsx_v4.ml skips fixed arguments (`Parg_fixed`).
            if arg.fixed.is_none() && (is_labelled(&arg.lbl) || is_optional(&arg.lbl)) {
                // jsx_v4.ml uses the final return location only for the last
                // argument of the final arrow group; all other arguments keep
                // their own type location.
                let loc = if index == last && !ret_is_arrow {
                    ret.ptyp_loc
                } else {
                    arena.get_core_type(arg.typ).ptyp_loc
                };
                types.push((arg.lbl, arg.attrs.clone(), loc, arg.typ));
            }
        }
        if ret_is_arrow {
            collect_prop_types_rec(arena, ret, types);
        }
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// jsx_common.ml `reject_leftover_component_attrs`: `Ast_helper` takes the
/// first `@react.component`, or failing that the first
/// `@react.componentWithProps`, into the binding's or description's
/// component node. One still among the attributes is a second annotation, or
/// one with a payload the node cannot hold; it stays an attribute so that
/// formatting keeps it, and the JSX transform rejects it here. Returns
/// whether it raised.
fn reject_leftover_component_attrs(
    arena: &ParseArena,
    attrs: &Attributes,
    config: &mut JsxConfig,
) -> bool {
    for attr in attrs.iter() {
        let name = arena.get_string(attr.0.txt);
        if !matches!(
            name,
            "react.component"
                | "jsx.component"
                | "react.componentWithProps"
                | "jsx.componentWithProps"
        ) {
            continue;
        }
        let message = if crate::ast_jsx_component::of_attribute(arena, attr).is_some() {
            "A definition can have only one JSX component annotation.".to_string()
        } else if matches!(name, "react.component" | "jsx.component") {
            format!("@{name} takes no payload, or the props type to share, as in @{name}(: props).")
        } else {
            format!("@{name} takes no payload.")
        };
        set_fatal_error(config, attr.0.loc, &message);
        return true;
    }
    false
}

fn check_multiple_components(config: &mut JsxConfig, loc: Location) {
    if config.has_component {
        set_fatal_error(config, loc, MULTIPLE_COMPONENT_DEFINITIONS_MSG);
    } else {
        config.has_component = true;
    }
}

fn set_fatal_error(config: &mut JsxConfig, loc: Location, message: &str) {
    set_fatal_error_with_style(
        config,
        loc,
        message,
        JsxPreprocessorMessageStyle::PrefixedLines,
    );
}

fn set_fatal_error_with_style(
    config: &mut JsxConfig,
    loc: Location,
    message: &str,
    message_style: JsxPreprocessorMessageStyle,
) {
    if config.fatal_error.is_none() {
        config.fatal_error = Some(JsxPreprocessorError {
            loc,
            message: message.to_string(),
            message_style,
        });
    }
}

/// The props type shared by `@react.component(: sharedProps<T>)`.
fn core_type_of_component(
    arena: &ParseArena,
    component: Option<&JsxComponent>,
) -> Option<CoreType> {
    match component?.pjc_kind {
        JsxComponentKind::Labelled(Some(typ)) => Some(arena.get_core_type(typ).clone()),
        JsxComponentKind::Labelled(None) | JsxComponentKind::WithProps => None,
    }
}

/// Extract type variables from a core type (for sharedProps<'a, 'b>)
fn typ_vars_of_core_type(arena: &ParseArena, typ: &CoreType) -> Vec<CoreType> {
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (_, ref args) = **inner;
            args.iter()
                .map(|t| arena.get_core_type(*t))
                .filter(|t| matches!(*t.ptyp_desc, CoreTypeDesc::Ptyp_var(_)))
                .cloned()
                .collect()
        }
        _ => vec![],
    }
}

/// Check if an expression is React.forwardRef
fn is_forward_ref(arena: &ParseArena, expr: &Expression) -> bool {
    if let ExpressionDesc::Pexp_ident(loc) = &*expr.pexp_desc {
        if let Longident::Ldot(base, field_idx) = arena.get_longident(loc.txt) {
            if let Longident::Lident(m_idx) = base.as_ref() {
                let m = arena.get_string(*m_idx);
                let field = arena.get_string(*field_idx);
                return m == "React" && field == "forwardRef";
            }
        }
    }
    false
}

/// `check_invalid_forward_ref` in OCaml `map_binding`'s
/// `@react.componentWithProps` case (jsx_v4.ml:814-836).
fn component_with_props_forward_ref_error_loc(
    arena: &ParseArena,
    expr_idx: ExprIdx,
) -> Option<Location> {
    let expr = arena.get_expr(expr_idx);
    let ExpressionDesc::Pexp_apply(apply) = &*expr.pexp_desc else {
        return None;
    };
    match apply.args.as_slice() {
        [(ArgLabel::Nolabel, func_expr)] if is_forward_ref(arena, arena.get_expr(apply.funct)) => {
            component_with_props_forward_ref_fun_error_loc(arena, *func_expr)
        }
        _ => None,
    }
}

fn component_with_props_forward_ref_fun_error_loc(
    arena: &ParseArena,
    expr_idx: ExprIdx,
) -> Option<Location> {
    let expr = arena.get_expr(expr_idx);
    let ExpressionDesc::Pexp_fun(fun) = &*expr.pexp_desc else {
        return None;
    };
    let has_labelled = arena
        .nary_fun_params(fun)
        .iter()
        .any(|param| !matches!(param.p_lbl, ArgLabel::Nolabel));
    if has_labelled {
        Some(expr.pexp_loc)
    } else {
        component_with_props_forward_ref_fun_error_loc(arena, arena.nary_fun_body(fun))
    }
}

/// The error of OCaml `modified_binding`'s `spelunk_for_fun_expression`
/// (jsx_v4.ml:428-483): only the first parameter of the component function is
/// inspected; an unlabelled one other than `()`/`_` is an error unless the
/// function is wrapped in an application (`React.forwardRef`, `React.memo`).
fn component_props_need_labelled_error_loc(
    arena: &ParseArena,
    expr_idx: ExprIdx,
    has_application: bool,
) -> Option<Location> {
    let expr = arena.get_expr(expr_idx);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_fun(fun) => {
            let params = arena.nary_fun_params(fun);
            let first = params.first()?;
            match first.p_lbl {
                ArgLabel::Labelled(_) | ArgLabel::Optional(_) => None,
                ArgLabel::Nolabel => {
                    let lhs = arena.get_pat(first.p_pat);
                    if pattern_is_unit_or_any(arena, lhs) || has_application {
                        None
                    } else {
                        Some(lhs.ppat_loc)
                    }
                }
            }
        }
        ExpressionDesc::Pexp_braces(braces) => {
            component_props_need_labelled_error_loc(arena, braces.expr, has_application)
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (_, body_idx) = &**inner;
            component_props_need_labelled_error_loc(arena, *body_idx, has_application)
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (_, _, body_idx) = &**inner;
            component_props_need_labelled_error_loc(arena, *body_idx, has_application)
        }
        ExpressionDesc::Pexp_apply(apply)
            if apply.args.len() == 1 && matches!(apply.args[0].0, ArgLabel::Nolabel) =>
        {
            component_props_need_labelled_error_loc(arena, apply.args[0].1, true)
        }
        ExpressionDesc::Pexp_sequence(_, inner_idx) => {
            component_props_need_labelled_error_loc(arena, *inner_idx, has_application)
        }
        _ => None,
    }
}

/// jsx_v4.ml `find_function_expression`: the final function through
/// expression wrappers. Applications are only followed when inspecting
/// component wrappers such as forwardRef and memo.
fn find_function_expression(
    arena: &ParseArena,
    expr_idx: ExprIdx,
    through_application: bool,
) -> Result<&Expression, &Expression> {
    let expr = arena.get_expr(expr_idx);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_fun(_) | ExpressionDesc::Pexp_newtype(_) => Ok(expr),
        ExpressionDesc::Pexp_braces(braces) => {
            find_function_expression(arena, braces.expr, through_application)
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            find_function_expression(arena, inner.0, through_application)
        }
        ExpressionDesc::Pexp_let(inner) => {
            find_function_expression(arena, inner.2, through_application)
        }
        ExpressionDesc::Pexp_sequence(_, body) => {
            find_function_expression(arena, *body, through_application)
        }
        ExpressionDesc::Pexp_apply(apply)
            if through_application
                && apply.args.len() == 1
                && matches!(apply.args[0].0, ArgLabel::Nolabel) =>
        {
            find_function_expression(arena, apply.args[0].1, through_application)
        }
        _ => Err(expr),
    }
}

/// jsx_v4.ml `is_function_expression`.
fn is_function_expression(arena: &ParseArena, expr_idx: ExprIdx) -> bool {
    find_function_expression(arena, expr_idx, false).is_ok()
}

/// OCaml `modified_binding_old`: the component function whose parameters
/// define the props. When there is none (the
/// `component_call_needs_function_error_loc` error), the expression itself.
fn modified_binding_old_expr(arena: &ParseArena, expr_idx: ExprIdx) -> Expression {
    match find_function_expression(arena, expr_idx, true) {
        Ok(expr) | Err(expr) => expr.clone(),
    }
}

fn component_call_needs_function_error_loc(
    arena: &ParseArena,
    expr_idx: ExprIdx,
) -> Option<Location> {
    find_function_expression(arena, expr_idx, true)
        .err()
        .map(|expr| expr.pexp_loc)
}

fn pattern_is_plain_name_or_constraint(pat: &Pattern, arena: &ParseArena) -> bool {
    match &*pat.ppat_desc {
        PatternDesc::Ppat_var(_) => true,
        PatternDesc::Ppat_constraint(inner) => {
            let (inner_pat_idx, _) = &**inner;
            let inner_pat = arena.get_pat(*inner_pat_idx);
            matches!(&*inner_pat.ppat_desc, PatternDesc::Ppat_var(_))
        }
        _ => false,
    }
}

fn pattern_is_unit_or_any(arena: &ParseArena, pat: &Pattern) -> bool {
    if matches!(&*pat.ppat_desc, PatternDesc::Ppat_any) {
        return true;
    }
    if let PatternDesc::Ppat_construct(loc, _) = &*pat.ppat_desc {
        return arena.is_lident(loc.txt, "()");
    }
    false
}

fn string_int_attribute_loc_in_attrs(arena: &ParseArena, attrs: &Attributes) -> Option<Location> {
    attrs.iter().find_map(|attr| {
        matches!(arena.get_string(attr.0.txt), "string" | "int").then_some(attr.0.loc)
    })
}

fn string_int_attribute_loc_in_core_type(
    arena: &ParseArena,
    typ_idx: &CoreTypeIdx,
) -> Option<Location> {
    let typ = arena.get_core_type(*typ_idx);
    if let Some(loc) = string_int_attribute_loc_in_attrs(arena, &typ.ptyp_attributes) {
        return Some(loc);
    }
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, _) = &**inner;
            string_int_attribute_loc_in_attrs(arena, &arg.attrs)
                .or_else(|| string_int_attribute_loc_in_core_type(arena, &arg.typ))
                .or_else(|| string_int_attribute_loc_in_core_type(arena, ret))
        }
        CoreTypeDesc::Ptyp_tuple(items) => items
            .iter()
            .find_map(|item| string_int_attribute_loc_in_core_type(arena, item)),
        CoreTypeDesc::Ptyp_constr(inner) => inner
            .1
            .iter()
            .find_map(|item| string_int_attribute_loc_in_core_type(arena, item)),
        CoreTypeDesc::Ptyp_object(inner) => inner.0.iter().find_map(|field| match field {
            ObjectField::Otag(_, attrs, typ) => string_int_attribute_loc_in_attrs(arena, attrs)
                .or_else(|| string_int_attribute_loc_in_core_type(arena, typ)),
            ObjectField::Oinherit(typ) => string_int_attribute_loc_in_core_type(arena, typ),
        }),
        CoreTypeDesc::Ptyp_alias(inner) => string_int_attribute_loc_in_core_type(arena, &inner.0),
        CoreTypeDesc::Ptyp_variant(inner) => inner.0.iter().find_map(|field| match field {
            RowField::Rtag(_, attrs, _, args) => string_int_attribute_loc_in_attrs(arena, attrs)
                .or_else(|| {
                    args.iter()
                        .flat_map(|group| group.txt.iter())
                        .find_map(|arg| string_int_attribute_loc_in_core_type(arena, arg))
                }),
            RowField::Rinherit(typ) => string_int_attribute_loc_in_core_type(arena, typ),
        }),
        CoreTypeDesc::Ptyp_poly(inner) => string_int_attribute_loc_in_core_type(arena, &inner.1),
        CoreTypeDesc::Ptyp_package(package) => package
            .1
            .iter()
            .find_map(|(_, typ)| string_int_attribute_loc_in_core_type(arena, typ)),
        CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) | CoreTypeDesc::Ptyp_extension(_) => {
            None
        }
    }
}

/// `get_fn_name` (jsx_v4.ml:66-72). `pat_loc` is the `ppat_loc` OCaml sees on
/// the outer pattern: `map_binding` has replaced it with `empty_loc` for
/// `@react.component` (jsx_v4.ml:582-590), not for `componentWithProps`.
fn get_fn_name(
    arena: &ParseArena,
    config: &mut JsxConfig,
    pat: &Pattern,
    pat_loc: Location,
) -> String {
    match &*pat.ppat_desc {
        PatternDesc::Ppat_var(loc) => arena.get_string(loc.txt).to_string(),
        PatternDesc::Ppat_constraint(inner) => {
            let (ref inner_idx, _) = **inner;
            let inner_pat = arena.get_pat(*inner_idx);
            let inner_loc = inner_pat.ppat_loc;
            get_fn_name(arena, config, inner_pat, inner_loc)
        }
        _ => {
            set_fatal_error(config, pat_loc, REACT_COMPONENT_DESTRUCTURE_MSG);
            "make".to_string()
        }
    }
}

/// Get the location of the function name from a pattern
/// For Ppat_constraint, returns the OUTER constraint's location (not the inner pattern's)
/// This matches OCaml's jsx_v4.ml: `let binding_pat_loc = binding.pvb_pat.ppat_loc`
fn get_fn_name_loc(pat: &Pattern) -> Location {
    match &*pat.ppat_desc {
        PatternDesc::Ppat_var(loc) => loc.loc,
        // For constrained patterns, use the constraint's location (the full span including type annotation)
        // OCaml uses binding.pvb_pat.ppat_loc which is the outer Ppat_constraint's location
        PatternDesc::Ppat_constraint(_) => pat.ppat_loc,
        _ => pat.ppat_loc,
    }
}

fn make_module_name(config: &JsxConfig, fn_name: &str) -> String {
    // Component name: file_name (if any) + nested_modules (in order) +
    // fn_name (unless it is "make"), joined with '$'.
    let file_name = (!config.file_name.is_empty()).then_some(config.file_name.as_str());
    let fn_name = (fn_name != "make").then_some(fn_name);
    let parts: Vec<&str> = file_name
        .into_iter()
        .chain(config.nested_modules.iter().map(String::as_str))
        .chain(fn_name)
        .collect();
    parts.join("$")
}

/// Strip `option<T>` wrapper from a type, returning just `T`
/// jsx_v4.ml:114-118 `strip_option`: the first argument of an
/// `option<...>` (unqualified `Lident "option"`); any other type is kept.
fn strip_option(arena: &ParseArena, core_type: &CoreType) -> Option<CoreType> {
    match &*core_type.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            match arena.get_longident(lid.txt) {
                Longident::Lident(name) if arena.get_string(*name) == "option" => {
                    args.first().map(|t| arena.get_core_type(*t).clone())
                }
                _ => Some(core_type.clone()),
            }
        }
        _ => Some(core_type.clone()),
    }
}

/// jsx_v4.ml:138-158 `make_props_type_params`, for one prop.
fn make_props_type_param(
    arena: &ParseArena,
    nt: &NamedType,
    strip_explicit_option: bool,
    strip_explicit_nullable_of_ref: bool,
) -> Option<CoreType> {
    if nt.label == "key" {
        None
    } else if nt.label == "ref" {
        // If ref has a type annotation then use it, else 'ref (at the
        // prop's location).
        match &*nt.interior_type.ptyp_desc {
            CoreTypeDesc::Ptyp_any => Some(CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Borrowed("ref")))),
                ptyp_loc: nt.loc,
                ptyp_attributes: Attributes::new(),
            }),
            _ if strip_explicit_nullable_of_ref => strip_js_nullable(arena, &nt.interior_type),
            _ => Some(nt.interior_type.clone()),
        }
    } else if nt.is_optional && strip_explicit_option {
        strip_option(arena, &nt.interior_type)
    } else {
        Some(nt.interior_type.clone())
    }
}

/// Strip `Stdlib.Nullable.t<T>` wrapper from a type, returning just `T`
/// OCaml `strip_nullable` (jsx_v4.ml:120-131): the first argument of a
/// `nullable` / `Nullable.t` / `Stdlib.Nullable.t` annotation (none if it has
/// no arguments); any other type is kept.
fn strip_js_nullable(arena: &ParseArena, core_type: &CoreType) -> Option<CoreType> {
    if let CoreTypeDesc::Ptyp_constr(inner) = &*core_type.ptyp_desc {
        let (ref lid, ref args) = **inner;
        let is_nullable = match arena.get_longident(lid.txt) {
            Longident::Lident(name) => arena.get_string(*name) == "nullable",
            Longident::Ldot(outer, t) if arena.get_string(*t) == "t" => match outer.as_ref() {
                Longident::Lident(m) => arena.get_string(*m) == "Nullable",
                Longident::Ldot(root, m) => {
                    arena.get_string(*m) == "Nullable"
                        && matches!(root.as_ref(), Longident::Lident(r) if arena.get_string(*r) == "Stdlib")
                }
                _ => false,
            },
            _ => false,
        };
        if is_nullable {
            return args.first().map(|t| arena.get_core_type(*t).clone());
        }
    }
    Some(core_type.clone())
}

/// Create React.element type constraint
fn jsx_element_type(arena: &mut ParseArena, config: &JsxConfig, loc: &Location) -> CoreType {
    let element_str_idx = arena.intern_string("element");
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Loc {
                txt: module_access_name_with_idx(arena, config, element_str_idx),
                loc: *loc,
            },
            vec![],
        )))),
        ptyp_loc: *loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Wrap expression with React.element constraint (recursively through function bodies)
fn constrain_jsx_return(
    arena: &mut ParseArena,
    expr: Expression,
    config: &JsxConfig,
) -> Expression {
    let loc = &expr.pexp_loc;
    let element_type = jsx_element_type(arena, config, loc);
    let element_type_idx = arena.push_core_type(element_type);

    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) if is_function_expression(arena, braces.expr) => {
            let inner = arena.get_expr(braces.expr).clone();
            let constrained = constrain_jsx_return(arena, inner, config);
            let constrained_idx = arena.push_expr(constrained);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_braces(Box::new(
                    crate::parser::ast::PexpBraces {
                        expr: constrained_idx,
                        braces_loc: braces.braces_loc,
                    },
                ))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun {
                ref arg_label,
                ref default,
                ref lhs,
                ref rhs,
                ref arity,
                ref is_async,
            } = **inner;
            let rhs_expr = arena.get_expr(*rhs).clone();
            let constrained_rhs = constrain_jsx_return(arena, rhs_expr, config);
            let constrained_rhs_idx = arena.push_expr(constrained_rhs);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: *arg_label,
                    default: *default,
                    lhs: *lhs,
                    rhs: constrained_rhs_idx,
                    arity: *arity,
                    is_async: *is_async,
                }))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (ref param, ref inner_idx) = **inner;
            let inner_expr = arena.get_expr(*inner_idx).clone();
            let constrained = constrain_jsx_return(arena, inner_expr, config);
            let constrained_idx = arena.push_expr(constrained);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_newtype(Box::new((
                    *param,
                    constrained_idx,
                )))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref inner_idx, _) = **inner;
            // Already constrained, wrap the inner with jsx element constraint
            let inner_expr = arena.get_expr(*inner_idx).clone();
            let constrained = constrain_jsx_return(arena, inner_expr, config);
            let constrained_idx = arena.push_expr(constrained);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    constrained_idx,
                    element_type_idx,
                )))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (ref rec_flag, ref bindings, ref body_idx) = **inner;
            let body_expr = arena.get_expr(*body_idx).clone();
            let constrained_body = constrain_jsx_return(arena, body_expr, config);
            let constrained_body_idx = arena.push_expr(constrained_body);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                    *rec_flag,
                    bindings.clone(),
                    constrained_body_idx,
                )))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        ExpressionDesc::Pexp_sequence(first, second) => {
            let second_expr = arena.get_expr(*second).clone();
            let constrained_second = constrain_jsx_return(arena, second_expr, config);
            let constrained_second_idx = arena.push_expr(constrained_second);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_sequence(
                    *first,
                    constrained_second_idx,
                )),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        _ => {
            // Default: wrap with constraint
            // OCaml uses ghost location for the synthesized Pexp_constraint wrapper
            let expr_idx = arena.push_expr(expr.clone());
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    expr_idx,
                    element_type_idx,
                )))),
                pexp_loc: empty_loc(),
                pexp_attributes: Attributes::new(),
            }
        }
    }
}

fn safe_type_from_value(value: &str) -> String {
    if value.is_empty() || !value.starts_with('_') {
        value.to_string()
    } else {
        format!("T{}", value)
    }
}

/// Capitalize the first character of a string (like OCaml's String.capitalize_ascii)
fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

/// Parse the dotted JSX module path the same way as OCaml `Longident.parse`.
fn jsx_module_longident(arena: &mut ParseArena, config: &JsxConfig) -> Longident {
    let capitalized = capitalize_first(&config.module_name);
    let mut segments = capitalized.split('.');
    let first = segments.next().unwrap_or("");
    let mut longident = Longident::Lident(arena.push_string(first));
    for segment in segments {
        longident = Longident::Ldot(Box::new(longident), arena.push_string(segment));
    }
    longident
}

fn module_access_name_with_idx(
    arena: &mut ParseArena,
    config: &JsxConfig,
    value: StrIdx,
) -> LidentIdx {
    let module_path = jsx_module_longident(arena, config);
    arena.push_longident(Longident::Ldot(Box::new(module_path), value))
}

/// Build module access path: capitalize(module_) + "." + value -> parsed as Longident.
/// Matches OCaml `Jsx_v4.module_access_name`.
fn module_access_name(arena: &mut ParseArena, config: &JsxConfig, value: &str) -> LidentIdx {
    let val_str_idx = arena.intern_string(value);
    module_access_name_with_idx(arena, config, val_str_idx)
}

/// Coerce a generated component wrapper through the configured JSX module's
/// component identity. Mirrors `Jsx_v4.jsx_component_expr`.
fn jsx_component_expr(
    arena: &mut ParseArena,
    config: &JsxConfig,
    loc: Location,
    expr: Expression,
) -> Expression {
    let component_lid = module_access_name(arena, config, "component");
    let component_expr = arena.push_expr(Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
            txt: component_lid,
            loc,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    });
    let argument = arena.push_expr(expr);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: component_expr,
            args: vec![(ArgLabel::Nolabel, argument)],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Try to find the key prop in a list of JSX props
/// Returns the (label, expression) if found
fn try_find_key_prop(arena: &mut ParseArena, props: &[JsxProp]) -> Option<(ArgLabel, ExprIdx)> {
    for prop in props {
        match prop {
            JsxProp::Punning { optional, name } if arena.get_string(name.txt) == "key" => {
                let key_str_idx = arena.intern_string("key");
                let label_loc = Located::new(key_str_idx, name.loc);
                let arg_label = if *optional {
                    ArgLabel::Optional(label_loc)
                } else {
                    ArgLabel::Labelled(label_loc)
                };
                // OCaml: Exp.ident without ~loc defaults to Location.none (ghost)
                let expr = Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                        txt: arena.push_longident(Longident::Lident(key_str_idx)),
                        loc: name.loc,
                    })),
                    pexp_loc: empty_loc(),
                    pexp_attributes: Attributes::new(),
                };
                return Some((arg_label, arena.push_expr(expr)));
            }
            JsxProp::Value {
                name,
                optional,
                value,
            } if arena.get_string(name.txt) == "key" => {
                let key_str_idx = name.txt;
                let label_loc = Located::new(key_str_idx, name.loc);
                let arg_label = if *optional {
                    ArgLabel::Optional(label_loc)
                } else {
                    ArgLabel::Labelled(label_loc)
                };
                return Some((arg_label, *value));
            }
            _ => {}
        }
    }
    None
}

/// Create a unit expression () at the given location
fn unit_expr(arena: &mut ParseArena, loc: &Location) -> Expression {
    let unit_str_idx = arena.intern_string("()");
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
            Loc {
                txt: arena.push_longident(Longident::Lident(unit_str_idx)),
                loc: *loc,
            },
            ctor_args(Vec::new(), *loc),
        )),
        pexp_loc: *loc,
        pexp_attributes: Attributes::new(),
    }
}

fn is_optional(label: &ArgLabel) -> bool {
    matches!(label, ArgLabel::Optional(_))
}

fn is_labelled(label: &ArgLabel) -> bool {
    matches!(label, ArgLabel::Labelled(_))
}

fn get_label(arena: &ParseArena, label: &ArgLabel) -> String {
    match label {
        ArgLabel::Labelled(s) | ArgLabel::Optional(s) => arena.get_string(s.txt).to_string(),
        ArgLabel::Nolabel => String::new(),
    }
}

fn empty_loc() -> Location {
    // Use Location::none() to match OCaml's Location.none (serialized as (loc 1 -1 1 -1))
    Location::none()
}

/// Recursively extract named arguments from a function expression
/// OCaml `recursively_transform_named_args_for_make` (jsx_v4.ml:242-346).
/// The first error it raises (key prop, non-plain ref argument) is returned.
fn recursively_extract_named_args(
    arena: &ParseArena,
    expr: &Expression,
) -> (
    Vec<ExtractedArg>,
    Vec<(StringLoc, Attributes)>,
    Option<CoreType>,
    Vec<JsxPreprocessorWarning>,
    Option<(Location, &'static str)>,
) {
    let mut args = vec![];
    let mut newtypes = vec![];
    let mut warnings = vec![];
    let mut error = None;
    extract_args_rec(
        arena,
        expr,
        &mut args,
        &mut newtypes,
        &mut warnings,
        &mut error,
    );
    (args, newtypes, None, warnings, error)
}

fn extract_args_rec(
    arena: &ParseArena,
    expr: &Expression,
    args: &mut Vec<ExtractedArg>,
    newtypes: &mut Vec<(StringLoc, Attributes)>,
    warnings: &mut Vec<JsxPreprocessorWarning>,
    error: &mut Option<(Location, &'static str)>,
) {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            newtypes.extend(arena.nary_fun_newtypes(inner).iter().cloned());
            let params = arena.nary_fun_params(inner);
            // `transform_params_for_make` (jsx_v4.ml:253-346).
            for param in params.iter() {
                let arg_label = &param.p_lbl;
                let default = &param.p_default;
                let lhs_pat = arena.get_pat(param.p_pat);
                if is_labelled(arg_label) || is_optional(arg_label) {
                    if get_label(arena, arg_label) == "key" {
                        *error = Some((expr.pexp_loc, COMPONENT_KEY_PROP_MSG));
                        return;
                    }
                    if let Some(message) =
                        optional_argument_annotation_warning(arena, arg_label, default, lhs_pat)
                    {
                        let loc = lhs_pat.ppat_loc;
                        warnings.push(JsxPreprocessorWarning {
                            start_pos: *arena.loc_start(loc),
                            end_pos: *arena.loc_end(loc),
                            message,
                        });
                    }
                    args.push(ExtractedArg {
                        label: *arg_label,
                        default: default.map(|idx| arena.get_expr(idx).clone()),
                        pattern: lhs_pat.clone(),
                        alias: get_alias_from_pattern(arena, lhs_pat, arg_label),
                        loc: lhs_pat.ppat_loc,
                        type_: get_type_from_pattern(arena, lhs_pat),
                    });
                    continue;
                }
                // An unlabelled parameter ends the props: `()`/`_` and plain
                // variables stop the walk (a `ref` variable becomes the ref
                // prop of forwardRef); any other pattern is an error.
                if pattern_is_unit_or_any(arena, lhs_pat) {
                    return;
                }
                if pattern_is_plain_name_or_constraint(lhs_pat, arena) {
                    let alias = get_alias_from_pattern(arena, lhs_pat, arg_label);
                    if alias == "ref" || alias == "_ref" {
                        args.push(ExtractedArg {
                            label: *arg_label,
                            default: None,
                            pattern: lhs_pat.clone(),
                            alias,
                            loc: lhs_pat.ppat_loc,
                            type_: get_type_from_pattern(arena, lhs_pat),
                        });
                    }
                    return;
                }
                *error = Some((lhs_pat.ppat_loc, COMPONENT_REF_PLAIN_ARGS_MSG));
                return;
            }
            // All parameters consumed: keep walking into the body.
            let body = arena.get_expr(arena.nary_fun_body(inner));
            extract_args_rec(arena, body, args, newtypes, warnings, error);
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (ref name, ref body_idx) = **inner;
            newtypes.push((*name, Attributes::new()));
            let body: &Expression = arena.get_expr(*body_idx);
            extract_args_rec(arena, body, args, newtypes, warnings, error);
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref inner_idx, _) = **inner;
            let inner: &Expression = arena.get_expr(*inner_idx);
            extract_args_rec(arena, inner, args, newtypes, warnings, error);
        }
        _ => {}
    }
}

fn optional_argument_annotation_warning(
    arena: &ParseArena,
    arg_label: &ArgLabel,
    default: &Option<ExprIdx>,
    lhs_pat: &Pattern,
) -> Option<String> {
    if !is_optional(arg_label) || default.is_some() {
        return None;
    }

    let PatternDesc::Ppat_constraint(inner) = &*lhs_pat.ppat_desc else {
        return None;
    };

    let (_, typ_idx) = **inner;
    let typ = arena.get_core_type(typ_idx);

    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) if inner.1.len() == 1 => {
            let last_idx = arena.get_longident(inner.0.txt).last_idx();
            if arena.get_string(last_idx) == "option" {
                return None;
            }
        }
        _ => {}
    }

    let current_type = match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let type_name = arena
                .get_longident(inner.0.txt)
                .flatten_idx()
                .iter()
                .map(|idx| arena.get_string(*idx))
                .collect::<Vec<_>>()
                .join(".");
            if inner.1.is_empty() {
                type_name
            } else {
                format!("{type_name}(...)")
            }
        }
        _ => "...".to_string(),
    };

    Some(format!(
        "React: optional argument annotations must have explicit `option`. Did you mean `option<{}>=?`?",
        current_type
    ))
}

fn get_alias_from_pattern(arena: &ParseArena, pat: &Pattern, label: &ArgLabel) -> String {
    match &*pat.ppat_desc {
        PatternDesc::Ppat_var(loc) => arena.get_string(loc.txt).to_string(),
        PatternDesc::Ppat_alias(_, loc) => arena.get_string(loc.txt).to_string(),
        PatternDesc::Ppat_constraint(inner) => {
            let (ref inner_idx, _) = **inner;
            let inner_pat = arena.get_pat(*inner_idx);
            get_alias_from_pattern(arena, inner_pat, label)
        }
        PatternDesc::Ppat_any => "_".to_string(),
        _ => get_label(arena, label),
    }
}

fn get_type_from_pattern(_arena: &ParseArena, pat: &Pattern) -> Option<CoreType> {
    match &*pat.ppat_desc {
        PatternDesc::Ppat_constraint(inner) => {
            let (_, ref typ) = **inner;
            let typ = _arena.get_core_type(*typ);
            // Don't use package types
            if matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_package(_)) {
                None
            } else {
                Some(typ.clone())
            }
        }
        _ => None,
    }
}

fn arg_to_type(arena: &ParseArena, arg: &ExtractedArg) -> Option<NamedType> {
    let label = get_label(arena, &arg.label);
    // For unlabeled arguments (like 'ref' in forwardRef), use the alias as label
    // Note: "_ref" (underscore-prefixed) means unused ref, should NOT be added to props
    let label = if label.is_empty() {
        if arg.alias == "ref" {
            // Only "ref" (without underscore) gets added to props
            "ref".to_string()
        } else {
            // "_ref" or other unlabeled args are excluded from props
            return None;
        }
    } else {
        label
    };

    let interior_type = arg.type_.clone().unwrap_or_else(|| CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
        ptyp_loc: arg.loc,
        ptyp_attributes: Attributes::new(),
    });

    Some(NamedType {
        is_optional: is_optional(&arg.label),
        label,
        attrs: arg.pattern.ppat_attributes.clone(),
        loc: arg.loc,
        interior_type,
    })
}

/// Check for duplicate labels in props (OCaml: check_duplicated_label)
fn duplicated_label(named_types: &[NamedType]) -> Option<(Location, &str)> {
    for (idx, nt) in named_types.iter().enumerate().rev() {
        if named_types[..idx]
            .iter()
            .any(|previous| previous.label.as_str() == nt.label.as_str())
        {
            return Some((nt.loc, nt.label.as_str()));
        }
    }
    None
}

fn set_duplicate_label_error(config: &mut JsxConfig, named_types: &[NamedType]) {
    if let Some((loc, label)) = duplicated_label(named_types) {
        let message = format!(
            "{COMPONENT_DUPLICATE_PROP_MSG_PREFIX}{label}{COMPONENT_DUPLICATE_PROP_MSG_SUFFIX}"
        );
        set_fatal_error(config, loc, &message);
    }
}

fn make_props_record_type(
    arena: &mut ParseArena,
    config: &mut JsxConfig,
    name: &str,
    loc: &Location,
    named_types: &[NamedType],
    has_forward_ref: bool,
) -> StructureItem {
    set_duplicate_label_error(config, named_types);

    let label_decls: Vec<LabelDeclaration> = named_types
        .iter()
        .map(|nt| {
            // OCaml uses ghost location for the Ptyp_var inside label declarations
            let type_var = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(
                    safe_type_from_value(&nt.label),
                )))),
                ptyp_loc: empty_loc(),
                ptyp_attributes: Attributes::new(),
            };

            // Key prop is always optional in type declaration (OCaml: if label = "key" then ~optional:true)
            // For forwardRef, ref is also always optional
            let is_optional = if nt.label == "key" || (nt.label == "ref" && has_forward_ref) {
                true
            } else {
                nt.is_optional
            };

            let label_str_idx = arena.push_interned_string(&nt.label);
            let typ_idx = arena.push_core_type(type_var);
            crate::ast_helper_type::field(
                arena,
                nt.loc,
                nt.attrs.clone(),
                MutableFlag::Immutable,
                is_optional,
                None,
                Loc {
                    txt: label_str_idx,
                    loc: nt.loc,
                },
                typ_idx,
            )
        })
        .collect();

    let type_params: Vec<(CoreTypeIdx, Variance)> = named_types
        .iter()
        .filter(|nt| nt.label != "key")
        .map(|nt| {
            (
                arena.push_core_type(CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(
                        safe_type_from_value(&nt.label),
                    )))),
                    ptyp_loc: nt.loc,
                    ptyp_attributes: Attributes::new(),
                }),
                Variance::Invariant,
            )
        })
        .collect();

    let name_str_idx = arena.push_interned_string(name);
    let jsx_props_attr_idx = arena.intern_string("res.jsxComponentProps");
    let type_decl = TypeDeclaration {
        ptype_name: Loc {
            txt: name_str_idx,
            loc: *loc,
        },
        ptype_params: type_params,
        ptype_cstrs: vec![],
        ptype_kind: TypeKind::Ptype_record(label_decls),
        ptype_private: PrivateFlag::Public,
        ptype_manifest: None,
        ptype_origin: TypeDeclarationOrigin::Declared,
        ptype_attributes: Attributes::from_vec(vec![(
            Loc {
                txt: jsx_props_attr_idx,
                loc: empty_loc(),
            },
            Payload::PStr(Box::default()),
        )]),
        ptype_loc: *loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_type(Box::new((
            RecFlag::Nonrecursive,
            vec![type_decl],
        )))),
        // OCaml's Str.type_ without ~loc uses Location.none
        pstr_loc: empty_loc(),
    }
}

/// Create props record type declaration for signatures
fn make_props_record_type_sig(
    arena: &mut ParseArena,
    config: &mut JsxConfig,
    name: &str,
    loc: &Location,
    named_types: &[NamedType],
) -> SignatureItem {
    set_duplicate_label_error(config, named_types);

    let label_decls: Vec<LabelDeclaration> = named_types
        .iter()
        .map(|nt| {
            // OCaml uses ghost location for the Ptyp_var inside label declarations
            let type_var = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(
                    safe_type_from_value(&nt.label),
                )))),
                ptyp_loc: empty_loc(),
                ptyp_attributes: Attributes::new(),
            };

            // Key prop is always optional in type declaration (OCaml: if label = "key" then ~optional:true)
            let is_optional = if nt.label == "key" {
                true
            } else {
                nt.is_optional
            };

            let label_str_idx = arena.push_interned_string(&nt.label);
            let typ_idx = arena.push_core_type(type_var);
            crate::ast_helper_type::field(
                arena,
                nt.loc,
                nt.attrs.clone(),
                MutableFlag::Immutable,
                is_optional,
                None,
                Loc {
                    txt: label_str_idx,
                    loc: nt.loc,
                },
                typ_idx,
            )
        })
        .collect();

    let type_params: Vec<(CoreTypeIdx, Variance)> = named_types
        .iter()
        .filter(|nt| nt.label != "key")
        .map(|nt| {
            (
                arena.push_core_type(CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(
                        safe_type_from_value(&nt.label),
                    )))),
                    ptyp_loc: nt.loc,
                    ptyp_attributes: Attributes::new(),
                }),
                Variance::Invariant,
            )
        })
        .collect();

    let name_str_idx = arena.push_interned_string(name);
    let jsx_props_attr_idx = arena.intern_string("res.jsxComponentProps");
    let type_decl = TypeDeclaration {
        ptype_name: Loc {
            txt: name_str_idx,
            loc: *loc,
        },
        ptype_params: type_params,
        ptype_cstrs: vec![],
        ptype_kind: TypeKind::Ptype_record(label_decls),
        ptype_private: PrivateFlag::Public,
        ptype_manifest: None,
        ptype_origin: TypeDeclarationOrigin::Declared,
        ptype_attributes: Attributes::from_vec(vec![(
            Loc {
                txt: jsx_props_attr_idx,
                loc: empty_loc(),
            },
            Payload::PStr(Box::default()),
        )]),
        ptype_loc: *loc,
    };

    SignatureItem {
        psig_desc: Box::new(SignatureItemDesc::Psig_type(Box::new((
            RecFlag::Nonrecursive,
            vec![type_decl],
        )))),
        // OCaml: Sig.type_ without ~loc uses Location.none
        psig_loc: empty_loc(),
    }
}

/// Create abstract props type with manifest (for sharedProps)
/// type props = sharedProps<T>
fn make_props_abstract_type(
    arena: &mut ParseArena,
    name: &str,
    loc: &Location,
    manifest: &CoreType,
    typ_vars: &[CoreType],
) -> StructureItem {
    let type_params: Vec<(CoreTypeIdx, Variance)> = typ_vars
        .iter()
        .map(|v| (arena.push_core_type(v.clone()), Variance::Invariant))
        .collect();

    let name_str_idx = arena.push_interned_string(name);
    let type_decl = TypeDeclaration {
        ptype_name: Loc {
            txt: name_str_idx,
            loc: *loc,
        },
        ptype_params: type_params,
        ptype_cstrs: vec![],
        ptype_kind: TypeKind::Ptype_abstract,
        ptype_private: PrivateFlag::Public,
        ptype_manifest: Some(arena.push_core_type(manifest.clone())),
        ptype_origin: TypeDeclarationOrigin::Declared,
        ptype_attributes: Attributes::new(),
        ptype_loc: *loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_type(Box::new((
            RecFlag::Nonrecursive,
            vec![type_decl],
        )))),
        // OCaml's Str.type_ without ~loc uses Location.none
        pstr_loc: empty_loc(),
    }
}

/// Create abstract props type with manifest for signatures (for sharedProps)
fn make_props_abstract_type_sig(
    arena: &mut ParseArena,
    name: &str,
    loc: &Location,
    manifest: &CoreType,
    typ_vars: &[CoreType],
) -> SignatureItem {
    let type_params: Vec<(CoreTypeIdx, Variance)> = typ_vars
        .iter()
        .map(|v| (arena.push_core_type(v.clone()), Variance::Invariant))
        .collect();

    let name_str_idx = arena.push_interned_string(name);
    let type_decl = TypeDeclaration {
        ptype_name: Loc {
            txt: name_str_idx,
            loc: *loc,
        },
        ptype_params: type_params,
        ptype_cstrs: vec![],
        ptype_kind: TypeKind::Ptype_abstract,
        ptype_private: PrivateFlag::Public,
        ptype_manifest: Some(arena.push_core_type(manifest.clone())),
        ptype_origin: TypeDeclarationOrigin::Declared,
        ptype_attributes: Attributes::new(),
        ptype_loc: *loc,
    };

    SignatureItem {
        psig_desc: Box::new(SignatureItemDesc::Psig_type(Box::new((
            RecFlag::Nonrecursive,
            vec![type_decl],
        )))),
        // OCaml: Sig.type_ without ~loc uses Location.none
        psig_loc: empty_loc(),
    }
}

// ============================================================================
// Config Update
// ============================================================================

fn update_config_from_attribute(arena: &ParseArena, attr: &Attribute, config: &mut JsxConfig) {
    // Parse @@jsxConfig({version: 4, module_: "React"})
    // Matches OCaml's update_config behavior
    if let Payload::PStr(items) = &attr.1 {
        for item in items.iter() {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*item.pstr_desc {
                let (ref expr, _) = **eval_inner;
                // jsx_ppx.ml `get_payload_fields`: `Ast_payload.unwrap_payload_expression`.
                let expr = if items.len() == 1 {
                    crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr))
                } else {
                    arena.get_expr(*expr)
                };
                if let ExpressionDesc::Pexp_record(rec_inner) = &*expr.pexp_desc {
                    let (ref fields, _) = **rec_inner;
                    let mut module_raw: Option<String> = None;
                    let mut version_raw: Option<i32> = None;

                    for field in fields {
                        let last_idx = arena.get_longident(field.lid.txt).last_idx();
                        let last_str = arena.get_string(last_idx);
                        match last_str {
                            "version" => {
                                if let ExpressionDesc::Pexp_constant(c) =
                                    &*crate::ast_payload::unwrap_braces(
                                        arena,
                                        arena.get_expr(field.expr),
                                    )
                                    .pexp_desc
                                {
                                    if let Constant::Integer(s, _) = &**c {
                                        if let Ok(v) = s.parse::<i32>() {
                                            version_raw = Some(v);
                                        }
                                    }
                                }
                            }
                            "module_" => {
                                match crate::ast_payload::semantic_string_of_expression(
                                    arena,
                                    arena.get_expr(field.expr),
                                ) {
                                    Ok(value) => {
                                        if let Some(value) = value {
                                            module_raw = Some(value);
                                        }
                                    }
                                    Err(error) => {
                                        set_fatal_error(config, error.loc, error.message);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }

                    // OCaml behavior: if module is not "react" (case-insensitive), it's "generic"
                    // and version is always set to 4. Otherwise use explicit version.
                    let is_generic = match &module_raw {
                        Some(m) if m.to_lowercase() == "react" => false,
                        Some(_) => true,
                        None => false,
                    };

                    match (is_generic, version_raw) {
                        (true, _) => config.version = 4,
                        (false, Some(v)) => config.version = v,
                        (false, None) => {}
                    }

                    if let Some(m) = module_raw {
                        config.module_name = m;
                    }
                }
            }
        }
    }
}

// ============================================================================
// Structure/Signature Item Desc Transformation (for non-component items)
// ============================================================================

fn transform_structure_item_desc(
    desc: StructureItemDesc,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> StructureItemDesc {
    match desc {
        StructureItemDesc::Pstr_value(inner) => StructureItemDesc::Pstr_value(inner),
        StructureItemDesc::Pstr_eval(inner) => {
            let (expr_idx, attrs) = *inner;
            let expr = arena.get_expr(expr_idx).clone();
            let transformed = transform_expression(expr, config, arena);
            StructureItemDesc::Pstr_eval(Box::new((arena.push_expr(transformed), attrs)))
        }
        StructureItemDesc::Pstr_module(mb) => StructureItemDesc::Pstr_module(Box::new(
            transform_module_binding(*mb, config, arena, warnings),
        )),
        StructureItemDesc::Pstr_recmodule(mbs) => {
            let mut result = vec![];
            for mb in *mbs {
                result.push(transform_module_binding(mb, config, arena, warnings));
            }
            StructureItemDesc::Pstr_recmodule(Box::new(result))
        }
        StructureItemDesc::Pstr_modtype(mt) => StructureItemDesc::Pstr_modtype(Box::new(
            transform_module_type_declaration(*mt, config, arena, warnings),
        )),
        StructureItemDesc::Pstr_include(incl) => {
            let mod_expr = arena.get_mod_expr(incl.pincl_mod).clone();
            let transformed = transform_module_expr(mod_expr, config, arena, warnings);
            StructureItemDesc::Pstr_include(Box::new(IncludeDeclaration {
                pincl_mod: arena.push_mod_expr(transformed),
                pincl_loc: incl.pincl_loc,
                pincl_attributes: incl.pincl_attributes,
            }))
        }
        StructureItemDesc::Pstr_extension(inner) => {
            let ((name, payload), attrs) = *inner;
            let payload = transform_payload(payload, config, arena, warnings);
            StructureItemDesc::Pstr_extension(Box::new(((name, payload), attrs)))
        }
        other => other,
    }
}

fn transform_module_type_declaration(
    mt: ModuleTypeDeclaration,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> ModuleTypeDeclaration {
    ModuleTypeDeclaration {
        pmtd_name: mt.pmtd_name,
        pmtd_type: mt
            .pmtd_type
            .map(|mty| transform_module_type_idx(mty, config, arena, warnings)),
        pmtd_attributes: mt.pmtd_attributes,
        pmtd_loc: mt.pmtd_loc,
    }
}

fn transform_module_type_idx(
    mty: crate::parse_arena::ModTypeIdx,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> crate::parse_arena::ModTypeIdx {
    let mty_val = arena.get_mod_type(mty).clone();
    let transformed = transform_module_type(mty_val, config, arena, warnings);
    arena.push_mod_type(transformed)
}

/// `default_mapper.module_type` with the JSX `signature` override
/// (compiler/syntax/src/jsx_ppx.ml:101-120): every nested module type and
/// module expression is visited.
fn transform_module_type(
    mty: ModuleType,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> ModuleType {
    ModuleType {
        pmty_desc: Box::new(match *mty.pmty_desc {
            ModuleTypeDesc::Pmty_signature(sig_items) => {
                // Save and reset has_component (OCaml: config.has_component <- false)
                let old_has_component = config.has_component;
                config.has_component = false;
                // Transform signature items
                let mut result = vec![];
                for item in *sig_items {
                    let items = transform_signature_item_multi(item, config, arena, warnings);
                    result.extend(items);
                }
                // Restore has_component
                config.has_component = old_has_component;
                ModuleTypeDesc::Pmty_signature(Box::new(result))
            }
            ModuleTypeDesc::Pmty_functor(inner) => {
                let (name, arg, body) = *inner;
                // OCaml evaluates constructor arguments right to left.
                let body = transform_module_type_idx(body, config, arena, warnings);
                let arg = arg.map(|arg| transform_module_type_idx(arg, config, arena, warnings));
                ModuleTypeDesc::Pmty_functor(Box::new((name, arg, body)))
            }
            ModuleTypeDesc::Pmty_with(inner) => {
                let (body, constraints) = *inner;
                let body = transform_module_type_idx(body, config, arena, warnings);
                ModuleTypeDesc::Pmty_with(Box::new((body, constraints)))
            }
            ModuleTypeDesc::Pmty_typeof(mexpr) => {
                let mexpr_val = arena.get_mod_expr(mexpr).clone();
                let transformed = transform_module_expr(mexpr_val, config, arena, warnings);
                ModuleTypeDesc::Pmty_typeof(arena.push_mod_expr(transformed))
            }
            other => other,
        }),
        pmty_loc: mty.pmty_loc,
        pmty_attributes: mty.pmty_attributes,
    }
}

fn transform_signature_item_desc(
    desc: SignatureItemDesc,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> SignatureItemDesc {
    match desc {
        SignatureItemDesc::Psig_module(md) => {
            // Transform module declaration - recurse into the module type
            let pmd_type = transform_module_type_idx(md.pmd_type, config, arena, warnings);
            SignatureItemDesc::Psig_module(Box::new(ModuleDeclaration {
                pmd_name: md.pmd_name,
                pmd_type,
                pmd_attributes: md.pmd_attributes,
                pmd_loc: md.pmd_loc,
            }))
        }
        SignatureItemDesc::Psig_recmodule(mds) => {
            // Transform recursive module declarations
            SignatureItemDesc::Psig_recmodule(Box::new(
                mds.into_iter()
                    .map(|md| ModuleDeclaration {
                        pmd_name: md.pmd_name,
                        pmd_type: transform_module_type_idx(md.pmd_type, config, arena, warnings),
                        pmd_attributes: md.pmd_attributes,
                        pmd_loc: md.pmd_loc,
                    })
                    .collect(),
            ))
        }
        SignatureItemDesc::Psig_modtype(mtd) => {
            // Transform module type declaration
            SignatureItemDesc::Psig_modtype(Box::new(transform_module_type_declaration(
                *mtd, config, arena, warnings,
            )))
        }
        SignatureItemDesc::Psig_include(incl) => {
            let incl = *incl;
            SignatureItemDesc::Psig_include(Box::new(IncludeDescription {
                pincl_mod: transform_module_type_idx(incl.pincl_mod, config, arena, warnings),
                ..incl
            }))
        }
        SignatureItemDesc::Psig_extension(inner) => {
            let ((name, payload), attrs) = *inner;
            let payload = transform_payload(payload, config, arena, warnings);
            SignatureItemDesc::Psig_extension(Box::new(((name, payload), attrs)))
        }
        other => other,
    }
}

/// `default_mapper.payload` (compiler/ml/ast_mapper.ml): a structure or
/// signature payload goes back through the JSX `structure`/`signature`
/// mappers (compiler/syntax/src/jsx_ppx.ml:97-128), a pattern guard through
/// `expr`.
fn transform_payload(
    payload: Payload,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> Payload {
    match payload {
        Payload::PStr(items) => Payload::PStr(Box::new(transform_structure_with_config(
            *items, config, arena, warnings,
        ))),
        Payload::PSig(items) => {
            let old_has_component = config.has_component;
            config.has_component = false;
            let mut result = vec![];
            for item in *items {
                result.extend(transform_signature_item_multi(
                    item, config, arena, warnings,
                ));
            }
            config.has_component = old_has_component;
            Payload::PSig(Box::new(result))
        }
        Payload::PPat(inner) => {
            let (pat, guard) = *inner;
            let guard = guard.map(|guard| {
                let guard_expr = arena.get_expr(guard).clone();
                let transformed = transform_expression(guard_expr, config, arena);
                arena.push_expr(transformed)
            });
            Payload::PPat(Box::new((pat, guard)))
        }
        other => other,
    }
}

fn transform_module_binding(
    mb: ModuleBinding,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> ModuleBinding {
    let pmb_expr = {
        let mexpr_val = arena.get_mod_expr(mb.pmb_expr).clone();
        let transformed = transform_module_expr(mexpr_val, config, arena, warnings);
        arena.push_mod_expr(transformed)
    };
    ModuleBinding {
        pmb_name: mb.pmb_name,
        pmb_expr,
        pmb_attributes: mb.pmb_attributes,
        pmb_loc: mb.pmb_loc,
    }
}

/// Transform a structure with an existing config (preserves file_name and nested_modules)
fn transform_structure_with_config(
    structure: Structure,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> Structure {
    // Save and reset has_component (OCaml: config.has_component <- false)
    let old_has_component = config.has_component;
    config.has_component = false;

    let mut result = vec![];
    for item in structure {
        let items = transform_structure_item_multi(item, config, arena, warnings);
        result.extend(items);
    }

    // Restore has_component
    config.has_component = old_has_component;
    result
}

fn transform_module_expr(
    mexpr: ModuleExpr,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
    warnings: &mut Vec<JsxPreprocessorWarning>,
) -> ModuleExpr {
    ModuleExpr {
        pmod_desc: Box::new(match *mexpr.pmod_desc {
            ModuleExprDesc::Pmod_structure(items) => {
                // Transform structure with current config (preserving file_name and nested_modules)
                ModuleExprDesc::Pmod_structure(Box::new(transform_structure_with_config(
                    *items, config, arena, warnings,
                )))
            }
            ModuleExprDesc::Pmod_functor(inner) => {
                let (arg, arg_ty, body) = *inner;
                let body_expr = arena.get_mod_expr(body).clone();
                let transformed_body = transform_module_expr(body_expr, config, arena, warnings);
                let arg_ty =
                    arg_ty.map(|arg_ty| transform_module_type_idx(arg_ty, config, arena, warnings));
                ModuleExprDesc::Pmod_functor(Box::new((
                    arg,
                    arg_ty,
                    arena.push_mod_expr(transformed_body),
                )))
            }
            ModuleExprDesc::Pmod_apply(m1, m2) => {
                let m1_expr = arena.get_mod_expr(m1).clone();
                let m2_expr = arena.get_mod_expr(m2).clone();
                let m1_transformed = transform_module_expr(m1_expr, config, arena, warnings);
                let m2_transformed = transform_module_expr(m2_expr, config, arena, warnings);
                ModuleExprDesc::Pmod_apply(
                    arena.push_mod_expr(m1_transformed),
                    arena.push_mod_expr(m2_transformed),
                )
            }
            ModuleExprDesc::Pmod_constraint(m, mt) => {
                // OCaml evaluates constructor arguments right to left, so the
                // module type is mapped before the module expression.
                let mt = transform_module_type_idx(mt, config, arena, warnings);
                let m_expr = arena.get_mod_expr(m).clone();
                let m_transformed = transform_module_expr(m_expr, config, arena, warnings);
                ModuleExprDesc::Pmod_constraint(arena.push_mod_expr(m_transformed), mt)
            }
            ModuleExprDesc::Pmod_unpack(expr) => {
                let expr_val = arena.get_expr(expr).clone();
                let transformed = transform_expression(expr_val, config, arena);
                ModuleExprDesc::Pmod_unpack(arena.push_expr(transformed))
            }
            other => other,
        }),
        pmod_loc: mexpr.pmod_loc,
        pmod_attributes: mexpr.pmod_attributes,
    }
}

fn transform_value_binding(
    binding: ValueBinding,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
) -> ValueBinding {
    let pvb_expr = transform_expression(arena.get_expr(binding.pvb_expr).clone(), config, arena);
    ValueBinding {
        pvb_jsx_component: binding.pvb_jsx_component,
        pvb_pat: binding.pvb_pat,
        pvb_expr: arena.push_expr(pvb_expr),
        pvb_attributes: binding.pvb_attributes,
        pvb_loc: binding.pvb_loc,
    }
}

// ============================================================================
// Expression Transformation
// ============================================================================

fn transform_expression(
    expr: Expression,
    config: &mut JsxConfig,
    arena: &mut ParseArena,
) -> Expression {
    // Every arm below only rebuilds its node around transformed children,
    // except JSX elements and module expressions. A subtree without either
    // comes back unchanged, so return it without rebuilding.
    if !expression_may_change(&expr, arena, &mut config.unchanged_memo) {
        return expr;
    }
    let new_desc = match *expr.pexp_desc {
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            transform_jsx_element(*jsx, config, &expr.pexp_loc, &expr.pexp_attributes, arena)
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (rec_flag, bindings, body) = *inner;
            let transformed_bindings = bindings
                .into_iter()
                .map(|binding| transform_value_binding(binding, config, arena))
                .collect();
            let body_expr = arena.get_expr(body).clone();
            let transformed_body = transform_expression(body_expr, config, arena);
            ExpressionDesc::Pexp_let(Box::new((
                rec_flag,
                transformed_bindings,
                arena.push_expr(transformed_body),
            )))
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun {
                arg_label,
                default,
                lhs,
                rhs,
                is_async,
                arity,
            } = *inner;
            let rhs_expr = arena.get_expr(rhs).clone();
            let transformed_rhs = transform_expression(rhs_expr, config, arena);
            let transformed_default = default.map(|d| {
                let d_expr = arena.get_expr(d).clone();
                let rw = transform_expression(d_expr, config, arena);
                arena.push_expr(rw)
            });
            ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label,
                default: transformed_default,
                lhs,
                rhs: arena.push_expr(transformed_rhs),
                is_async,
                arity,
            }))
        }
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                funct,
                args,
                partial,
                transformed_jsx,
            } = *inner;
            let funct_expr = arena.get_expr(funct).clone();
            let transformed_funct = transform_expression(funct_expr, config, arena);
            ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: arena.push_expr(transformed_funct),
                args: args
                    .into_iter()
                    .map(|(lbl, e)| {
                        let e_expr = arena.get_expr(e).clone();
                        let transformed = transform_expression(e_expr, config, arena);
                        (lbl, arena.push_expr(transformed))
                    })
                    .collect(),
                partial,
                transformed_jsx,
            }))
        }
        ExpressionDesc::Pexp_match(inner) => {
            let (scrutinee, cases) = *inner;
            let scrutinee_expr = arena.get_expr(scrutinee).clone();
            let transformed_scrutinee = transform_expression(scrutinee_expr, config, arena);
            let transformed_cases = cases
                .into_iter()
                .map(|case| transform_case(case, config, arena))
                .collect();
            ExpressionDesc::Pexp_match(Box::new((
                arena.push_expr(transformed_scrutinee),
                transformed_cases,
            )))
        }
        ExpressionDesc::Pexp_try(inner) => {
            let (body, cases) = *inner;
            let body_expr = arena.get_expr(body).clone();
            let transformed_body = transform_expression(body_expr, config, arena);
            let transformed_cases = cases
                .into_iter()
                .map(|case| transform_case(case, config, arena))
                .collect();
            ExpressionDesc::Pexp_try(Box::new((
                arena.push_expr(transformed_body),
                transformed_cases,
            )))
        }
        ExpressionDesc::Pexp_tuple(exprs) => ExpressionDesc::Pexp_tuple(Box::new(
            exprs
                .into_iter()
                .map(|e| {
                    let e_expr = arena.get_expr(e).clone();
                    let transformed = transform_expression(e_expr, config, arena);
                    arena.push_expr(transformed)
                })
                .collect(),
        )),
        ExpressionDesc::Pexp_construct(lid, mut args) => {
            for e in args.txt.iter_mut() {
                let e_expr = arena.get_expr(*e).clone();
                let rw = transform_expression(e_expr, config, arena);
                *e = arena.push_expr(rw);
            }
            ExpressionDesc::Pexp_construct(lid, args)
        }
        ExpressionDesc::Pexp_variant(inner) => {
            let (label, mut args) = *inner;
            for e in args.txt.iter_mut() {
                let e_expr = arena.get_expr(*e).clone();
                let transformed = transform_expression(e_expr, config, arena);
                *e = arena.push_expr(transformed);
            }
            ExpressionDesc::Pexp_variant(Box::new((label, args)))
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, base) = *inner;
            let transformed_base = base.map(|e| {
                let e_expr = arena.get_expr(e).clone();
                let rw = transform_expression(e_expr, config, arena);
                arena.push_expr(rw)
            });
            ExpressionDesc::Pexp_record(Box::new((
                fields
                    .into_iter()
                    .map(|f| ExpressionRecordField {
                        lid: f.lid,
                        expr: {
                            let expr = arena.get_expr(f.expr).clone();
                            let transformed = transform_expression(expr, config, arena);
                            arena.push_expr(transformed)
                        },
                        opt: f.opt,
                    })
                    .collect(),
                transformed_base,
            )))
        }
        ExpressionDesc::Pexp_field(obj, field) => {
            let obj_expr = arena.get_expr(obj).clone();
            let transformed_obj = transform_expression(obj_expr, config, arena);
            ExpressionDesc::Pexp_field(arena.push_expr(transformed_obj), field)
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (obj, field, value) = *inner;
            let obj_expr = arena.get_expr(obj).clone();
            let value_expr = arena.get_expr(value).clone();
            let transformed_obj = transform_expression(obj_expr, config, arena);
            let transformed_value = transform_expression(value_expr, config, arena);
            ExpressionDesc::Pexp_setfield(Box::new((
                arena.push_expr(transformed_obj),
                field,
                arena.push_expr(transformed_value),
            )))
        }
        ExpressionDesc::Pexp_object_get(inner) => {
            let (obj, name) = *inner;
            let obj_expr = arena.get_expr(obj).clone();
            let transformed_obj = transform_expression(obj_expr, config, arena);
            ExpressionDesc::Pexp_object_get(Box::new((arena.push_expr(transformed_obj), name)))
        }
        ExpressionDesc::Pexp_object_set(inner) => {
            let (obj, name, value) = *inner;
            let value_expr = arena.get_expr(value).clone();
            let transformed_value = transform_expression(value_expr, config, arena);
            let value = arena.push_expr(transformed_value);
            let obj_expr = arena.get_expr(obj).clone();
            let transformed_obj = transform_expression(obj_expr, config, arena);
            ExpressionDesc::Pexp_object_set(Box::new((
                arena.push_expr(transformed_obj),
                name,
                value,
            )))
        }
        ExpressionDesc::Pexp_object_literal(fields) => {
            ExpressionDesc::Pexp_object_literal(Box::new(
                fields
                    .into_iter()
                    .map(|(name, e)| {
                        let e_expr = arena.get_expr(e).clone();
                        let transformed = transform_expression(e_expr, config, arena);
                        (name, arena.push_expr(transformed))
                    })
                    .collect(),
            ))
        }
        ExpressionDesc::Pexp_dict(entries) => ExpressionDesc::Pexp_dict(Box::new(
            entries
                .into_iter()
                .map(|entry| {
                    let mut transform = |e: ExprIdx| {
                        let e_expr = arena.get_expr(e).clone();
                        let transformed = transform_expression(e_expr, config, arena);
                        arena.push_expr(transformed)
                    };
                    match entry {
                        DictEntry::Pdict_entry(key, e) => DictEntry::Pdict_entry(key, transform(e)),
                        DictEntry::Pdict_spread(e) => DictEntry::Pdict_spread(transform(e)),
                    }
                })
                .collect(),
        )),
        ExpressionDesc::Pexp_array(elems) => ExpressionDesc::Pexp_array(Box::new(
            elems
                .into_iter()
                .map(|e| {
                    let e_expr = arena.get_expr(e).clone();
                    let transformed = transform_expression(e_expr, config, arena);
                    arena.push_expr(transformed)
                })
                .collect(),
        )),
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (cond, then_expr, else_expr) = *inner;
            let cond_expr = arena.get_expr(cond).clone();
            let then_expr_val = arena.get_expr(then_expr).clone();
            let transformed_cond = transform_expression(cond_expr, config, arena);
            let transformed_then = transform_expression(then_expr_val, config, arena);
            let transformed_else = else_expr.map(|e| {
                let else_expr_val = arena.get_expr(e).clone();
                let transformed = transform_expression(else_expr_val, config, arena);
                arena.push_expr(transformed)
            });
            ExpressionDesc::Pexp_ifthenelse(Box::new((
                arena.push_expr(transformed_cond),
                arena.push_expr(transformed_then),
                transformed_else,
            )))
        }
        ExpressionDesc::Pexp_ternary(inner) => {
            let (cond, consequent, alternate) = *inner;
            let cond = arena.get_expr(cond).clone();
            let consequent = arena.get_expr(consequent).clone();
            let alternate = arena.get_expr(alternate).clone();
            let cond = transform_expression(cond, config, arena);
            let consequent = transform_expression(consequent, config, arena);
            let alternate = transform_expression(alternate, config, arena);
            ExpressionDesc::Pexp_ternary(Box::new((
                arena.push_expr(cond),
                arena.push_expr(consequent),
                arena.push_expr(alternate),
            )))
        }
        ExpressionDesc::Pexp_braces(braces) => {
            let inner = arena.get_expr(braces.expr).clone();
            let inner = transform_expression(inner, config, arena);
            ExpressionDesc::Pexp_braces(Box::new(crate::parser::ast::PexpBraces {
                expr: arena.push_expr(inner),
                braces_loc: braces.braces_loc,
            }))
        }
        ExpressionDesc::Pexp_sequence(e1, e2) => {
            let e1_expr = arena.get_expr(e1).clone();
            let e2_expr = arena.get_expr(e2).clone();
            let t1 = transform_expression(e1_expr, config, arena);
            let t2 = transform_expression(e2_expr, config, arena);
            ExpressionDesc::Pexp_sequence(arena.push_expr(t1), arena.push_expr(t2))
        }
        ExpressionDesc::Pexp_while(cond, body) => {
            let cond_expr = arena.get_expr(cond).clone();
            let body_expr = arena.get_expr(body).clone();
            let tc = transform_expression(cond_expr, config, arena);
            let tb = transform_expression(body_expr, config, arena);
            ExpressionDesc::Pexp_while(arena.push_expr(tc), arena.push_expr(tb))
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (pat, start, end_, dir, body) = *inner;
            let start_expr = arena.get_expr(start).clone();
            let end_expr = arena.get_expr(end_).clone();
            let body_expr = arena.get_expr(body).clone();
            let transformed_start = transform_expression(start_expr, config, arena);
            let transformed_end = transform_expression(end_expr, config, arena);
            let transformed_body = transform_expression(body_expr, config, arena);
            ExpressionDesc::Pexp_for(Box::new((
                pat,
                arena.push_expr(transformed_start),
                arena.push_expr(transformed_end),
                dir,
                arena.push_expr(transformed_body),
            )))
        }
        ExpressionDesc::Pexp_for_of(inner) => {
            let (pat, iterable, body) = *inner;
            let iterable_expr = arena.get_expr(iterable).clone();
            let body_expr = arena.get_expr(body).clone();
            let transformed_iterable = transform_expression(iterable_expr, config, arena);
            let transformed_body = transform_expression(body_expr, config, arena);
            ExpressionDesc::Pexp_for_of(Box::new((
                pat,
                arena.push_expr(transformed_iterable),
                arena.push_expr(transformed_body),
            )))
        }
        ExpressionDesc::Pexp_for_await_of(inner) => {
            let (pat, iterable, body) = *inner;
            let iterable_expr = arena.get_expr(iterable).clone();
            let body_expr = arena.get_expr(body).clone();
            let transformed_iterable = transform_expression(iterable_expr, config, arena);
            let transformed_body = transform_expression(body_expr, config, arena);
            ExpressionDesc::Pexp_for_await_of(Box::new((
                pat,
                arena.push_expr(transformed_iterable),
                arena.push_expr(transformed_body),
            )))
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (inner_expr_idx, typ) = *inner;
            let inner_expr = arena.get_expr(inner_expr_idx).clone();
            let transformed = transform_expression(inner_expr, config, arena);
            ExpressionDesc::Pexp_constraint(Box::new((arena.push_expr(transformed), typ)))
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (inner_expr_idx, from_typ, to_typ) = *inner;
            let inner_expr = arena.get_expr(inner_expr_idx).clone();
            let transformed = transform_expression(inner_expr, config, arena);
            ExpressionDesc::Pexp_coerce(Box::new((arena.push_expr(transformed), from_typ, to_typ)))
        }
        ExpressionDesc::Pexp_extension(inner) => {
            let (name, payload) = *inner;
            let mut ignored_warnings = vec![];
            let payload = transform_payload(payload, config, arena, &mut ignored_warnings);
            ExpressionDesc::Pexp_extension(Box::new((name, payload)))
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (name, module_idx, body_idx) = *inner;
            let mut ignored_warnings = vec![];
            let module_expr = arena.get_mod_expr(module_idx).clone();
            let transformed_module =
                transform_module_expr(module_expr, config, arena, &mut ignored_warnings);
            let body_expr = arena.get_expr(body_idx).clone();
            let transformed_body = transform_expression(body_expr, config, arena);
            ExpressionDesc::Pexp_letmodule(Box::new((
                name,
                arena.push_mod_expr(transformed_module),
                arena.push_expr(transformed_body),
            )))
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (extension, body_idx) = *inner;
            let body_expr = arena.get_expr(body_idx).clone();
            let transformed_body = transform_expression(body_expr, config, arena);
            ExpressionDesc::Pexp_letexception(Box::new((
                extension,
                arena.push_expr(transformed_body),
            )))
        }
        ExpressionDesc::Pexp_assert(e) => {
            let e_expr = arena.get_expr(e).clone();
            let transformed = transform_expression(e_expr, config, arena);
            ExpressionDesc::Pexp_assert(arena.push_expr(transformed))
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (name, body_idx) = *inner;
            let body_expr = arena.get_expr(body_idx).clone();
            let transformed_body = transform_expression(body_expr, config, arena);
            ExpressionDesc::Pexp_newtype(Box::new((name, arena.push_expr(transformed_body))))
        }
        ExpressionDesc::Pexp_pack(mexpr) => {
            let mut ignored_warnings = vec![];
            let mexpr_val = arena.get_mod_expr(mexpr).clone();
            let transformed =
                transform_module_expr(mexpr_val, config, arena, &mut ignored_warnings);
            ExpressionDesc::Pexp_pack(arena.push_mod_expr(transformed))
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (override_flag, lid, inner_expr_idx) = *inner;
            let inner_expr = arena.get_expr(inner_expr_idx).clone();
            let transformed = transform_expression(inner_expr, config, arena);
            ExpressionDesc::Pexp_open(Box::new((override_flag, lid, arena.push_expr(transformed))))
        }
        ExpressionDesc::Pexp_await(e) => {
            let e_expr = arena.get_expr(e).clone();
            let transformed = transform_expression(e_expr, config, arena);
            ExpressionDesc::Pexp_await(arena.push_expr(transformed))
        }
        // Ast_mapper: `Pexp_template` maps its values; `Pexp_tagged_template`
        // maps the tag, then the values.
        ExpressionDesc::Pexp_template(mut template) => {
            template.values = template
                .values
                .into_iter()
                .map(|e| {
                    let e_expr = arena.get_expr(e).clone();
                    let transformed = transform_expression(e_expr, config, arena);
                    arena.push_expr(transformed)
                })
                .collect();
            ExpressionDesc::Pexp_template(template)
        }
        ExpressionDesc::Pexp_tagged_template(mut template) => {
            let tag_expr = arena.get_expr(template.tag).clone();
            let tag = transform_expression(tag_expr, config, arena);
            template.tag = arena.push_expr(tag);
            template.values = template
                .values
                .into_iter()
                .map(|e| {
                    let e_expr = arena.get_expr(e).clone();
                    let transformed = transform_expression(e_expr, config, arena);
                    arena.push_expr(transformed)
                })
                .collect();
            ExpressionDesc::Pexp_tagged_template(template)
        }
        other => other,
    };

    Expression {
        pexp_desc: Box::new(new_desc),
        pexp_loc: expr.pexp_loc,
        pexp_attributes: expr.pexp_attributes,
    }
}

fn transform_case(case: Case, config: &mut JsxConfig, arena: &mut ParseArena) -> Case {
    let transformed_guard = case.pc_guard.map(|e| {
        let e_expr = arena.get_expr(e).clone();
        let transformed = transform_expression(e_expr, config, arena);
        arena.push_expr(transformed)
    });
    let transformed_rhs = {
        let rhs_expr = arena.get_expr(case.pc_rhs).clone();
        let transformed = transform_expression(rhs_expr, config, arena);
        arena.push_expr(transformed)
    };
    Case {
        pc_bar: case.pc_bar,
        pc_lhs: case.pc_lhs,
        pc_guard: transformed_guard,
        pc_rhs: transformed_rhs,
    }
}

// ============================================================================
// JSX Element Transformation
// ============================================================================

fn transform_jsx_element(
    jsx: JsxElement,
    config: &mut JsxConfig,
    loc: &Location,
    attrs: &Attributes,
    arena: &mut ParseArena,
) -> ExpressionDesc {
    match jsx {
        JsxElement::Fragment(fragment) => {
            transform_jsx_fragment(fragment, config, loc, attrs, arena)
        }
        JsxElement::Unary(unary) => transform_jsx_unary(unary, config, loc, attrs, arena),
        JsxElement::Container(container) => {
            transform_jsx_container(container, config, loc, attrs, arena)
        }
    }
}

/// Main JSX transformation function - matches OCaml's mk_react_jsx
fn mk_react_jsx(
    config: &mut JsxConfig,
    loc: &Location,
    _attrs: &Attributes,
    component_description: ComponentDescription,
    element_tag: Expression,
    props: Vec<JsxProp>,
    children: Vec<ExprIdx>,
    arena: &mut ParseArena,
) -> ExpressionDesc {
    let more_than_one_children = children.len() > 1;

    // Append children prop
    let props_with_children = append_children_prop(
        config,
        component_description,
        props,
        children.clone(),
        arena,
    );

    // Create the props record (filtering out key)
    let props_record = mk_record_from_props(loc, &props_with_children, config, arena);

    // Determine jsx function and key handling
    let key_prop = try_find_key_prop(arena, &props_with_children);

    let (jsx_expr, key_and_unit) = {
        let jsx_part = match &key_prop {
            Some(_) => {
                if more_than_one_children {
                    "jsxsKeyed"
                } else {
                    "jsxKeyed"
                }
            }
            None => {
                if more_than_one_children {
                    "jsxs"
                } else {
                    "jsx"
                }
            }
        };

        let jsx_path = match component_description {
            ComponentDescription::FragmentComponent | ComponentDescription::UppercasedComponent => {
                module_access_name(arena, config, jsx_part)
            }
            ComponentDescription::LowercasedComponent => {
                let element_binding = if config.module_name.to_lowercase() == "react" {
                    let react_dom_idx = arena.intern_string("ReactDOM");
                    Longident::Lident(react_dom_idx)
                } else {
                    let elements_idx = arena.intern_string("Elements");
                    let module_path = jsx_module_longident(arena, config);
                    Longident::Ldot(Box::new(module_path), elements_idx)
                };
                let jsx_part_idx = arena.intern_string(jsx_part);
                arena.push_longident(Longident::Ldot(Box::new(element_binding), jsx_part_idx))
            }
        };

        let jsx_expr = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                txt: jsx_path,
                loc: empty_loc(),
            })),
            pexp_loc: empty_loc(),
            pexp_attributes: Attributes::new(),
        };

        let key_and_unit: Vec<(ArgLabel, ExprIdx)> = match key_prop {
            Some((label, expr)) => {
                let unit = unit_expr(arena, &empty_loc());
                let unit_idx = arena.push_expr(unit);
                vec![(label, expr), (ArgLabel::Nolabel, unit_idx)]
            }
            None => vec![],
        };

        (jsx_expr, key_and_unit)
    };

    let mut args = vec![
        (ArgLabel::Nolabel, arena.push_expr(element_tag)),
        (ArgLabel::Nolabel, arena.push_expr(props_record)),
    ];
    args.extend(key_and_unit);

    // Note: jsx_expr uses empty_loc() for ghost locations - don't overwrite it
    // The attributes go on the outer Pexp_apply, not on the jsx function ident
    let jsx_expr_idx = arena.push_expr(jsx_expr);
    ExpressionDesc::Pexp_apply(Box::new(PexpApply {
        funct: jsx_expr_idx,
        args,
        partial: false,
        transformed_jsx: true,
    }))
}

/// Append children prop to props list - matches OCaml's append_children_prop
fn append_children_prop(
    config: &mut JsxConfig,
    component_description: ComponentDescription,
    mut props: Vec<JsxProp>,
    children: Vec<ExprIdx>,
    arena: &mut ParseArena,
) -> Vec<JsxProp> {
    if children.is_empty() {
        return props;
    }

    if children.len() == 1 {
        let child = children.into_iter().next().unwrap();
        let child_expr = arena.get_expr(child).clone();
        let transformed_child = transform_expression(child_expr, config, arena);

        // For lowercase components, wrap in ReactDOM.someElement
        let expr = match component_description {
            ComponentDescription::FragmentComponent | ComponentDescription::UppercasedComponent => {
                transformed_child
            }
            ComponentDescription::LowercasedComponent => {
                let element_binding = if config.module_name.to_lowercase() == "react" {
                    let react_dom_idx = arena.intern_string("ReactDOM");
                    Longident::Lident(react_dom_idx)
                } else {
                    let elements_idx = arena.intern_string("Elements");
                    let module_path = jsx_module_longident(arena, config);
                    Longident::Ldot(Box::new(module_path), elements_idx)
                };
                let some_element_idx = arena.intern_string("someElement");
                let some_element_path = arena
                    .push_longident(Longident::Ldot(Box::new(element_binding), some_element_idx));

                // OCaml: Exp.apply without ~loc uses Location.none (default_loc = ref Location.none)
                let funct_idx = arena.push_expr(Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                        txt: some_element_path,
                        loc: empty_loc(),
                    })),
                    pexp_loc: empty_loc(),
                    pexp_attributes: Attributes::new(),
                });
                Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                        funct: funct_idx,
                        args: vec![(ArgLabel::Nolabel, arena.push_expr(transformed_child))],
                        partial: false,
                        transformed_jsx: false,
                    }))),
                    pexp_loc: empty_loc(), // OCaml: Exp.apply without ~loc defaults to Location.none
                    pexp_attributes: Attributes::new(),
                }
            }
        };

        // Children is optional for lowercase components
        let is_optional = matches!(
            component_description,
            ComponentDescription::LowercasedComponent
        );
        let children_str_idx = arena.intern_string("children");

        props.push(JsxProp::Value {
            name: Loc {
                txt: children_str_idx,
                loc: arena.get_expr(child).pexp_loc,
            },
            optional: is_optional,
            value: arena.push_expr(expr),
        });
    } else {
        // Multiple children: wrap in Module.array([...])
        // OCaml uses real location spanning all children for outer expressions but ghost for inner synthesized ones
        let loc = if let (Some(first), Some(last)) = (children.first(), children.last()) {
            // Create composite location spanning from first child start to last child end
            let start_idx = arena.loc_start_idx(arena.get_expr(*first).pexp_loc);
            let end_idx = arena.loc_end_idx(arena.get_expr(*last).pexp_loc);
            arena.mk_loc(start_idx, end_idx)
        } else {
            empty_loc()
        };

        // React.array function - uses ghost location for ident, real loc for outer expr
        let array_fn = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                txt: module_access_name(arena, config, "array"),
                loc, // OCaml uses the children loc for the longident
            })),
            pexp_loc: empty_loc(), // Ghost location for the ident expression itself
            pexp_attributes: Attributes::new(),
        };

        // Array literal containing children - ghost location
        let children_array = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_array(Box::new(
                children
                    .into_iter()
                    .map(|c| {
                        let c_expr = arena.get_expr(c).clone();
                        let transformed = transform_expression(c_expr, config, arena);
                        arena.push_expr(transformed)
                    })
                    .collect(),
            ))),
            pexp_loc: empty_loc(), // Ghost location for the array
            pexp_attributes: Attributes::new(),
        };

        let array_fn_idx = arena.push_expr(array_fn);
        let children_expr = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: array_fn_idx,
                args: vec![(ArgLabel::Nolabel, arena.push_expr(children_array))],
                partial: false,
                transformed_jsx: false,
            }))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        };

        let children_str_idx = arena.intern_string("children");
        props.push(JsxProp::Value {
            name: Loc {
                txt: children_str_idx,
                loc,
            },
            optional: false,
            value: arena.push_expr(children_expr),
        });
    }

    props
}

/// Get location from a JSX prop
fn loc_from_prop(prop: &JsxProp, arena: &mut ParseArena) -> Location {
    match prop {
        JsxProp::Punning { name, .. } => name.loc,
        JsxProp::Value { name, value, .. } => {
            // Location spans from name start to value end
            let start_idx = arena.loc_start_idx(name.loc);
            let end_idx = arena.loc_end_idx(arena.get_expr(*value).pexp_loc);
            arena.mk_loc(start_idx, end_idx)
        }
        JsxProp::Spreading { loc, .. } => *loc,
    }
}

/// Create props record from JSX props - matches OCaml's mk_record_from_props
fn mk_record_from_props(
    jsx_expr_loc: &Location,
    props: &[JsxProp],
    config: &mut JsxConfig,
    arena: &mut ParseArena,
) -> Expression {
    // Calculate location from ALL props (including key) - OCaml does this before filtering
    let loc = if props.is_empty() {
        *jsx_expr_loc
    } else {
        let first = loc_from_prop(&props[0], arena);
        let last = loc_from_prop(props.last().unwrap(), arena);
        // Create composite location from first to last
        let start_idx = arena.loc_start_idx(first);
        let end_idx = arena.loc_end_idx(last);
        arena.mk_loc(start_idx, end_idx)
    };

    // Filter out key prop AFTER calculating location
    let props: Vec<&JsxProp> = props
        .iter()
        .filter(|p| match p {
            JsxProp::Punning { name, .. } | JsxProp::Value { name, .. } => {
                arena.get_string(name.txt) != "key"
            }
            JsxProp::Spreading { .. } => true,
        })
        .collect();

    // Handle spread props - must be first if present
    let (regular_props, spread_base) = {
        let mut props_iter = props.into_iter().peekable();
        let spread_base = if let Some(JsxProp::Spreading { expr, .. }) = props_iter.peek() {
            let spread = transform_expression(arena.get_expr(*expr).clone(), config, arena);
            props_iter.next(); // consume the spread
            Some(arena.push_expr(spread))
        } else {
            None
        };

        let regular: Vec<_> = props_iter.collect();
        (regular, spread_base)
    };

    // Build record fields
    let record_fields: Vec<ExpressionRecordField> = regular_props
        .into_iter()
        .filter_map(|prop| {
            match prop {
                JsxProp::Punning { optional, name } => {
                    // name.txt is already a StrIdx, use it directly
                    let name_str_idx = name.txt;
                    let name_lid = arena.push_longident(Longident::Lident(name_str_idx));
                    Some(ExpressionRecordField {
                        lid: Loc {
                            txt: name_lid,
                            loc: name.loc,
                        },
                        expr: arena.push_expr(Expression {
                            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                                txt: name_lid,
                                loc: name.loc,
                            })),
                            pexp_loc: name.loc,
                            pexp_attributes: Attributes::new(),
                        }),
                        opt: *optional,
                    })
                }
                JsxProp::Value {
                    name,
                    optional,
                    value,
                } => {
                    // name.txt is already a StrIdx, use it directly
                    let name_str_idx = name.txt;
                    Some(ExpressionRecordField {
                        lid: Loc {
                            txt: arena.push_longident(Longident::Lident(name_str_idx)),
                            loc: name.loc,
                        },
                        expr: {
                            let value = arena.get_expr(*value).clone();
                            let transformed = transform_expression(value, config, arena);
                            arena.push_expr(transformed)
                        },
                        opt: *optional,
                    })
                }
                JsxProp::Spreading { loc, .. } => {
                    set_fatal_error(config, *loc, JSX_SPREAD_AFTER_PROP_MSG);
                    None
                }
            }
        })
        .collect();

    // Handle empty record with spread
    match (&record_fields[..], &spread_base) {
        ([], Some(spread_idx)) => {
            let spread_expr = arena.get_expr(*spread_idx).clone();
            Expression {
                pexp_desc: spread_expr.pexp_desc,
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        _ => Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((
                record_fields,
                spread_base,
            )))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        },
    }
}

fn transform_jsx_fragment(
    fragment: JsxFragment,
    config: &mut JsxConfig,
    loc: &Location,
    attrs: &Attributes,
    arena: &mut ParseArena,
) -> ExpressionDesc {
    let children = fragment.children;

    // Fragment expression: React.jsxFragment (or Module.jsxFragment)
    let fragment_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
            txt: module_access_name(arena, config, "jsxFragment"),
            loc: *loc,
        })),
        pexp_loc: *loc,
        pexp_attributes: Attributes::new(),
    };

    // Use mk_react_jsx to handle the full transformation
    mk_react_jsx(
        config,
        loc,
        attrs,
        ComponentDescription::FragmentComponent,
        fragment_expr,
        vec![], // No props for fragments
        children,
        arena,
    )
}

fn transform_jsx_unary(
    unary: JsxUnaryElement,
    config: &mut JsxConfig,
    loc: &Location,
    attrs: &Attributes,
    arena: &mut ParseArena,
) -> ExpressionDesc {
    let tag_loc = &unary.tag_name.loc;
    match &unary.tag_name.txt {
        JsxTagName::Lower(name) => {
            // Lowercase element like <div />
            let component_name_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(Constant::string(
                    name,
                )))),
                pexp_loc: *tag_loc,
                pexp_attributes: Attributes::new(),
            };
            mk_react_jsx(
                config,
                loc,
                attrs,
                ComponentDescription::LowercasedComponent,
                component_name_expr,
                unary.props,
                vec![],
                arena,
            )
        }
        JsxTagName::Upper(path) => {
            // Uppercase element like <MyModule /> -> MyModule.make
            let make_str_idx = arena.intern_string("make");
            let make_id = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                    txt: arena.push_longident(Longident::Ldot(
                        Box::new(arena.get_longident(*path).clone()),
                        make_str_idx,
                    )),
                    loc: *tag_loc,
                })),
                pexp_loc: *tag_loc,
                pexp_attributes: Attributes::new(),
            };
            mk_react_jsx(
                config,
                loc,
                attrs,
                ComponentDescription::UppercasedComponent,
                make_id,
                unary.props,
                vec![],
                arena,
            )
        }
        JsxTagName::QualifiedLower { path, name } => {
            // Qualified lowercase like <MyModule.lowercase /> -> MyModule.lowercase
            let name_str_idx = arena.push_interned_string(name);
            let make_id = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                    txt: arena.push_longident(Longident::Ldot(
                        Box::new(arena.get_longident(*path).clone()),
                        name_str_idx,
                    )),
                    loc: *tag_loc,
                })),
                pexp_loc: *tag_loc,
                pexp_attributes: Attributes::new(),
            };
            mk_react_jsx(
                config,
                loc,
                attrs,
                ComponentDescription::UppercasedComponent,
                make_id,
                unary.props,
                vec![],
                arena,
            )
        }
        JsxTagName::Invalid(name) => {
            set_fatal_error(
                config,
                *loc,
                &format!(
                    "JSX: element name is neither upper- or lowercase, got \"{}\"",
                    name
                ),
            );
            ExpressionDesc::Pexp_jsx_element(Box::new(JsxElement::Unary(unary)))
        }
    }
}

fn transform_jsx_container(
    container: JsxContainerElement,
    config: &mut JsxConfig,
    loc: &Location,
    attrs: &Attributes,
    arena: &mut ParseArena,
) -> ExpressionDesc {
    let tag_loc = &container.tag_name_start.loc;
    match &container.tag_name_start.txt {
        JsxTagName::Lower(name) => {
            // Lowercase element like <div>...</div>
            let component_name_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(Constant::string(
                    name,
                )))),
                pexp_loc: *tag_loc,
                pexp_attributes: Attributes::new(),
            };
            mk_react_jsx(
                config,
                loc,
                attrs,
                ComponentDescription::LowercasedComponent,
                component_name_expr,
                container.props,
                container.children,
                arena,
            )
        }
        JsxTagName::Upper(path) => {
            // Uppercase element like <MyModule>...</MyModule> -> MyModule.make
            let make_str_idx = arena.intern_string("make");
            let make_id = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                    txt: arena.push_longident(Longident::Ldot(
                        Box::new(arena.get_longident(*path).clone()),
                        make_str_idx,
                    )),
                    loc: *tag_loc,
                })),
                pexp_loc: *tag_loc,
                pexp_attributes: Attributes::new(),
            };
            mk_react_jsx(
                config,
                loc,
                attrs,
                ComponentDescription::UppercasedComponent,
                make_id,
                container.props,
                container.children,
                arena,
            )
        }
        JsxTagName::QualifiedLower { path, name } => {
            // Qualified lowercase like <MyModule.lowercase>...</MyModule.lowercase>
            let name_str_idx = arena.push_interned_string(name);
            let make_id = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc {
                    txt: arena.push_longident(Longident::Ldot(
                        Box::new(arena.get_longident(*path).clone()),
                        name_str_idx,
                    )),
                    loc: *tag_loc,
                })),
                pexp_loc: *tag_loc,
                pexp_attributes: Attributes::new(),
            };
            mk_react_jsx(
                config,
                loc,
                attrs,
                ComponentDescription::UppercasedComponent,
                make_id,
                container.props,
                container.children,
                arena,
            )
        }
        JsxTagName::Invalid(name) => {
            set_fatal_error(
                config,
                *loc,
                &format!(
                    "JSX: element name is neither upper- or lowercase, got \"{}\"",
                    name
                ),
            );
            ExpressionDesc::Pexp_jsx_element(Box::new(JsxElement::Container(container)))
        }
    }
}

/// Whether `transform_expression` may rewrite `expr` or its subtree: it
/// contains a JSX element, a module expression (whose structure items get the
/// component transform), or a construct this check does not inspect.
fn expression_may_change(expr: &Expression, arena: &ParseArena, memo: &mut Vec<u8>) -> bool {
    let child = |idx: ExprIdx, memo: &mut Vec<u8>| subtree_may_change(idx, arena, memo);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue => false,
        ExpressionDesc::Pexp_let(inner) => {
            inner.1.iter().any(|binding| child(binding.pvb_expr, memo)) || child(inner.2, memo)
        }
        ExpressionDesc::Pexp_fun(inner) => {
            inner.default.is_some_and(|default| child(default, memo)) || child(inner.rhs, memo)
        }
        ExpressionDesc::Pexp_apply(inner) => {
            child(inner.funct, memo) || inner.args.iter().any(|(_, arg)| child(*arg, memo))
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            child(inner.0, memo)
                || inner.1.iter().any(|case| {
                    case.pc_guard.is_some_and(|guard| child(guard, memo))
                        || child(case.pc_rhs, memo)
                })
        }
        ExpressionDesc::Pexp_template(template) => {
            template.values.iter().any(|item| child(*item, memo))
        }
        ExpressionDesc::Pexp_tagged_template(template) => {
            child(template.tag, memo) || template.values.iter().any(|item| child(*item, memo))
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            items.iter().any(|item| child(*item, memo))
        }
        ExpressionDesc::Pexp_dict(entries) => entries.iter().any(|entry| match entry {
            DictEntry::Pdict_entry(_, e) | DictEntry::Pdict_spread(e) => child(*e, memo),
        }),
        ExpressionDesc::Pexp_construct(_, args) => args.txt.iter().any(|arg| child(*arg, memo)),
        ExpressionDesc::Pexp_variant(inner) => inner.1.txt.iter().any(|arg| child(*arg, memo)),
        ExpressionDesc::Pexp_record(inner) => {
            inner.0.iter().any(|field| child(field.expr, memo))
                || inner.1.is_some_and(|spread| child(spread, memo))
        }
        ExpressionDesc::Pexp_field(target, _) => child(*target, memo),
        ExpressionDesc::Pexp_setfield(inner) => child(inner.0, memo) || child(inner.2, memo),
        ExpressionDesc::Pexp_object_get(inner) => child(inner.0, memo),
        ExpressionDesc::Pexp_object_set(inner) => child(inner.0, memo) || child(inner.2, memo),
        ExpressionDesc::Pexp_object_literal(fields) => fields.iter().any(|(_, e)| child(*e, memo)),
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            child(inner.0, memo)
                || child(inner.1, memo)
                || inner.2.is_some_and(|else_| child(else_, memo))
        }
        ExpressionDesc::Pexp_ternary(inner) => {
            child(inner.0, memo) || child(inner.1, memo) || child(inner.2, memo)
        }
        ExpressionDesc::Pexp_braces(braces) => child(braces.expr, memo),
        ExpressionDesc::Pexp_regexp(_) => false,
        ExpressionDesc::Pexp_sequence(first, second)
        | ExpressionDesc::Pexp_while(first, second) => child(*first, memo) || child(*second, memo),
        ExpressionDesc::Pexp_for(inner) => {
            child(inner.1, memo) || child(inner.2, memo) || child(inner.4, memo)
        }
        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            child(inner.1, memo) || child(inner.2, memo)
        }
        ExpressionDesc::Pexp_constraint(inner) => child(inner.0, memo),
        ExpressionDesc::Pexp_coerce(inner) => child(inner.0, memo),
        ExpressionDesc::Pexp_letexception(inner) => child(inner.1, memo),
        ExpressionDesc::Pexp_assert(inner) | ExpressionDesc::Pexp_await(inner) => {
            child(*inner, memo)
        }
        ExpressionDesc::Pexp_newtype(inner) => child(inner.1, memo),
        ExpressionDesc::Pexp_open(inner) => child(inner.2, memo),
        ExpressionDesc::Pexp_jsx_element(_)
        | ExpressionDesc::Pexp_letmodule(_)
        | ExpressionDesc::Pexp_pack(_)
        | ExpressionDesc::Pexp_extension(_)
        | ExpressionDesc::Pexp_raw(_) => true,
    }
}

fn subtree_may_change(idx: ExprIdx, arena: &ParseArena, memo: &mut Vec<u8>) -> bool {
    let slot = idx.0 as usize;
    if let Some(&known) = memo.get(slot)
        && known != 0
    {
        return known == 2;
    }
    let may_change = expression_may_change(arena.get_expr(idx), arena, memo);
    if slot >= memo.len() {
        memo.resize(slot + 1, 0);
    }
    memo[slot] = if may_change { 2 } else { 1 };
    may_change
}

#[cfg(test)]
mod tests {
    use super::{JsxConfig, module_access_name, transform_structure_result};
    use crate::parser::{ExpressionDesc, Longident, Parser, StructureItemDesc, module, sexp_locs};

    #[test]
    fn parses_dotted_custom_jsx_module_paths() {
        let mut parser = Parser::new("test.res".to_string(), "");
        let config = JsxConfig {
            module_name: "BaseUi.BaseUiJsxDOM".to_string(),
            ..JsxConfig::default()
        };

        let path = module_access_name(parser.arena_mut(), &config, "jsx");
        let Longident::Ldot(module_path, jsx_name) = parser.arena().get_longident(path) else {
            panic!("expected a qualified JSX access path");
        };
        assert_eq!(parser.arena().get_string(*jsx_name), "jsx");
        let Longident::Ldot(base_ui, runtime_name) = module_path.as_ref() else {
            panic!("expected the configured JSX module to remain qualified");
        };
        assert_eq!(parser.arena().get_string(*runtime_name), "BaseUiJsxDOM");
        let Longident::Lident(base_ui_name) = base_ui.as_ref() else {
            panic!("expected BaseUi to be the JSX module root");
        };
        assert_eq!(parser.arena().get_string(*base_ui_name), "BaseUi");
    }

    #[test]
    fn wraps_generated_component_with_component_identity() {
        let source = r#"
@react.component
let make = (~value: string) => React.null
"#;

        let mut parser = Parser::new("test.res".to_string(), source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let transformed =
            transform_structure_result(structure, 4, "react", parser.arena_mut()).unwrap();

        let StructureItemDesc::Pstr_value(value) = &*transformed
            .last()
            .expect("expected generated component binding")
            .pstr_desc
        else {
            panic!("expected generated value binding");
        };
        let (_, bindings) = &**value;
        let ExpressionDesc::Pexp_apply(apply) =
            &*parser.arena().get_expr(bindings[0].pvb_expr).pexp_desc
        else {
            panic!("expected generated binding to apply React.component");
        };
        let ExpressionDesc::Pexp_ident(component) =
            &*parser.arena().get_expr(apply.funct).pexp_desc
        else {
            panic!("expected component identity function");
        };
        let Longident::Ldot(module, component_name) = parser.arena().get_longident(component.txt)
        else {
            panic!("expected qualified component identity function");
        };
        let Longident::Lident(module_name) = module.as_ref() else {
            panic!("expected React module");
        };
        assert_eq!(parser.arena().get_string(*module_name), "React");
        assert_eq!(parser.arena().get_string(*component_name), "component");
    }

    #[test]
    fn keeps_labelled_wildcard_component_props() {
        let source = r#"
@react.component
let make = (~priority as _, ~text="Test") => React.string(text)
"#;

        let mut parser = Parser::new("test.res".to_string(), source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let transformed =
            transform_structure_result(structure, 4, "react", parser.arena_mut()).unwrap();

        let mut output = Vec::new();
        sexp_locs::print_structure(&transformed, parser.arena(), &mut output);
        let output = String::from_utf8(output).expect("sexp should be valid utf8");
        assert!(
            output.contains("priority"),
            "missing wildcard prop:\n{output}"
        );
        assert!(output.contains("text"), "missing defaulted prop:\n{output}");
    }

    #[test]
    fn transforms_jsx_inside_functor_module_body() {
        let source = r#"
module MakePreset = (Preset: { let value: int }) => {
  @react.component
  let make = (~children=?) => {
    <Div>{children->Option.getOr(React.null)}</Div>
  }
}
"#;

        let mut parser = Parser::new("test.res".to_string(), source);
        let structure = module::parse_structure(&mut parser);
        assert!(
            !parser.has_errors(),
            "parse failed with {} errors",
            parser.diagnostics().len()
        );

        let mut before = Vec::new();
        sexp_locs::print_structure(&structure, parser.arena(), &mut before);
        let before = String::from_utf8(before).expect("sexp should be valid utf8");
        assert!(
            before.contains("Pexp_jsx"),
            "expected JSX nodes before transform, got:\n{}",
            before
        );

        let transformed =
            transform_structure_result(structure, 4, "react", parser.arena_mut()).unwrap();

        let mut after = Vec::new();
        sexp_locs::print_structure(&transformed, parser.arena(), &mut after);
        let after = String::from_utf8(after).expect("sexp should be valid utf8");
        assert!(
            !after.contains("Pexp_jsx"),
            "expected no JSX nodes after transform, got:\n{}",
            after
        );
    }
}
