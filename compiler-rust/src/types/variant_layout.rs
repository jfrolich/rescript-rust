//! Runtime shapes and canonical layouts of type declarations.
//!
//! Port of `compiler/ml/variant_layout.ml` together with the runtime
//! annotation part of `compiler/ml/ast_untagged_variants.ml`
//! (`process_runtime_annotation`, `check_runtime_annotation`,
//! `unsupported_class`, `is_class_path`) and `Typedecl.check_manifest_annotation`.
//!
//! A declaration's `@notUndefined`, `@instanceOf` or `@typeOf` is resolved
//! once, when the type is declared, into its `type_shape`
//! ([`resolve_shapes`], [`declaration_shape`]). Readers take the shape of the
//! first type on an expansion chain that states one ([`value_shape`]).

use crate::ident::Ident;
use crate::location::Location;
use crate::types::PrivateFlag;
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorArguments, ConstructorDeclaration, RecordRepresentation, TypeDeclaration, TypeKind,
};
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::type_expr::{TypeDesc, TypeExprRef};
use crate::types::typemod::{AstUntaggedVariantError, TypeModError, TypeModResult};
use crate::types::variant_runtime::{
    Block, BlockType, ClassBlocks, Configuration, ConstructorCase, Instance, Layout, LiteralTag,
    ShapeAllocation, ShapeBlocks, ShapeString, Tag, TaggedBlock, ValueShape,
};

/// ast_untagged_variants.ml `runtime_annotation`: what `@notUndefined`,
/// `@instanceOf` or `@typeOf` on a type declaration states about the runtime
/// representation of its values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RuntimeAnnotation {
    /// Values that are never `undefined`.
    NotUndefined,
    /// Instances of the global class at this path.
    InstanceOf(String),
    /// Values with this `typeof`.
    TypeOf(BlockType),
}

const NOT_UNDEFINED: &str = "notUndefined";
const INSTANCE_OF: &str = "instanceOf";
const TYPE_OF: &str = "typeOf";
/// On a type with `@instanceOf`: the module the class is imported from.
const MODULE: &str = "module";
/// On a private record with `@instanceOf`: `@extends(: parent)` names its
/// superclass.
pub(crate) const EXTENDS: &str = "extends";

/// What kind of declaration a runtime annotation is written on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AnnotatedKind {
    /// An abstract type or a type abbreviation: every annotation.
    AbstractOrAbbreviation,
    /// A private record: `@instanceOf`, with `@extends`. Only its module
    /// builds its values, so a record literal cannot pass for an instance.
    PrivateRecord,
    /// A record anyone can build.
    PublicRecord,
    /// A variant or an open type.
    Other,
}

/// ast_untagged_variants.ml `unsupported_class`: why a syntactically valid
/// `@instanceOf` path is still not accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnsupportedClass {
    ThroughGlobalThis,
    /// Names the `@typeOf` that says the same.
    EveryValueOf(&'static str),
    /// Names the `@typeOf` of the wrapped primitive.
    WrapperOf(&'static str),
    ArrayClass,
    NotAClass,
}

/// ast_untagged_variants.ml `unsupported_class`. Classes nested in
/// namespaces, such as `Intl.Locale`, are not checked.
fn unsupported_class(name: &str) -> Option<UnsupportedClass> {
    let segments: Vec<&str> = name.split('.').collect();
    match segments.as_slice() {
        ["globalThis", _, ..] => Some(UnsupportedClass::ThroughGlobalThis),
        [global] => match *global {
            "Object" => Some(UnsupportedClass::EveryValueOf("object")),
            "Function" => Some(UnsupportedClass::EveryValueOf("function")),
            "Array" => Some(UnsupportedClass::ArrayClass),
            "String" => Some(UnsupportedClass::WrapperOf("string")),
            "Number" => Some(UnsupportedClass::WrapperOf("number")),
            "Boolean" => Some(UnsupportedClass::WrapperOf("boolean")),
            "BigInt" => Some(UnsupportedClass::WrapperOf("bigint")),
            "Symbol" => Some(UnsupportedClass::WrapperOf("symbol")),
            "globalThis" | "undefined" | "NaN" | "Infinity" | "Math" | "JSON" | "Reflect"
            | "Atomics" | "Intl" | "Proxy" => Some(UnsupportedClass::NotAClass),
            _ => None,
        },
        _ => None,
    }
}

/// ast_untagged_variants.ml `is_class_path`: a dot-separated list of
/// identifiers whose first one is not a JavaScript keyword. Properties may be
/// named like keywords.
fn is_class_path(name: &str) -> bool {
    fn is_start(c: u8) -> bool {
        c.is_ascii_alphabetic() || c == b'_' || c == b'$'
    }
    fn is_identifier(segment: &str) -> bool {
        let bytes = segment.as_bytes();
        !bytes.is_empty()
            && is_start(bytes[0])
            && bytes.iter().all(|c| c.is_ascii_digit() || is_start(*c))
    }
    let mut segments = name.split('.');
    match segments.next() {
        Some(global) => {
            is_identifier(global)
                && !crate::js_ir::printer::is_js_keyword(global)
                && segments.all(is_identifier)
        }
        None => false,
    }
}

pub(crate) fn runtime_attribute_name(annotation: &RuntimeAnnotation) -> &'static str {
    match annotation {
        RuntimeAnnotation::NotUndefined => NOT_UNDEFINED,
        RuntimeAnnotation::InstanceOf(_) => INSTANCE_OF,
        RuntimeAnnotation::TypeOf(_) => TYPE_OF,
    }
}

/// ast_untagged_variants.ml `typeof_name`: a `@typeOf` states one of the
/// kinds `typeof` recognizes.
fn typeof_name(block_type: &BlockType) -> &'static str {
    block_type.typeof_name().unwrap_or("object")
}

/// ast_untagged_variants.ml `runtime_annotation_to_string`.
fn runtime_annotation_to_string(annotation: &RuntimeAnnotation) -> String {
    match annotation {
        RuntimeAnnotation::NotUndefined => format!("@{NOT_UNDEFINED}"),
        RuntimeAnnotation::InstanceOf(name) => format!("@{INSTANCE_OF}(\"{name}\")"),
        RuntimeAnnotation::TypeOf(block_type) => {
            format!("@{TYPE_OF}(\"{}\")", typeof_name(block_type))
        }
    }
}

/// ast_untagged_variants.ml `describe_declared_values`: what a
/// declaration's annotations state about its values, for error messages.
pub(crate) fn describe_declared_values(block_type: Option<&BlockType>) -> String {
    match block_type {
        Some(BlockType::Instance(Instance::Class {
            name, ancestors, ..
        })) if ancestors.is_empty() => {
            format!("instances of {name}")
        }
        Some(BlockType::Instance(Instance::Class {
            name, ancestors, ..
        })) => {
            format!(
                "instances of {name}, a subclass of {}",
                ancestors.join(" and ")
            )
        }
        Some(BlockType::Instance(Instance::Array(_))) => "arrays".to_string(),
        Some(block_type) => format!("typeof \"{}\"", typeof_name(block_type)),
        None => "no stated class or typeof".to_string(),
    }
}

/// One attribute as `process_runtime_annotation` reads it: its name, the
/// semantic string of its payload, and the location of its name.
pub(crate) struct AnnotationAttribute<'a> {
    pub name: &'a str,
    /// `Ast_payload.semantic_string_of_payload`, or the location of the
    /// template it raises on.
    pub semantic: Result<Option<String>, Location>,
    pub loc: Location,
}

pub(crate) type AnnotationResult<T> = Result<T, AnnotationError>;

/// An error `process_runtime_annotation` raises.
pub(crate) enum AnnotationError {
    /// `Ast_untagged_variants.Error`.
    Untagged(Location, AstUntaggedVariantError),
    /// `Ast_payload.semantic_string_of_payload` on a template with an
    /// invalid escape.
    InvalidStringEscape(Location),
}

impl From<(Location, AstUntaggedVariantError)> for AnnotationError {
    fn from((loc, error): (Location, AstUntaggedVariantError)) -> Self {
        AnnotationError::Untagged(loc, error)
    }
}

/// ast_untagged_variants.ml `process_runtime_annotation`: the
/// `@notUndefined`, `@instanceOf` or `@typeOf` annotation among `attrs`,
/// validated. An attribute without a location is reported at `loc`.
pub(crate) fn process_runtime_annotation<'a>(
    attrs: impl IntoIterator<Item = AnnotationAttribute<'a>>,
    loc: Location,
) -> AnnotationResult<Option<RuntimeAnnotation>> {
    let mut annotations = Vec::new();
    for attr in attrs {
        let attr_loc = if attr.loc.is_none() { loc } else { attr.loc };
        let annotation = if attr.name == NOT_UNDEFINED {
            RuntimeAnnotation::NotUndefined
        } else if attr.name == INSTANCE_OF {
            match attr
                .semantic
                .map_err(AnnotationError::InvalidStringEscape)?
            {
                Some(name) if is_class_path(&name) => match unsupported_class(&name) {
                    None => RuntimeAnnotation::InstanceOf(name),
                    Some(reason) => {
                        return Err(AnnotationError::Untagged(
                            attr_loc,
                            AstUntaggedVariantError::UnsupportedInstanceOf(name, reason),
                        ));
                    }
                },
                _ => {
                    return Err(AnnotationError::Untagged(
                        attr_loc,
                        AstUntaggedVariantError::InvalidInstanceOf,
                    ));
                }
            }
        } else if attr.name == TYPE_OF {
            match attr
                .semantic
                .map_err(AnnotationError::InvalidStringEscape)?
            {
                Some(name) => match BlockType::of_typeof(&name) {
                    Some(block_type) => RuntimeAnnotation::TypeOf(block_type),
                    None => {
                        return Err(AnnotationError::Untagged(
                            attr_loc,
                            AstUntaggedVariantError::InvalidTypeOf(name),
                        ));
                    }
                },
                None => {
                    return Err(AnnotationError::Untagged(
                        attr_loc,
                        AstUntaggedVariantError::InvalidTypeOf(String::new()),
                    ));
                }
            }
        } else {
            continue;
        };
        annotations.push(annotation);
    }
    match annotations.as_slice() {
        [] => Ok(None),
        [_] => Ok(annotations.pop()),
        [first, second, ..] => Err(AnnotationError::Untagged(
            loc,
            if runtime_attribute_name(first) == runtime_attribute_name(second) {
                AstUntaggedVariantError::DuplicateRuntimeAnnotation(
                    runtime_attribute_name(first).to_string(),
                )
            } else {
                AstUntaggedVariantError::ConflictingRuntimeAnnotations
            },
        )),
    }
}

/// The attributes of a declaration as `process_runtime_annotation` reads
/// them.
pub(crate) fn decl_annotation_attributes<'a>(
    ctx: &'a TypeContext,
    attrs: &'a [crate::types::decl::Attribute],
) -> impl Iterator<Item = AnnotationAttribute<'a>> + 'a {
    attrs.iter().map(move |attr| AnnotationAttribute {
        name: attr.attr_name.txt.as_str(),
        semantic: attr
            .attr_payload
            .semantic_string()
            .map(|semantic| semantic.map(str::to_string))
            .map_err(|loc| ctx.resolve_loc(loc)),
        loc: if attr.attr_name.txt == NOT_UNDEFINED
            || attr.attr_name.txt == INSTANCE_OF
            || attr.attr_name.txt == TYPE_OF
        {
            ctx.resolve_loc(attr.attr_name.loc)
        } else {
            Location::none()
        },
    })
}

/// The runtime annotation of a declaration accepted when it was declared
/// (`process_runtime_annotation decl.type_attributes`, without a location).
fn declared_runtime_annotation(
    ctx: &TypeContext,
    decl: &TypeDeclaration,
) -> AnnotationResult<Option<RuntimeAnnotation>> {
    process_runtime_annotation(
        decl_annotation_attributes(ctx, &decl.type_attributes),
        Location::none(),
    )
}

/// The runtime annotation a declaration states, as it is written, for
/// printing it (printtyp.ml `tree_of_type_decl`); a malformed one was
/// reported when the declaration was typed and is left out.
pub(crate) fn stated_runtime_annotation(
    ctx: &TypeContext,
    decl: &TypeDeclaration,
) -> Option<String> {
    match declared_runtime_annotation(ctx, decl) {
        Ok(Some(annotation)) => Some(runtime_annotation_to_string(&annotation)),
        Ok(None) | Err(_) => None,
    }
}

fn annotation_error(err: impl Into<AnnotationError>) -> TypeModError {
    match err.into() {
        AnnotationError::Untagged(loc, error) => {
            TypeModError::AstUntaggedVariantError { loc, error }
        }
        AnnotationError::InvalidStringEscape(loc) => TypeModError::InvalidStringEscape { loc },
    }
}

/// ast_untagged_variants.ml `check_runtime_annotation`: checks the runtime
/// annotations of a declaration whose kind is `is_abstract_or_abbreviation`.
pub(crate) fn check_runtime_annotation<'a>(
    loc: Location,
    kind: AnnotatedKind,
    attrs: impl IntoIterator<Item = AnnotationAttribute<'a>>,
) -> TypeModResult<()> {
    let attrs: Vec<AnnotationAttribute<'a>> = attrs.into_iter().collect();
    let extends = attrs.iter().any(|attr| attr.name == EXTENDS);
    let annotation = process_runtime_annotation(attrs, loc).map_err(annotation_error)?;
    let error = |err: AstUntaggedVariantError| Err(annotation_error((loc, err)));
    // A superclass is named on a record that is a class itself. An abstract
    // class type names its superclass by abbreviating it.
    if extends
        && !(kind == AnnotatedKind::PrivateRecord
            && matches!(annotation, Some(RuntimeAnnotation::InstanceOf(_))))
    {
        return error(AstUntaggedVariantError::ExtendsWithoutClassRecord);
    }
    match (annotation, kind) {
        (None, _) | (Some(_), AnnotatedKind::AbstractOrAbbreviation) => Ok(()),
        (Some(RuntimeAnnotation::InstanceOf(_)), AnnotatedKind::PrivateRecord) => Ok(()),
        (Some(RuntimeAnnotation::InstanceOf(name)), AnnotatedKind::PublicRecord) => {
            error(AstUntaggedVariantError::ClassOnPublicRecord(name))
        }
        (Some(annotation), _) => error(
            AstUntaggedVariantError::RuntimeAnnotationOnRepresentedType(
                runtime_attribute_name(&annotation).to_string(),
            ),
        ),
    }
}

/// The name of the class a declaration with `@instanceOf(path)` declares:
/// with `@module("m")` beside it, the class `path` of that module.
fn declared_class_name(ctx: &TypeContext, decl: &TypeDeclaration, path: &str) -> TypeModResult<String> {
    let module = decl
        .type_attributes
        .iter()
        .find(|attr| attr.attr_name.txt == MODULE);
    match module {
        None => Ok(path.to_string()),
        Some(attr) => match attr.attr_payload.semantic_string() {
            Ok(Some(module)) if !module.is_empty() => {
                Ok(crate::types::variant_runtime::module_class_name(path, module))
            }
            Ok(_) => Err(annotation_error((
                ctx.resolve_loc(attr.attr_name.loc),
                AstUntaggedVariantError::InvalidClassModule,
            ))),
            Err(loc) => Err(TypeModError::InvalidStringEscape {
                loc: ctx.resolve_loc(loc),
            }),
        },
    }
}

/// The class a type is declared to be, with its ancestors.
fn declared_class(ctx: &TypeContext, env: &Env, path: &Path) -> Option<Instance> {
    match find_type(ctx, env, path)?.type_shape.block_type() {
        Some(BlockType::Instance(class @ Instance::Class { .. })) => Some(class.clone()),
        _ => None,
    }
}

/// `Env.find_type`.
fn find_type<'a>(
    ctx: &'a TypeContext,
    env: &'a Env,
    path: &Path,
) -> Option<crate::types::decl::TypeDeclarationRef<'a>> {
    crate::types::ctype::lookup_type_decl_for_path(ctx, env, path)
}

/// variant_layout.ml `value_shape`: the shape stated by the first
/// declaration on the expansion chain of `t` that states one. `fuel` bounds
/// the walk, since a recursive group's shapes are resolved before its
/// abbreviations are checked for cycles.
pub(crate) fn value_shape(ctx: &TypeContext, env: &Env, t: TypeExprRef) -> ValueShape {
    let mut t = t;
    let mut fuel = 100;
    loop {
        let t_repr = ctx.repr(t);
        let path = match &*ctx.get_desc(t_repr) {
            TypeDesc::Tconstr { path, .. } if fuel > 0 => path.clone(),
            _ => return ValueShape::Unstated,
        };
        if let Some(decl) = find_type(ctx, env, &path)
            && decl.type_shape != ValueShape::Unstated
        {
            return decl.type_shape.clone();
        }
        // `Ctype.try_expand_once_opt`.
        match crate::types::ctype::expand_abbrev_opt_once(ctx, env, t_repr) {
            Some(expanded) => {
                t = expanded;
                fuel -= 1;
            }
            None => return ValueShape::Unstated,
        }
    }
}

/// variant_layout.ml `recognized_as`: the payload kind `t` is declared to
/// have.
pub(crate) fn recognized_as(ctx: &TypeContext, env: &Env, t: TypeExprRef) -> Option<BlockType> {
    match value_shape(ctx, env, t) {
        ValueShape::RecognizedAs(shape) => Some(shape.block_type),
        ValueShape::Unstated | ValueShape::NeverUndefined => None,
    }
}

/// variant_layout.ml `payload_kind`: the payload kind of the values of `t`,
/// the one its declarations state or the one its structure gives. A private
/// abbreviation is expanded like any other. An unboxed record is the value of
/// its field, so it has no kind of its own.
pub(crate) fn payload_kind(ctx: &TypeContext, env: &Env, t: TypeExprRef) -> Option<BlockType> {
    if let Some(declared) = recognized_as(ctx, env, t) {
        return Some(declared);
    }
    let expanded = crate::types::ctype::expand_head_opt(ctx, env, t);
    let path = match &*ctx.get_desc(expanded) {
        TypeDesc::Ttuple(_) => {
            return Some(BlockType::Instance(Instance::Array(
                ShapeAllocation::TUPLE_ARRAY,
            )));
        }
        TypeDesc::Tarrow { .. } => return Some(BlockType::Function),
        TypeDesc::Tobject { .. } => return Some(BlockType::Object),
        TypeDesc::Tconstr { path, .. } => path.clone(),
        _ => return None,
    };
    match find_type(ctx, env, &path)
        .as_deref()
        .map(|decl| &decl.type_kind)
    {
        Some(TypeKind::TypeRecord(_, RecordRepresentation::RecordUnboxed(_))) => None,
        Some(TypeKind::TypeRecord(_, _)) => Some(BlockType::Object),
        _ => None,
    }
}

/// variant_layout.ml `declaration_shape`: the shape a declaration states,
/// resolved against what the type it abbreviates states in `env`.
///
/// `superclass` is the type an `@extends(: parent)` on the declaration names.
pub(crate) fn declaration_shape(
    ctx: &TypeContext,
    env: &Env,
    decl: &TypeDeclaration,
    superclass: Option<&Path>,
) -> TypeModResult<ValueShape> {
    Ok(
        match declared_runtime_annotation(ctx, decl).map_err(annotation_error)? {
            None => ValueShape::Unstated,
            Some(RuntimeAnnotation::TypeOf(block_type)) => {
                ValueShape::recognized_as(block_type, ShapeBlocks::fresh())
            }
            Some(RuntimeAnnotation::InstanceOf(path)) => {
                let name = declared_class_name(ctx, decl, &path)?;
                // The name is the attribute's payload string.
                let name_string = decl
                    .type_attributes
                    .iter()
                    .find(|attr| attr.attr_name.txt == INSTANCE_OF)
                    .map(|attr| match &attr.attr_payload {
                        // A backquoted string decodes to a fresh string.
                        crate::types::decl::AttributePayload::SemanticString(payload)
                            if payload.template =>
                        {
                            ShapeString::Allocation(ShapeAllocation::fresh())
                        }
                        _ => ShapeString::attribute(ctx, attr.attr_name.loc),
                    })
                    .expect("an @instanceOf annotation is an attribute");
                // The superclass is the class of the abbreviated type or, for
                // a record, of the type `@extends` names. In a recursive group
                // that type's shape is known from the second round on.
                let superclass = match decl.type_manifest {
                    Some(manifest) => recognized_as(ctx, env, manifest),
                    None => superclass
                        .and_then(|path| declared_class(ctx, env, path))
                        .map(BlockType::Instance),
                };
                let (ancestors, ancestor_blocks) =
                    match superclass {
                        Some(BlockType::Instance(Instance::Class {
                            name: inner,
                            ancestors,
                            blocks,
                        })) => {
                            // An annotation repeating the abbreviated type's, as a
                            // module alias does, states no new class: its list of
                            // ancestors is kept. Otherwise a cell holding the
                            // superclass's name string is put in front of it.
                            if inner == name {
                                (ancestors, blocks.ancestors)
                            } else {
                                (
                                    std::iter::once(inner).chain(ancestors).collect(),
                                    std::iter::once((ShapeAllocation::fresh(), blocks.name))
                                        .chain(blocks.ancestors)
                                        .collect(),
                                )
                            }
                        }
                        _ => (Vec::new(), Vec::new()),
                    };
                ValueShape::recognized_as(
                    BlockType::Instance(Instance::Class {
                        name,
                        ancestors,
                        blocks: ClassBlocks {
                            block: ShapeAllocation::fresh(),
                            name: name_string,
                            ancestors: ancestor_blocks,
                        },
                    }),
                    ShapeBlocks::fresh(),
                )
            }
            Some(RuntimeAnnotation::NotUndefined) => {
                // Restating a kind the abbreviated type is recognized by keeps it.
                match decl.type_manifest.map(|m| value_shape(ctx, env, m)) {
                    Some(shape @ ValueShape::RecognizedAs(_)) => shape,
                    _ => ValueShape::NeverUndefined,
                }
            }
        },
    )
}

/// variant_layout.ml `resolve_shapes`: the shapes of a group of declarations,
/// which can abbreviate each other. Each round resolves one more level of
/// abbreviation within the group, so the rounds stop when one changes
/// nothing.
///
/// `superclasses` holds, for each declaration, the type its `@extends`
/// names.
pub(crate) fn resolve_shapes(
    ctx: &TypeContext,
    env: &Env,
    ids: &[Ident],
    decls: &[TypeDeclaration],
    superclasses: &[Option<Path>],
) -> TypeModResult<Vec<ValueShape>> {
    let with_group = |shapes: &[ValueShape]| {
        let mut env = env.clone();
        for ((id, decl), shape) in ids.iter().zip(decls).zip(shapes) {
            let mut decl = decl.clone();
            decl.type_shape = shape.clone();
            env.store_type(ctx, *id, decl);
        }
        env
    };
    let mut previous: Vec<ValueShape> = decls.iter().map(|d| d.type_shape.clone()).collect();
    let mut round_env = with_group(&previous);
    let mut n = decls.len();
    loop {
        let shapes = decls
            .iter()
            .enumerate()
            .map(|(index, decl)| {
                let superclass = superclasses.get(index).and_then(Option::as_ref);
                declaration_shape(ctx, &round_env, decl, superclass)
            })
            .collect::<TypeModResult<Vec<_>>>()?;
        if n <= 1 || shapes == previous {
            return Ok(shapes);
        }
        round_env = with_group(&shapes);
        previous = shapes;
        n -= 1;
    }
}

fn invalid_untagged(ctx: &TypeContext, loc: crate::types::DeclLoc, reason: String) -> TypeModError {
    TypeModError::InvalidUntaggedVariantDefinition {
        loc: ctx.resolve_loc(loc),
        reason,
    }
}

/// variant_layout.ml `get_block_type`.
fn get_block_type(
    ctx: &TypeContext,
    env: &Env,
    cstr: &ConstructorDeclaration,
) -> TypeModResult<BlockType> {
    match &cstr.cd_args {
        ConstructorArguments::CstrTuple(args) => match args.as_slice() {
            [ty] => Ok(payload_kind(ctx, env, *ty).unwrap_or(BlockType::Unknown)),
            [_, _, ..] => Err(invalid_untagged(
                ctx,
                cstr.cd_loc,
                format!(
                    "Constructor {} has more than one argument.",
                    cstr.cd_id.name()
                ),
            )),
            [] => unreachable!("nullary constructors have no payload shape"),
        },
        ConstructorArguments::CstrRecord(_) => Ok(BlockType::Object),
    }
}

/// ast_untagged_variants.ml `report_error` of `AtMostOneOfKind`.
fn at_most_one_of_kind(kind: &BlockType) -> String {
    let kind = match kind {
        BlockType::Object => "an object type".to_string(),
        BlockType::Instance(Instance::Array(_)) => "an array or tuple type".to_string(),
        BlockType::Instance(instance) => format!("an instance of {}", instance.as_str()),
        BlockType::Function => "a function type".to_string(),
        BlockType::String => "a string type".to_string(),
        BlockType::Number => "a number type (int or float)".to_string(),
        BlockType::Bigint => "a bigint type".to_string(),
        BlockType::Boolean => "a boolean type".to_string(),
        BlockType::Symbol => "a symbol type".to_string(),
        BlockType::Unknown => "of an unknown type".to_string(),
    };
    format!("At most one case can be {kind}.")
}

/// variant_layout.ml `check_invariant`: the cases of a variant must be told
/// apart at run time: nullary cases and tagged blocks by distinct literals,
/// the untagged payloads of an `@unboxed` variant by distinct kinds.
fn check_invariant(
    ctx: &TypeContext,
    consts: &[(crate::types::DeclLoc, &Tag)],
    blocks: &[(crate::types::DeclLoc, &Block)],
) -> TypeModResult<()> {
    use std::collections::{HashMap, HashSet};
    let mut string_literals_consts: HashSet<String> = HashSet::new();
    let mut string_literals_blocks: HashSet<String> = HashSet::new();
    // Keyed by `literal_value_key`, with the spelling of the literal.
    let mut nonstring_literals_consts: HashMap<String, String> = HashMap::new();
    let mut nonstring_literals_blocks: HashMap<String, String> = HashMap::new();
    let mut check_literal = |is_const: bool, loc: crate::types::DeclLoc, tag: &Tag| {
        let (key, spelling) = match &tag.literal {
            LiteralTag::String(s) => {
                let set = if is_const {
                    &mut string_literals_consts
                } else {
                    &mut string_literals_blocks
                };
                if !set.insert(s.clone()) {
                    return Err(invalid_untagged(
                        ctx,
                        loc,
                        format!("Duplicate literal {s}."),
                    ));
                }
                return Ok(());
            }
            literal @ LiteralTag::Int(i) => (literal.value_key(), i.to_string()),
            literal @ LiteralTag::Float(f) => (literal.value_key(), f.clone()),
            literal @ LiteralTag::BigInt(i) => (literal.value_key(), format!("{i}n")),
            literal @ LiteralTag::Bool(b) => (literal.value_key(), b.to_string()),
            literal @ LiteralTag::Null => (literal.value_key(), "null".to_string()),
            literal @ LiteralTag::Undefined => (literal.value_key(), "undefined".to_string()),
        };
        let map = if is_const {
            &mut nonstring_literals_consts
        } else {
            &mut nonstring_literals_blocks
        };
        match map.get(&key) {
            Some(earlier) if *earlier == spelling => {
                return Err(invalid_untagged(
                    ctx,
                    loc,
                    format!("Duplicate literal {spelling}."),
                ));
            }
            Some(earlier) => {
                return Err(invalid_untagged(
                    ctx,
                    loc,
                    format!("The literal {spelling} is the same JavaScript value as {earlier}."),
                ));
            }
            None => {}
        }
        map.insert(key, spelling);
        Ok(())
    };
    for (loc, tag) in consts {
        check_literal(true, *loc, tag)?;
    }
    let true_and_false_are_cases = {
        let key = |b| LiteralTag::Bool(b).value_key();
        consts
            .iter()
            .any(|(_, tag)| tag.literal.value_key() == key(true))
            && consts
                .iter()
                .any(|(_, tag)| tag.literal.value_key() == key(false))
    };
    // The kinds of the untagged payloads seen so far. A class is identified
    // by its name.
    let mut kinds: Vec<BlockType> = Vec::new();
    let kind_key = |kind: &BlockType| match kind {
        BlockType::Instance(Instance::Class { name, blocks, .. }) => {
            BlockType::Instance(Instance::Class {
                name: name.clone(),
                ancestors: Vec::new(),
                blocks: ClassBlocks {
                    ancestors: Vec::new(),
                    ..blocks.clone()
                },
            })
        }
        kind => kind.clone(),
    };
    for (loc, block) in blocks {
        match block {
            Block::Tagged(TaggedBlock { tag, .. }) => check_literal(false, *loc, tag)?,
            Block::Untagged {
                tag,
                block_type: BlockType::Unknown,
            } => {
                // No check tells an unknown payload apart from another payload.
                if blocks.len() != 1 {
                    return Err(invalid_untagged(
                        ctx,
                        *loc,
                        format!(
                            "Case {} has a payload that is not of one of the recognized shapes (object, array, etc). Then it must be the only case with payloads.",
                            tag.name
                        ),
                    ));
                }
            }
            Block::Untagged { tag, block_type } => {
                // Literal cases are matched before payload cases, so a boolean
                // payload only receives the booleans that are not literal
                // cases. A partial overlap is allowed.
                if *block_type == BlockType::Boolean && true_and_false_are_cases {
                    return Err(invalid_untagged(
                        ctx,
                        *loc,
                        format!(
                            "Case {} can never match: both true and false are already cases of this variant.",
                            tag.name
                        ),
                    ));
                }
                let key = kind_key(block_type);
                if kinds.contains(&key) {
                    return Err(invalid_untagged(ctx, *loc, at_most_one_of_kind(block_type)));
                }
                kinds.push(key);
            }
        }
    }
    Ok(())
}

/// ast_untagged_variants.ml `declared_tag`: a constructor without `@as` is
/// represented by its name.
pub(crate) fn declared_tag(cstr: &ConstructorDeclaration) -> Tag {
    let name = cstr.cd_id.name_atom();
    Tag {
        literal: cstr
            .cd_runtime_tag
            .clone()
            .unwrap_or_else(|| LiteralTag::String(name.to_string())),
        name,
    }
}

/// variant_layout.ml `layout_from_type_variant`. `process_tag_name` reads a
/// constructor's `@tag`.
pub(crate) fn layout_from_type_variant(
    ctx: &TypeContext,
    env: &Env,
    configuration: Configuration,
    cstrs: &[ConstructorDeclaration],
    mut process_tag_name: impl FnMut(&ConstructorDeclaration) -> TypeModResult<Option<String>>,
) -> TypeModResult<Layout> {
    let mut located = Vec::with_capacity(cstrs.len());
    for cstr in cstrs {
        let is_nullary =
            matches!(&cstr.cd_args, ConstructorArguments::CstrTuple(args) if args.is_empty());
        if is_nullary {
            located.push((cstr.cd_loc, ConstructorCase::Constant(declared_tag(cstr))));
        } else {
            let tag = declared_tag(cstr);
            let tag_name = process_tag_name(cstr)?;
            let block = if configuration.unboxed {
                Block::Untagged {
                    tag,
                    block_type: get_block_type(ctx, env, cstr)?,
                }
            } else {
                Block::Tagged(TaggedBlock { tag, tag_name })
            };
            located.push((cstr.cd_loc, ConstructorCase::Block(block)));
        }
    }
    {
        let consts: Vec<_> = located
            .iter()
            .filter_map(|(loc, case)| match case {
                ConstructorCase::Constant(tag) => Some((*loc, tag)),
                ConstructorCase::Block(_) => None,
            })
            .collect();
        let blocks: Vec<_> = located
            .iter()
            .filter_map(|(loc, case)| match case {
                ConstructorCase::Block(block) => Some((*loc, block)),
                ConstructorCase::Constant(_) => None,
            })
            .collect();
        check_invariant(ctx, &consts, &blocks)?;
    }
    Ok(Layout::new(
        configuration,
        located.into_iter().map(|(_, case)| case).collect(),
    ))
}

/// typedecl.ml `check_manifest_annotation`: an annotation on an abbreviation
/// is a claim about the abbreviated type, so it must agree with what the
/// compiler knows about that type.
///
/// For a record with `@extends`, `extends` is the declared type's own path
/// and the type named, when it is one.
pub(crate) fn check_manifest_annotation(
    ctx: &TypeContext,
    loc: Location,
    env: &Env,
    decl: &TypeDeclaration,
    extends: Option<(&Path, Option<&Path>)>,
) -> TypeModResult<()> {
    use crate::raw_lambda::typeopt::{Abstractness, Undefinedness};
    let annotation = declared_runtime_annotation(ctx, decl).map_err(annotation_error)?;
    if let Some((own, superclass)) = extends
        && decl.type_attributes.iter().any(|attr| attr.attr_name.txt == EXTENDS)
    {
        check_extends(ctx, loc, env, decl, &annotation, own, superclass)?;
    }
    let (Some(outer), Some(manifest)) = (annotation, decl.type_manifest) else {
        return Ok(());
    };
    let error = |err: AstUntaggedVariantError| Err(annotation_error((loc, err)));
    // A class is compared by its name, which includes its module.
    let outer = match outer {
        RuntimeAnnotation::InstanceOf(path) => {
            RuntimeAnnotation::InstanceOf(declared_class_name(ctx, decl, &path)?)
        }
        outer => outer,
    };
    let name = runtime_attribute_name(&outer).to_string();
    let stands_for_another = || {
        error(AstUntaggedVariantError::RuntimeAnnotationOnTypeParameter(
            name.clone(),
        ))
    };
    let unrelated = || {
        error(AstUntaggedVariantError::RuntimeAnnotationOnUnrelatedType(
            name.clone(),
        ))
    };
    match (&outer, payload_kind(ctx, env, manifest)) {
        (RuntimeAnnotation::NotUndefined, _) => {
            match crate::raw_lambda::typeopt::undefinedness(ctx, env, manifest) {
                Undefinedness::CannotBeUndefined | Undefinedness::Unseen => Ok(()),
                Undefinedness::StandsForAnother => stands_for_another(),
                Undefinedness::CanBeUndefined => unrelated(),
            }
        }
        (RuntimeAnnotation::InstanceOf(_) | RuntimeAnnotation::TypeOf(_), None) => {
            match crate::raw_lambda::typeopt::abstractness(ctx, env, manifest) {
                Abstractness::Opaque => match &outer {
                    // Two public abbreviations of one type would declare its
                    // values instances of two classes.
                    RuntimeAnnotation::InstanceOf(name)
                        if decl.type_private == PrivateFlag::Public =>
                    {
                        error(AstUntaggedVariantError::ClassOnPublicAbbreviation(
                            name.clone(),
                        ))
                    }
                    _ => Ok(()),
                },
                Abstractness::StandsForAnother => stands_for_another(),
                Abstractness::NotAbstract => unrelated(),
            }
        }
        (RuntimeAnnotation::TypeOf(block_type), Some(inner)) if *block_type == inner => Ok(()),
        (
            RuntimeAnnotation::InstanceOf(name),
            Some(BlockType::Instance(Instance::Class { name: inner, .. })),
        ) if *name == inner => Ok(()),
        (
            RuntimeAnnotation::InstanceOf(name),
            Some(inner @ (BlockType::Instance(Instance::Class { .. }) | BlockType::Object)),
        ) => {
            // A public abbreviation would make every value of the superclass
            // type a value of the subclass, without a coercion.
            let (superclass, ancestors) = match inner {
                BlockType::Instance(Instance::Class {
                    name: ancestor,
                    ancestors,
                    ..
                }) => (
                    ancestor.clone(),
                    std::iter::once(ancestor)
                        .chain(ancestors)
                        .collect::<Vec<_>>(),
                ),
                // Every class instance is an object.
                _ => ("Object".to_string(), Vec::new()),
            };
            if decl.type_private == PrivateFlag::Public {
                error(AstUntaggedVariantError::SubclassOfPublicAbbreviation(
                    name.clone(),
                    superclass,
                ))
            } else if ancestors.contains(name) {
                error(AstUntaggedVariantError::ClassTwiceInChain(name.clone()))
            } else {
                Ok(())
            }
        }
        (RuntimeAnnotation::InstanceOf(name), Some(BlockType::Instance(Instance::Array(_)))) => {
            error(AstUntaggedVariantError::SubclassOfArray(name.clone()))
        }
        (RuntimeAnnotation::InstanceOf(_) | RuntimeAnnotation::TypeOf(_), Some(inner)) => {
            let recognized_by = match &inner {
                BlockType::Instance(Instance::Class { name, .. }) => {
                    runtime_annotation_to_string(&RuntimeAnnotation::InstanceOf(name.clone()))
                }
                BlockType::Instance(Instance::Array(_)) => "Array.isArray".to_string(),
                block_type => {
                    runtime_annotation_to_string(&RuntimeAnnotation::TypeOf(block_type.clone()))
                }
            };
            error(
                AstUntaggedVariantError::RuntimeAnnotationContradictsManifest(
                    runtime_annotation_to_string(&outer),
                    recognized_by,
                ),
            )
        }
    }
}

/// A private record with `@instanceOf` and `@extends(: parent)`: the named
/// type is a class, the record is not its own ancestor, and the record
/// coerces to it, so it has the superclass's fields at the same types.
fn check_extends(
    ctx: &TypeContext,
    loc: Location,
    env: &Env,
    decl: &TypeDeclaration,
    annotation: &Option<RuntimeAnnotation>,
    own: &Path,
    superclass: Option<&Path>,
) -> TypeModResult<()> {
    let error = |err: AstUntaggedVariantError| Err(annotation_error((loc, err)));
    let Some(RuntimeAnnotation::InstanceOf(path)) = annotation else {
        return error(AstUntaggedVariantError::ExtendsWithoutClassRecord);
    };
    let name = declared_class_name(ctx, decl, path)?;
    let Some(superclass) = superclass else {
        return error(AstUntaggedVariantError::ExtendsNotAClass);
    };
    let Some(Instance::Class {
        name: parent,
        ancestors,
        ..
    }) = declared_class(ctx, env, superclass)
    else {
        return error(AstUntaggedVariantError::ExtendsNotAClass);
    };
    if parent == name || ancestors.contains(&name) {
        return error(AstUntaggedVariantError::ClassTwiceInChain(name));
    }
    // An abstract class type has no fields to compare, and nothing coerces
    // to it but its own abbreviations.
    let parent_is_record = matches!(
        find_type(ctx, env, superclass).as_deref().map(|decl| &decl.type_kind),
        Some(TypeKind::TypeRecord(..))
    );
    if !parent_is_record {
        return Ok(());
    }
    // Both at their most general instance: the fields are then compared up
    // to the parameters of the two types.
    let instance = |path: &Path| {
        let arity = find_type(ctx, env, path).map_or(0, |decl| decl.type_params.len());
        ctx.new_constr(path.clone(), (0..arity).map(|_| ctx.new_var(None)).collect())
    };
    let own_type = instance(own);
    let parent_type = instance(superclass);
    match crate::types::ctype::subtype_now(ctx, env, own_type, parent_type) {
        Ok(()) => Ok(()),
        Err(_) => error(AstUntaggedVariantError::ExtendsFieldsMismatch(parent)),
    }
}
