//! Type system for the ReScript compiler.
//!
//! This module provides the core types and operations for the ReScript
//! type checker. It includes:
//!
//! - [`Path`] - Module paths for qualified names
//! - [`TypeExpr`] - Type expressions with unification support
//! - [`TypeContext`] - Per-compilation type checking context
//! - [`Variance`] - Variance analysis for type parameters
//!
//! # Architecture
//!
//! The type system is designed for concurrent compilation:
//!
//! - No global state - all state is in `TypeContext`
//! - Arena-based allocation for type expressions
//! - Interior mutability for unification algorithm
//!
//! # Usage
//!
//! ```rust,ignore
//! use rescript_compiler::types::{TypeContext, Path};
//! use rescript_compiler::context::IdGenerator;
//!
//! let id_gen = IdGenerator::new();
//! let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
//!
//! // Create types
//! let t1 = ctx.new_var(Some("a".to_string()));
//! let t2 = ctx.new_var(None);
//! let func = ctx.new_arrow_simple(t1, t2);
//! ```

pub mod asttypes;
pub mod btype;
pub mod context;
pub mod ctype;
pub mod decl;
pub mod decl_loc;
pub mod dict_pattern;
pub mod env;
pub(crate) mod env_lazy;
pub mod external_ffi_types;
pub mod includecore;
pub mod includemod;
pub(crate) mod parmatch;
pub mod path;
pub(crate) mod path_provenance;
pub mod predef;
pub mod printtyp;
pub mod record_runtime;
pub mod sexp_typedtree;
pub mod shared_store;
pub mod tast_arena;
pub mod tast_iterator;
pub mod thread_store;
pub mod type_expr;
pub mod typecore;
pub mod typedtree;
pub mod typemod;
pub mod unit_reads;
pub mod usage;
pub mod variance;
pub mod variant_runtime;
pub(crate) mod variant_layout;

// Re-exports for convenience
pub use asttypes::{ArgLabel, Label, Located, MutableFlag, PrivateFlag};
pub use context::TypeContext;
pub use decl::{
    AliasPresence, Attribute, AttributePayload, ConstructorArguments, ConstructorDeclaration,
    ConstructorDescription, ConstructorKind, ExtStatus, ExtensionConstructor, LabelArrayRef,
    LabelDeclaration, LabelDescription, ModtypeDeclaration, ModuleDeclaration, ModuleType,
    PrimitiveDescription, RecStatus, RecordRepresentation, Signature, SignatureItem,
    TypeDeclaration, TypeInlinedType, TypeKind, TypeRepresentation, ValueDescription, ValueKind,
    may_equal_constructor, same_constructor,
};
pub use decl_loc::{DeclLoc, DeclLocTable, DeclLocs};
pub use path::{NOPOS, Path, Typath};
pub(crate) use type_expr::TypeExprRefMap;
pub use type_expr::{
    AbbrevMemo, AbbrevMemoRef, FieldMutability, GENERIC_LEVEL, LOWEST_LEVEL, MutabilityRef,
    PIVOT_LEVEL, RowDesc, RowField, RowFieldRef, TypeArg, TypeDesc, TypeExpr, TypeExprRef,
};
pub use variance::{Variance, VarianceFlag};
pub use variant_runtime::{
    Block as VariantBlock, BlockType as VariantBlockType, Configuration as VariantConfiguration,
    ConstructorCase as VariantConstructorCase, ConstructorReference, Instance as VariantInstance,
    Layout as VariantLayout, LayoutRef as VariantLayoutRef, LiteralTag as VariantLiteralTag,
    MatchingFacts as VariantMatchingFacts, Tag as VariantTag, TagType as VariantTagType,
    ClassBlocks, RecognizedShape, ShapeAllocation, ShapeBlocks, ShapeString, TaggedBlock, ValueShape,
};

// btype exports
pub use btype::{
    hash_variant, is_row_name, is_tconstr, is_tunivar, is_tvar, iter_type_expr,
    iter_type_expr_kind, mark_type_node, row_field, row_field_repr, row_fixed, row_more, row_repr,
    static_row, unmark_type,
};

// ctype exports
pub use ctype::{
    SubtypeContext, TypeError, TypePair, TypeResult, UnifyMode, UnifyState, copy_type, deep_occur,
    function_arity, generalize, generalize_structure, instance, instance_constructor,
    instance_constructor_in_pattern, is_function, link_type, occurs, split_arrow, tuple_elements,
    unify, unify_var, update_level,
};

// env exports
pub use env::{Env, EnvError, EnvFlags, EnvResult, IdTbl, TycompTbl, initial_env};

// typecore exports
pub use typecore::{
    PatternMode, PatternState, TypeCheckContext, TypeClashContext, TypeCoreError, TypeCoreResult,
    type_binding, type_expression, type_pattern,
};

// typedtree exports
pub use typedtree::{
    Case, Constant as TypedConstant, Expression, ExpressionDesc, Partial, Pattern, PatternDesc,
    TypedCoreType, ValueBinding,
};

// typemod exports
pub use typemod::{
    TypeModError, TypeModResult, transl_signature, type_module_expr, type_structure,
};

// includemod exports
pub use includemod::{
    IncludeModError, IncludeModResult, is_empty_signature, modtypes, signature_modules,
    signature_types, signature_values, signatures,
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::ident::Ident;

    #[test]
    fn test_integration() {
        // Create a type context
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        // Create a simple function type: 'a -> 'b
        let a = ctx.new_var(Some("a".to_string()));
        let b = ctx.new_var(Some("b".to_string()));
        let _func = ctx.new_arrow_simple(a, b);

        // Create a path
        let string_id = Ident::create_persistent("String");
        let string_path = Path::pident(string_id);
        let string_type = ctx.new_constr(string_path, vec![]);

        // Test repr
        let link = ctx.new_link(string_type);
        assert_eq!(ctx.repr(link), string_type);
    }

    #[test]
    fn test_level_scoping() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        // Begin a definition scope
        ctx.begin_def();
        let level1 = ctx.current_level();

        // Create a type at this level
        let t = ctx.new_var(None);
        assert_eq!(ctx.get_level(t), level1);

        // Nested scope
        ctx.begin_def();
        assert_eq!(ctx.current_level(), level1 + 1);

        ctx.end_def();
        assert_eq!(ctx.current_level(), level1);

        ctx.end_def();
        assert_eq!(ctx.current_level(), 0);
    }
}
