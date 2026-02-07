//! Binary AST file writer
//!
//! This module provides functionality to write binary AST files (.ast, .iast)
//! that are byte-identical to those produced by the OCaml compiler.
//!
//! # Binary AST File Format
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │ SECTION 1: Header                                                   │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ Offset 0-3: Dependency section size (4 bytes, big-endian u32)       │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ SECTION 2: Dependencies + Source Path                               │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ Byte 4: '\n' (0x0A) - separator                                     │
//! │ "ModuleName1\n"                                                     │
//! │ "ModuleName2\n"                                                     │
//! │ ...                                                                 │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ Source path + '\n'                                                  │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ SECTION 3: OCaml Marshal Data                                       │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ Magic: 0x84 0x95 0xA6 0xBE (4 bytes)                                │
//! │ Header: data_len(4) + obj_count(4) + size_32(4) + size_64(4)        │
//! │ Payload: Encoded parsetree0 AST                                     │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```

use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;

use super::deps::{extract_signature_deps, extract_structure_deps};
use super::mapper_to0::{map_signature, map_structure};
use super::marshal::MarshalWriter;
use super::ppx;
use super::serialize::Marshal;
use crate::parse_arena::ParseArena;
use crate::parser::ast::{
    IncludeDeclaration, ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeDesc, Signature,
    Structure, StructureItem, StructureItemDesc,
};

/// The separator character used in the binary AST format.
const MAGIC_SEP_CHAR: u8 = b'\n';

/// Write a binary AST file for a structure (implementation, .ast file).
///
/// # Arguments
///
/// * `output_path` - Path to the output .ast file
/// * `source_path` - Absolute path to the source file
/// * `arena` - The parse arena containing location data
/// * `ast` - The parsed structure AST
///
/// # Returns
///
/// Returns `Ok(())` on success, or an `io::Error` if writing fails.
pub fn write_structure_ast(
    output_path: &Path,
    source_path: &str,
    arena: &mut ParseArena,
    ast: &Structure,
) -> io::Result<()> {
    // 1. Extract dependencies
    let deps = extract_structure_deps(arena, ast);

    // 2. Convert AST to parsetree0 format
    let ast0 = map_structure(arena, ast);

    // 3. Write the binary AST file (parsetree0 doesn't need arena for marshalling)
    write_ast_file(output_path, source_path, arena, &deps, &ast0)
}

/// Write a binary AST file for a signature (interface, .iast file).
///
/// # Arguments
///
/// * `output_path` - Path to the output .iast file
/// * `source_path` - Absolute path to the source file
/// * `arena` - The parse arena containing location data
/// * `ast` - The parsed signature AST
///
/// # Returns
///
/// Returns `Ok(())` on success, or an `io::Error` if writing fails.
pub fn write_signature_ast(
    output_path: &Path,
    source_path: &str,
    arena: &mut ParseArena,
    ast: &Signature,
) -> io::Result<()> {
    // 1. Extract dependencies
    let deps = extract_signature_deps(arena, ast);

    // 2. Convert AST to parsetree0 format
    let ast0 = map_signature(arena, ast);

    // 3. Write the binary AST file (parsetree0 doesn't need arena for marshalling)
    write_ast_file(output_path, source_path, arena, &deps, &ast0)
}

/// Write a binary AST file for a structure in the CURRENT parsetree format.
///
/// This is different from `write_structure_ast` which converts to parsetree0.
/// The current format is what OCaml's `-bs-ast` flag outputs.
///
/// This applies built-in PPX transformations (FFI encoding for externals)
/// before writing, matching OCaml's behavior.
pub fn write_structure_ast_current(
    output_path: &Path,
    source_path: &str,
    arena: &mut crate::parse_arena::ParseArena,
    ast: &Structure,
) -> io::Result<()> {
    // 1. Apply built-in PPX transformations (FFI encoding for externals, etc.)
    let rewritten_ast = ppx::rewrite_structure(ast, arena)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("PPX rewrite failed: {e}")))?;

    // 2. Process @@config attributes (e.g., no_export wrapping)
    let rewritten_ast = if has_no_export_config(&rewritten_ast, arena) {
        wrap_no_export(rewritten_ast)
    } else {
        rewritten_ast
    };

    // 3. Extract dependencies from the rewritten AST
    let deps = extract_structure_deps(arena, &rewritten_ast);

    // 4. Write the binary AST file directly (current format, no parsetree0 conversion)
    write_ast_file(output_path, source_path, arena, &deps, &rewritten_ast)
}

/// Write a binary AST file for a signature in the CURRENT parsetree format.
///
/// This applies built-in PPX transformations (FFI encoding for externals)
/// before writing, matching OCaml's behavior.
pub fn write_signature_ast_current(
    output_path: &Path,
    source_path: &str,
    arena: &mut crate::parse_arena::ParseArena,
    ast: &Signature,
) -> io::Result<()> {
    // 1. Apply built-in PPX transformations (FFI encoding for externals, etc.)
    let rewritten_ast = ppx::rewrite_signature(ast, arena)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("PPX rewrite failed: {e}")))?;

    // 2. Extract dependencies from the rewritten AST
    let deps = extract_signature_deps(arena, &rewritten_ast);

    // 3. Write the binary AST file directly (current format, no parsetree0 conversion)
    write_ast_file(output_path, source_path, arena, &deps, &rewritten_ast)
}

/// Write a binary AST file with the given dependencies and AST.
fn write_ast_file<A: Marshal>(
    output_path: &Path,
    source_path: &str,
    arena: &crate::parse_arena::ParseArena,
    deps: &std::collections::BTreeSet<String>,
    ast: &A,
) -> io::Result<()> {
    // Build the dependency section
    let mut dep_buf = Vec::with_capacity(256);
    dep_buf.push(MAGIC_SEP_CHAR); // Leading '\n'
    for dep in deps {
        dep_buf.extend_from_slice(dep.as_bytes());
        dep_buf.push(MAGIC_SEP_CHAR);
    }

    // Marshal the AST
    let mut marshal_writer = MarshalWriter::new();
    marshal_writer.set_arena(arena);
    ast.marshal(&mut marshal_writer);
    let marshal_data = marshal_writer.finish();

    // Open output file
    let file = File::create(output_path)?;
    let mut writer = BufWriter::new(file);

    // Write Section 1: Dependency section size (big-endian u32)
    let dep_size = dep_buf.len() as u32;
    writer.write_all(&dep_size.to_be_bytes())?;

    // Write Section 2: Dependencies
    writer.write_all(&dep_buf)?;

    // Write source path + newline
    writer.write_all(source_path.as_bytes())?;
    writer.write_all(&[MAGIC_SEP_CHAR])?;

    // Write Section 3: Marshal data
    writer.write_all(&marshal_data)?;

    writer.flush()?;
    Ok(())
}

/// Write a structure AST to a Vec<u8> (for testing).
pub fn write_structure_ast_to_vec(source_path: &str, arena: &mut ParseArena, ast: &Structure) -> Vec<u8> {
    let deps = extract_structure_deps(arena, ast);
    let ast0 = map_structure(arena, ast);
    write_ast_to_vec(source_path, arena, &deps, &ast0)
}

/// Write a signature AST to a Vec<u8> (for testing).
pub fn write_signature_ast_to_vec(source_path: &str, arena: &mut ParseArena, ast: &Signature) -> Vec<u8> {
    let deps = extract_signature_deps(arena, ast);
    let ast0 = map_signature(arena, ast);
    write_ast_to_vec(source_path, arena, &deps, &ast0)
}

/// Write an AST to a Vec<u8>.
fn write_ast_to_vec<A: Marshal>(
    source_path: &str,
    arena: &ParseArena,
    deps: &std::collections::BTreeSet<String>,
    ast: &A,
) -> Vec<u8> {
    let mut result = Vec::new();

    // Build the dependency section
    let mut dep_buf = Vec::with_capacity(256);
    dep_buf.push(MAGIC_SEP_CHAR);
    for dep in deps {
        dep_buf.extend_from_slice(dep.as_bytes());
        dep_buf.push(MAGIC_SEP_CHAR);
    }

    // Marshal the AST
    let mut marshal_writer = MarshalWriter::new();
    marshal_writer.set_arena(arena);
    ast.marshal(&mut marshal_writer);
    let marshal_data = marshal_writer.finish();

    // Write Section 1: Dependency section size
    let dep_size = dep_buf.len() as u32;
    result.extend_from_slice(&dep_size.to_be_bytes());

    // Write Section 2: Dependencies
    result.extend_from_slice(&dep_buf);

    // Write source path + newline
    result.extend_from_slice(source_path.as_bytes());
    result.push(MAGIC_SEP_CHAR);

    // Write Section 3: Marshal data
    result.extend_from_slice(&marshal_data);

    result
}

/// Check if the structure has a `@@config({no_export: ...})` attribute that
/// evaluates to true. Mirrors OCaml's `Ast_config.iter_on_bs_config_str` +
/// `Js_config.no_export` logic.
fn has_no_export_config(structure: &[StructureItem], arena: &ParseArena) -> bool {
    use crate::parser::ast::ExpressionDesc;
    use crate::parser::longident::Longident;

    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_attribute(attr) => {
                let attr_name = arena.get_string(attr.0.txt);
                if attr_name == "config" {
                    // Found @@config(...) - check if payload contains no_export
                    if let crate::parser::ast::Payload::PStr(Box::new(items)) = &attr.1 {
                        if let Some(eval_item) = items.first() {
                            if let StructureItemDesc::Pstr_eval(expr, _) = &*eval_item.pstr_desc {
                                match &*expr.pexp_desc {
                                    // @@config({no_export: ...}) - record form
                                    ExpressionDesc::Pexp_record(inner) => {
                    let (ref fields, _) = **inner;
                                        for field in fields {
                                            let lid = arena.get_longident(field.lid.txt);
                                            if let Longident::Lident(s) = lid {
                                                if arena.get_string(*s) == "no_export" {
                                                    // Check value: if it's an ident with same name,
                                                    // or `true`, it's true. Only explicit `false` is false.
                                                    if is_false_literal(&field.expr, arena) {
                                                        return false;
                                                    }
                                                    return true;
                                                }
                                            }
                                        }
                                    }
                                    // @@config(no_export) - bare ident form
                                    ExpressionDesc::Pexp_ident(lid_loc) => {
                                        let lid = arena.get_longident(lid_loc.txt);
                                        if let Longident::Lident(s) = lid {
                                            if arena.get_string(*s) == "no_export" {
                                                return true;
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                    // @@config found but no no_export
                    return false;
                }
                // Other floating attribute, continue scanning
            }
            _ => {
                // Non-attribute item, stop scanning (matches OCaml behavior)
                return false;
            }
        }
    }
    false
}

/// Check if an expression is the literal `false`.
fn is_false_literal(expr: &crate::parser::ast::Expression, arena: &ParseArena) -> bool {
    use crate::parser::ast::ExpressionDesc;
    use crate::parser::longident::Longident;

    if let ExpressionDesc::Pexp_construct(lid_loc, None) = &*expr.pexp_desc {
        let lid = arena.get_longident(lid_loc.txt);
        if let Longident::Lident(s) = lid {
            return arena.get_string(*s) == "false";
        }
    }
    false
}

/// Wrap a structure with `include (struct ... end : sig end)` for no_export.
/// This matches OCaml's `js_implementation.ml no_export` function.
fn wrap_no_export(structure: Vec<StructureItem>) -> Vec<StructureItem> {
    if structure.is_empty() {
        return structure;
    }

    // Use the location of the first item for all generated nodes
    let loc = structure[0].pstr_loc;

    // Build: include ((struct <items> end) : (sig end))
    let inner_mod = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(structure))),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    let empty_sig = ModuleType {
        pmty_desc: Box::new(ModuleTypeDesc::Pmty_signature(Box::new(vec![]))),
        pmty_loc: loc,
        pmty_attributes: vec![],
    };

    let constrained_mod = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_constraint(Box::new(inner_mod), Box::new(empty_sig))),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    let include_decl = IncludeDeclaration {
        pincl_mod: constrained_mod,
        pincl_loc: loc,
        pincl_attributes: vec![],
    };

    vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_include(Box::new(include_decl))),
        pstr_loc: loc,
    }]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_arena::{LocIdx, Located};
    use crate::parser::ast::{
        Constant, Expression, ExpressionDesc, Pattern, PatternDesc, RecFlag, StructureItem,
        StructureItemDesc, ValueBinding,
    };
    use crate::parser::longident::Longident;

    fn make_simple_let_binding(arena: &mut crate::parse_arena::ParseArena, name: &str, value: i32) -> StructureItem {
        let name_idx = arena.intern(name);
        StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_value(
                RecFlag::Nonrecursive,
                vec![ValueBinding {
                    pvb_pat: Pattern {
                        ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                            txt: name_idx,
                            loc: LocIdx::none(),
                        })),
                        ppat_loc: LocIdx::none(),
                        ppat_attributes: vec![],
                    },
                    pvb_expr: Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(Constant::Integer(
                            std::borrow::Cow::Owned(value.to_string()),
                            None,
                        )))),
                        pexp_loc: LocIdx::none(),
                        pexp_attributes: vec![],
                    },
                    pvb_attributes: vec![],
                    pvb_loc: LocIdx::none(),
                }],
            )),
            pstr_loc: LocIdx::none(),
        }
    }

    fn make_module_ref_expr(arena: &mut crate::parse_arena::ParseArena, module: &str, name: &str) -> Expression {
        let module_idx = arena.intern(module);
        let name_idx = arena.intern(name);
        let lid_idx = arena.push_longident(Longident::ldot(Longident::lident(module_idx), name_idx));
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: lid_idx,
                loc: LocIdx::none(),
            })),
            pexp_loc: LocIdx::none(),
            pexp_attributes: vec![],
        }
    }

    fn make_test_arena() -> crate::parse_arena::ParseArena {
        crate::parse_arena::ParseArena::new()
    }

    #[test]
    fn test_empty_structure() {
        let mut arena = make_test_arena();
        let ast: Structure = vec![];
        let result = write_structure_ast_to_vec("/test/empty.res", &mut arena, &ast);

        // Check header
        let dep_size = u32::from_be_bytes([result[0], result[1], result[2], result[3]]);
        assert_eq!(dep_size, 1); // Just the leading '\n'

        // Check leading '\n'
        assert_eq!(result[4], b'\n');

        // Check source path
        let path_start = 5;
        let expected_path = "/test/empty.res\n";
        assert_eq!(
            &result[path_start..path_start + expected_path.len()],
            expected_path.as_bytes()
        );

        // Check marshal magic number
        let marshal_start = path_start + expected_path.len();
        assert_eq!(result[marshal_start], 0x84);
        assert_eq!(result[marshal_start + 1], 0x95);
        assert_eq!(result[marshal_start + 2], 0xA6);
        assert_eq!(result[marshal_start + 3], 0xBE);
    }

    #[test]
    fn test_simple_binding() {
        let mut arena = make_test_arena();
        let ast = vec![make_simple_let_binding(&mut arena, "x", 42)];
        let result = write_structure_ast_to_vec("/test/simple.res", &mut arena, &ast);

        // Should have marshal magic number
        let dep_size = u32::from_be_bytes([result[0], result[1], result[2], result[3]]) as usize;
        let source_path = "/test/simple.res";
        let marshal_start = 4 + dep_size + source_path.len() + 1;

        assert_eq!(result[marshal_start], 0x84);
        assert_eq!(result[marshal_start + 1], 0x95);
        assert_eq!(result[marshal_start + 2], 0xA6);
        assert_eq!(result[marshal_start + 3], 0xBE);
    }

    #[test]
    fn test_with_dependencies() {
        let mut arena = make_test_arena();
        let ast = vec![StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((make_module_ref_expr(&mut arena, "Array", "map"), vec![])))),
            pstr_loc: LocIdx::none(),
        }];

        let result = write_structure_ast_to_vec("/test/deps.res", &mut arena, &ast);

        // Check dependency section
        let dep_size = u32::from_be_bytes([result[0], result[1], result[2], result[3]]) as usize;

        // dep_size should include '\n' + "Array\n"
        assert_eq!(dep_size, 1 + "Array\n".len());

        // Check the dependency content
        assert_eq!(result[4], b'\n'); // Leading separator
        assert_eq!(&result[5..5 + 5], b"Array");
        assert_eq!(result[10], b'\n'); // Trailing separator
    }

    #[test]
    fn test_multiple_dependencies() {
        let mut arena = make_test_arena();
        let ast = vec![
            StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_eval(
                    make_module_ref_expr(&mut arena, "Array", "map"),
                    vec![],
                )),
                pstr_loc: LocIdx::none(),
            },
            StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((make_module_ref_expr(&mut arena, "Js", "log"), vec![])))),
                pstr_loc: LocIdx::none(),
            },
        ];

        let result = write_structure_ast_to_vec("/test/multi.res", &mut arena, &ast);

        let dep_size = u32::from_be_bytes([result[0], result[1], result[2], result[3]]) as usize;

        // Dependencies are sorted, so: '\n' + "Array\n" + "Js\n"
        assert_eq!(dep_size, 1 + "Array\n".len() + "Js\n".len());
    }

    #[test]
    fn test_source_path_preserved() {
        let mut arena = make_test_arena();
        let ast: Structure = vec![];
        let source_path = "/Users/dev/project/src/Main.res";
        let result = write_structure_ast_to_vec(source_path, &mut arena, &ast);

        let dep_size = u32::from_be_bytes([result[0], result[1], result[2], result[3]]) as usize;
        let path_start = 4 + dep_size;

        // Find the path in the output
        let expected_with_newline = format!("{}\n", source_path);
        assert_eq!(
            &result[path_start..path_start + expected_with_newline.len()],
            expected_with_newline.as_bytes()
        );
    }

    #[test]
    fn test_write_to_file() {
        use std::fs;

        // Use a temp file in the target directory
        let output_path = std::path::Path::new("target/test_binary_ast_writer.ast");

        let mut arena = make_test_arena();
        let ast = vec![make_simple_let_binding(&mut arena, "x", 1)];
        write_structure_ast(output_path, "/test/test.res", &mut arena, &ast).unwrap();

        // Verify file exists and has content
        let content = fs::read(output_path).unwrap();
        assert!(!content.is_empty());

        // Verify marshal magic number is present
        let dep_size = u32::from_be_bytes([content[0], content[1], content[2], content[3]]) as usize;
        let source_path = "/test/test.res";
        let marshal_start = 4 + dep_size + source_path.len() + 1;

        assert_eq!(content[marshal_start], 0x84);
        assert_eq!(content[marshal_start + 1], 0x95);

        // Clean up
        let _ = fs::remove_file(output_path);
    }

    #[test]
    fn test_empty_signature() {
        let mut arena = make_test_arena();
        let ast: Signature = vec![];
        let result = write_signature_ast_to_vec("/test/empty.resi", &mut arena, &ast);

        // Should have valid structure
        let dep_size = u32::from_be_bytes([result[0], result[1], result[2], result[3]]);
        assert_eq!(dep_size, 1);

        // Check marshal magic
        let marshal_start = 4 + 1 + "/test/empty.resi\n".len();
        assert_eq!(result[marshal_start], 0x84);
    }
}
