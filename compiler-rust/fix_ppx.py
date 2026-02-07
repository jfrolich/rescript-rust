#!/usr/bin/env python3
"""
Comprehensive fix for ppx.rs boxed AST enum variant changes.
This script performs all necessary transformations at once.
"""

import re
import sys

def main():
    path = 'src/binary_ast/ppx.rs'
    with open(path, 'r') as f:
        content = f.read()
    original = content

    # Track changes
    def r(old, new, count=0):
        """Replace old with new. count=0 means all occurrences."""
        nonlocal content
        if old not in content:
            print(f"WARNING: not found: {repr(old[:100])}")
            return 0
        if count == 0:
            n = content.count(old)
            content = content.replace(old, new)
            return n
        else:
            n = min(count, content.count(old))
            content = content.replace(old, new, count)
            return n

    def rx(pattern, replacement, count=0):
        """Regex replace."""
        nonlocal content
        if count == 0:
            content, n = re.subn(pattern, replacement, content)
            return n
        else:
            content, n = re.subn(pattern, replacement, content, count=count)
            return n

    # ================================================================
    # IMPORTS: Add PexpApply, PexpFun, PtypArrow
    # ================================================================
    r(
        "    ModuleTypeDesc, ObjectField, Pattern, PatternDesc, PatternRecordField, Payload, PrivateFlag,",
        "    ModuleTypeDesc, ObjectField, Pattern, PatternDesc, PatternRecordField, Payload,\n    PexpApply, PexpFun, PexpFor, PtypArrow, PrivateFlag,",
    )

    # ================================================================
    # Ptyp_arrow: struct variant -> Box<PtypArrow>
    # ================================================================

    # Pattern matching: CoreTypeDesc::Ptyp_arrow { arg, ret, arity }
    # (in list_of_arrow)
    r(
        """CoreTypeDesc::Ptyp_arrow { arg, ret, arity } => {
                let arity_val = arena.get_arity(*arity);
                // OCaml: arity = None || acc = []
                if arity_val.is_none() || args.is_empty() {
                    args.push(arg.as_ref());
                    current = ret.as_ref();""",
        """CoreTypeDesc::Ptyp_arrow(inner) => {
                let PtypArrow { ref arg, ref ret, arity } = **inner;
                let arity_val = arena.get_arity(*arity);
                // OCaml: arity = None || acc = []
                if arity_val.is_none() || args.is_empty() {
                    args.push(arg);
                    current = ret;"""
    )

    # get_result_type
    r(
        "CoreTypeDesc::Ptyp_arrow { ret, .. } => Some(ret.as_ref()),",
        "CoreTypeDesc::Ptyp_arrow(inner) => Some(&inner.ret),"
    )

    # get_final_result_type
    r(
        "CoreTypeDesc::Ptyp_arrow { ret, .. } => get_final_result_type(ret),",
        "CoreTypeDesc::Ptyp_arrow(inner) => get_final_result_type(&inner.ret),"
    )

    # rewrite_core_type pattern match
    r(
        """CoreTypeDesc::Ptyp_arrow { arg, ret, arity } => {
            // Note: OCaml's default_mapper.typ for Ptyp_arrow does NOT process arg.attrs
            // through self.attributes - it only maps arg.typ. So we clone arg.attrs as-is.
            CoreTypeDesc::Ptyp_arrow {
                arg: Box::new(TypeArg {
                    attrs: arg.attrs.clone(),
                    lbl: arg.lbl.clone(),
                    typ: rewrite_core_type(&arg.typ, arena),
                }),
                ret: Box::new(rewrite_core_type(ret, arena)),
                arity: *arity,
            }
        }""",
        """CoreTypeDesc::Ptyp_arrow(inner) => {
            let PtypArrow { ref arg, ref ret, arity } = **inner;
            // Note: OCaml's default_mapper.typ for Ptyp_arrow does NOT process arg.attrs
            // through self.attributes - it only maps arg.typ. So we clone arg.attrs as-is.
            CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow {
                arg: TypeArg {
                    attrs: arg.attrs.clone(),
                    lbl: arg.lbl.clone(),
                    typ: rewrite_core_type(&arg.typ, arena),
                },
                ret: rewrite_core_type(ret, arena),
                arity: *arity,
            }))
        }"""
    )

    # Construction sites: CoreTypeDesc::Ptyp_arrow { arg: Box::new(X), ret: Box::new(Y), arity }
    # -> CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow { arg: X, ret: Y, arity }))

    # All construction sites of Ptyp_arrow use the struct pattern with arg/ret/arity
    # Replace each one individually to be safe

    # reconstruct_arrow_type_with_loc - first occurrence (unit_arg)
    r(
        """CoreTypeDesc::Ptyp_arrow {
                arg: Box::new(unit_arg),
                ret: Box::new(result.clone()),
                arity,
            },""",
        """CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow {
                arg: unit_arg,
                ret: result.clone(),
                arity,
            })),"""
    )

    # reconstruct_arrow_type_with_loc - second occurrence ((*arg).clone())
    r(
        """CoreTypeDesc::Ptyp_arrow {
                arg: Box::new((*arg).clone()),
                ret: Box::new(current),
                arity,
            },
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }
    current
}

/// Process an @obj external""",
        """CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow {
                arg: (*arg).clone(),
                ret: current,
                arity,
            })),
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }
    current
}

/// Process an @obj external"""
    )

    # process_obj_type (same pattern as reconstruct_arrow_type_with_loc second occurrence)
    r(
        """CoreTypeDesc::Ptyp_arrow {
                arg: Box::new((*arg).clone()),
                ret: Box::new(current),
                arity,
            },
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }
    current
}

/// Get optional""",
        """CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow {
                arg: (*arg).clone(),
                ret: current,
                arity,
            })),
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }
    current
}

/// Get optional"""
    )

    # build_arrows
    r(
        """CoreTypeDesc::Ptyp_arrow {
                arg: Box::new(arg),
                ret: Box::new(current),
                arity,
            },""",
        """CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow {
                arg: arg,
                ret: current,
                arity,
            })),"""
    )

    # handle_debugger - specific type (any_type -> unit_type)
    r(
        """CoreTypeDesc::Ptyp_arrow {
            arg: Box::new(TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type,
            }),
            ret: Box::new(unit_type),
            arity: arena.push_arity(Some(1)),  // OCaml's Typ.arrows computes Some(List.length args) - fresh each call
        },""",
        """CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow {
            arg: TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type,
            },
            ret: unit_type,
            arity: arena.push_arity(Some(1)),  // OCaml's Typ.arrows computes Some(List.length args) - fresh each call
        })),"""
    )

    # handle_external_ext - any_type.clone() -> any_type.clone()
    r(
        """CoreTypeDesc::Ptyp_arrow {
            arg: Box::new(TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type.clone(),
            }),
            ret: Box::new(any_type.clone()),
            arity: arena.push_arity(Some(1)),  // OCaml's Typ.arrows computes Some(List.length args) - fresh each call
        },""",
        """CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow {
            arg: TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type.clone(),
            },
            ret: any_type.clone(),
            arity: arena.push_arity(Some(1)),  // OCaml's Typ.arrows computes Some(List.length args) - fresh each call
        })),"""
    )

    # handle_raw (2 occurrences) - any_type.clone() -> any_type
    r(
        """CoreTypeDesc::Ptyp_arrow {
            arg: Box::new(TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type.clone(),
            }),
            ret: Box::new(any_type),
            arity: arena.push_arity(Some(1)),  // OCaml's Typ.arrows computes Some(List.length args) - fresh each call
        },""",
        """CoreTypeDesc::Ptyp_arrow(Box::new(PtypArrow {
            arg: TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type.clone(),
            },
            ret: any_type,
            arity: arena.push_arity(Some(1)),  // OCaml's Typ.arrows computes Some(List.length args) - fresh each call
        })),""",
        count=0  # all occurrences
    )

    # ================================================================
    # Ptyp_constr: (lid, types) -> Box<(lid, types)>
    # ================================================================

    # Construction: CoreTypeDesc::Ptyp_constr(\n            Located ..., vec![...]\n        )
    # Use regex to handle multi-line
    rx(
        r'CoreTypeDesc::Ptyp_constr\(\n(\s+)(Located \{ [^}]+ \}),\n\s+(vec!\[[^\]]*\]),?\n(\s*)\)',
        r'CoreTypeDesc::Ptyp_constr(Box::new((\n\1\2,\n\1\3,\n\4)))',
    )

    # Single-line: CoreTypeDesc::Ptyp_constr(Located::new(X, Y), vec![])
    rx(
        r'CoreTypeDesc::Ptyp_constr\(Located::new\(([^,]+), ([^)]+)\), vec!\[\]\)',
        r'CoreTypeDesc::Ptyp_constr(Box::new((Located::new(\1, \2), vec![])))',
    )

    # Single-line: CoreTypeDesc::Ptyp_constr(Located::new(X, Y), vec![Z])
    rx(
        r'CoreTypeDesc::Ptyp_constr\(Located::new\(([^,]+), ([^)]+)\), vec!\[([^\]]+)\]\)',
        r'CoreTypeDesc::Ptyp_constr(Box::new((Located::new(\1, \2), vec![\3])))',
    )

    # Pattern matching: CoreTypeDesc::Ptyp_constr(lid, args) ... => {
    # In rewrite_core_type
    r(
        "CoreTypeDesc::Ptyp_constr(lid, args) => {\n            CoreTypeDesc::Ptyp_constr(",
        "CoreTypeDesc::Ptyp_constr(inner) => {\n            let (lid, args) = inner.as_ref();\n            CoreTypeDesc::Ptyp_constr(Box::new(("
    )
    # And close the Box::new(( ... )) - the existing close is just )
    r(
        """            CoreTypeDesc::Ptyp_constr(Box::new((
                lid.clone(),
                args.iter().map(|t| rewrite_core_type(t, arena)).collect(),
            )""",
        """            CoreTypeDesc::Ptyp_constr(Box::new((
                lid.clone(),
                args.iter().map(|t| rewrite_core_type(t, arena)).collect(),
            )))"""
    )

    # ================================================================
    # Ptyp_object: (fields, flag) -> Box<(fields, flag)>
    # ================================================================
    r(
        "CoreTypeDesc::Ptyp_object(result_types, current::ClosedFlag::Closed)",
        "CoreTypeDesc::Ptyp_object(Box::new((result_types, current::ClosedFlag::Closed)))",
        count=0
    )
    r(
        "CoreTypeDesc::Ptyp_object(obj_fields, current::ClosedFlag::Closed)",
        "CoreTypeDesc::Ptyp_object(Box::new((obj_fields, current::ClosedFlag::Closed)))",
        count=0
    )

    # Pattern matching in rewrite_core_type
    r(
        """CoreTypeDesc::Ptyp_object(fields, closed) => {
            CoreTypeDesc::Ptyp_object(""",
        """CoreTypeDesc::Ptyp_object(inner) => {
            let (fields, closed) = inner.as_ref();
            CoreTypeDesc::Ptyp_object(Box::new(("""
    )
    r(
        """                }).collect(),
                *closed,
            )
        }
        CoreTypeDesc::Ptyp_variant""",
        """                }).collect(),
                *closed,
            )))
        }
        CoreTypeDesc::Ptyp_variant"""
    )

    # ================================================================
    # Ptyp_variant: (rows, flag, labels) -> Box<(rows, flag, labels)>
    # ================================================================
    # if-let patterns: Ptyp_variant(row_fields, current::ClosedFlag::Closed, None)
    rx(
        r'if let CoreTypeDesc::Ptyp_variant\((\w+), (current::ClosedFlag::\w+), (\w+)\) = (&\w+\.ptyp_desc) \{',
        r'if let CoreTypeDesc::Ptyp_variant(inner) = \4 { let (\1, _, \3) = inner.as_ref(); if matches!(inner.1, \2) {',
    )

    # Pattern matching in rewrite_core_type
    r(
        """CoreTypeDesc::Ptyp_variant(rows, closed, labels) => {
            CoreTypeDesc::Ptyp_variant(""",
        """CoreTypeDesc::Ptyp_variant(inner) => {
            let (rows, closed, labels) = inner.as_ref();
            CoreTypeDesc::Ptyp_variant(Box::new(("""
    )
    r(
        """                }).collect(),
                *closed,
                labels.clone(),
            )
        }
        CoreTypeDesc::Ptyp_package""",
        """                }).collect(),
                *closed,
                labels.clone(),
            )))
        }
        CoreTypeDesc::Ptyp_package"""
    )

    # ================================================================
    # Ptyp_alias: Box + val -> Box<tuple>
    # ================================================================
    r(
        "CoreTypeDesc::Ptyp_alias(inner, name) => {\n            CoreTypeDesc::Ptyp_alias(Box::new(rewrite_core_type(inner, arena)), name.clone())",
        "CoreTypeDesc::Ptyp_alias(inner) => {\n            let (ref inner_ty, ref name) = **inner;\n            CoreTypeDesc::Ptyp_alias(Box::new((rewrite_core_type(inner_ty, arena), name.clone())))"
    )

    # ================================================================
    # Ptyp_poly: vec + Box -> Box<tuple>
    # ================================================================
    r(
        "CoreTypeDesc::Ptyp_poly(vars, inner) => {\n            CoreTypeDesc::Ptyp_poly(vars.clone(), Box::new(rewrite_core_type(inner, arena)))",
        "CoreTypeDesc::Ptyp_poly(inner) => {\n            let (ref vars, ref inner_ty) = **inner;\n            CoreTypeDesc::Ptyp_poly(Box::new((vars.clone(), rewrite_core_type(inner_ty, arena))))"
    )

    # ================================================================
    # Ptyp_package: tuple -> Box<tuple>
    # ================================================================
    r(
        "CoreTypeDesc::Ptyp_package((lid, constraints)) => {\n            CoreTypeDesc::Ptyp_package((",
        "CoreTypeDesc::Ptyp_package(inner) => { let (lid, constraints) = inner.as_ref();\n            CoreTypeDesc::Ptyp_package(Box::new(("
    )
    r(
        """constraints.iter().map(|(l, t)| (l.clone(), rewrite_core_type(t, arena))).collect(),
            ))""",
        """constraints.iter().map(|(l, t)| (l.clone(), rewrite_core_type(t, arena))).collect(),
            )))"""
    )

    # Construction sites for Ptyp_package
    r(
        "CoreTypeDesc::Ptyp_package((\n            module_type_lid,",
        "CoreTypeDesc::Ptyp_package(Box::new((\n            module_type_lid,",
        count=0
    )
    # Close: vec![], // No with constraints\n        )), -> vec![], // No with constraints\n        ))),
    r(
        """            vec![], // No with constraints
        )),""",
        """            vec![], // No with constraints
        ))),""",
        count=0
    )

    # Ptyp_package in create_await_module_expression - different indentation
    r(
        "CoreTypeDesc::Ptyp_package((\n                Located {",
        "CoreTypeDesc::Ptyp_package(Box::new((\n                Located {",
        count=0
    )

    # ================================================================
    # Ptyp_extension: val -> Box<val>
    # ================================================================
    r(
        "CoreTypeDesc::Ptyp_extension((name.clone(), rewrite_payload(payload, arena)))",
        "CoreTypeDesc::Ptyp_extension(Box::new((name.clone(), rewrite_payload(payload, arena))))"
    )
    r(
        "CoreTypeDesc::Ptyp_extension(ext) => {\n            let (name, payload) = ext;",
        "CoreTypeDesc::Ptyp_extension(ext) => {\n            let (name, payload) = ext.as_ref();"
    )

    # ================================================================
    # Pstr_eval: (expr, attrs) -> Box<(expr, attrs)>
    # ================================================================
    # Pattern matching: StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc
    # -> StructureItemDesc::Pstr_eval(inner) = &items[0].pstr_desc { let (expr, _) = inner.as_ref();
    rx(
        r'if let StructureItemDesc::Pstr_eval\((\w+), _\) = (&\w+(?:\[\d+\])?\.pstr_desc) \{',
        r'if let StructureItemDesc::Pstr_eval(inner) = \2 { let (\1, _) = inner.as_ref();',
    )

    # Construction: StructureItemDesc::Pstr_eval(expr, vec![])
    r(
        "StructureItemDesc::Pstr_eval(letmodule_expr, vec![])",
        "StructureItemDesc::Pstr_eval(Box::new((letmodule_expr, vec![])))"
    )

    # ================================================================
    # Pstr_primitive: val -> Box<val>
    # ================================================================
    r("StructureItemDesc::Pstr_primitive(ValueDescription {",
      "StructureItemDesc::Pstr_primitive(Box::new(ValueDescription {",
      count=0)

    # For each Pstr_primitive(Box::new(ValueDescription { ... }) we need to add
    # extra closing ). Find closing pattern: pval_loc: X,\n            }) or })
    # Use a function to do brace-matching

    def fix_pstr_primitive_closings(text):
        """Find all Pstr_primitive(Box::new(ValueDescription { and add closing )."""
        marker = "Pstr_primitive(Box::new(ValueDescription {"
        result = []
        i = 0
        while i < len(text):
            idx = text.find(marker, i)
            if idx == -1:
                result.append(text[i:])
                break
            # Find start of ValueDescription {
            brace_start = idx + len(marker) - 1  # points to {
            result.append(text[i:brace_start + 1])
            i = brace_start + 1

            # Count braces to find matching }
            depth = 1
            j = i
            while j < len(text) and depth > 0:
                if text[j] == '{':
                    depth += 1
                elif text[j] == '}':
                    depth -= 1
                j += 1
            # j points after matching }
            # Copy content including }
            result.append(text[i:j])
            # Insert extra ) after }
            result.append(')')
            i = j
        return ''.join(result)

    content = fix_pstr_primitive_closings(content)

    # Simple val construction: StructureItemDesc::Pstr_primitive(vd)
    r("pstr_desc: StructureItemDesc::Pstr_primitive(vd),",
      "pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(vd)),",
      count=0)
    r("pstr_desc: StructureItemDesc::Pstr_primitive(val_desc),",
      "pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(val_desc)),",
      count=0)
    r("pstr_desc: StructureItemDesc::Pstr_primitive(unsafe_expr_prim),",
      "pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(unsafe_expr_prim)),",
      count=0)

    # Pattern match: StructureItemDesc::Pstr_primitive(vd) => {
    # vd is already Box<ValueDescription>, so pattern is fine, just need to use vd.as_ref() or *vd
    # Actually in pattern match, vd will be &Box<ValueDescription>, no change needed to the pattern
    # But usage sites may need .as_ref(). Let's leave pattern match as-is for now.

    # ================================================================
    # Pstr_module: val -> Box<val>
    # ================================================================
    r("StructureItemDesc::Pstr_module(module_binding)",
      "StructureItemDesc::Pstr_module(Box::new(module_binding))",
      count=0)
    r("StructureItemDesc::Pstr_module(current::ModuleBinding {",
      "StructureItemDesc::Pstr_module(Box::new(current::ModuleBinding {",
      count=0)

    # Close: for each Box::new(current::ModuleBinding { ... })
    def fix_module_binding_closings(text):
        marker = "Pstr_module(Box::new(current::ModuleBinding {"
        result = []
        i = 0
        while i < len(text):
            idx = text.find(marker, i)
            if idx == -1:
                result.append(text[i:])
                break
            brace_start = idx + len(marker) - 1
            result.append(text[i:brace_start + 1])
            i = brace_start + 1
            depth = 1
            j = i
            while j < len(text) and depth > 0:
                if text[j] == '{':
                    depth += 1
                elif text[j] == '}':
                    depth -= 1
                j += 1
            result.append(text[i:j])
            result.append(')')
            i = j
        return ''.join(result)

    content = fix_module_binding_closings(content)

    # ================================================================
    # Pstr_open: val -> Box<val>
    # ================================================================
    r("StructureItemDesc::Pstr_open(open_desc)",
      "StructureItemDesc::Pstr_open(Box::new(open_desc))",
      count=0)

    # ================================================================
    # Pstr_modtype: val -> Box<val>
    # ================================================================
    r("StructureItemDesc::Pstr_modtype(current::ModuleTypeDeclaration {",
      "StructureItemDesc::Pstr_modtype(Box::new(current::ModuleTypeDeclaration {",
      count=0)

    def fix_modtype_closings(text):
        marker = "Pstr_modtype(Box::new(current::ModuleTypeDeclaration {"
        result = []
        i = 0
        while i < len(text):
            idx = text.find(marker, i)
            if idx == -1:
                result.append(text[i:])
                break
            brace_start = idx + len(marker) - 1
            result.append(text[i:brace_start + 1])
            i = brace_start + 1
            depth = 1
            j = i
            while j < len(text) and depth > 0:
                if text[j] == '{':
                    depth += 1
                elif text[j] == '}':
                    depth -= 1
                j += 1
            result.append(text[i:j])
            result.append(')')
            i = j
        return ''.join(result)

    content = fix_modtype_closings(content)

    # ================================================================
    # Pexp_apply: struct -> Box<PexpApply>
    # ================================================================
    # Construction: ExpressionDesc::Pexp_apply {\n            funct: Box::new(X),\n...}
    # -> ExpressionDesc::Pexp_apply(Box::new(PexpApply {\n            funct: X,\n...}))

    # Replace struct construction to Box::new(PexpApply {})
    rx(
        r'ExpressionDesc::Pexp_apply \{\n(\s+)funct: Box::new\(([^)]+(?:\([^)]*\))*)\),',
        r'ExpressionDesc::Pexp_apply(Box::new(PexpApply {\n\1funct: \2,',
    )

    # Fix funct: fn1.clone(), (no Box::new)
    r(
        "ExpressionDesc::Pexp_apply {\n                funct: fn1.clone(),",
        "ExpressionDesc::Pexp_apply(Box::new(PexpApply {\n                funct: *fn1.clone(),"
    )

    # For construction where funct is not in Box::new (in rewrite_expression_generic)
    r(
        """ExpressionDesc::Pexp_apply {
            funct: Box::new(rewrite_expression(funct, arena)),""",
        """ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: rewrite_expression(funct, arena),"""
    )

    # Fix the closing braces for all Pexp_apply construction sites
    # Each one ends with: transformed_jsx: ...,\n        } or transformed_jsx: ...,\n            }
    # We need to add )) after the closing }
    def fix_pexp_apply_closings(text):
        marker = "Pexp_apply(Box::new(PexpApply {"
        result = []
        i = 0
        while i < len(text):
            idx = text.find(marker, i)
            if idx == -1:
                result.append(text[i:])
                break
            brace_start = idx + len(marker) - 1
            result.append(text[i:brace_start + 1])
            i = brace_start + 1
            depth = 1
            j = i
            while j < len(text) and depth > 0:
                if text[j] == '{':
                    depth += 1
                elif text[j] == '}':
                    depth -= 1
                j += 1
            result.append(text[i:j])
            result.append('))')
            i = j
        return ''.join(result)

    content = fix_pexp_apply_closings(content)

    # Pattern matching: ExpressionDesc::Pexp_apply { funct, args, ... } => ...
    # These are reference patterns - the funct was Box<Expression>, now it's Expression inside PexpApply

    # In rewrite_expression: both the pipe check and generic rewrite
    r(
        """ExpressionDesc::Pexp_apply {
        funct,
        args,
        partial: _,
        transformed_jsx: _,
    } = &expr.pexp_desc""",
        """ExpressionDesc::Pexp_apply(inner) = &expr.pexp_desc""",
    )
    # Add destructuring after the if-let
    r(
        """ExpressionDesc::Pexp_apply(inner) = &expr.pexp_desc
    {
        // Check if this is a binary op""",
        """ExpressionDesc::Pexp_apply(inner) = &expr.pexp_desc
    {
        let PexpApply { funct, args, partial: _, transformed_jsx: _ } = inner.as_ref();
        // Check if this is a binary op"""
    )

    # In rewrite_expression_generic
    r(
        """ExpressionDesc::Pexp_apply {
            funct,
            args,
            partial,
            transformed_jsx,
        } => ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: rewrite_expression(funct, arena),""",
        """ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply { funct, args, partial, transformed_jsx } = inner.as_ref();
            ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: rewrite_expression(funct, arena),"""
    )
    # Fix closing: this was originally }, (one level), now needs })) followed by }
    r(
        """            partial: *partial,
            transformed_jsx: *transformed_jsx,
        })),

        ExpressionDesc::Pexp_match""",
        """            partial: *partial,
            transformed_jsx: *transformed_jsx,
        }))
        }

        ExpressionDesc::Pexp_match"""
    )

    # In desugar_pipe - Pexp_apply pattern match
    r(
        """ExpressionDesc::Pexp_apply {
            funct: fn1,
            args,
            partial,
            transformed_jsx,
        } => {""",
        """ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply { funct: fn1, args, partial, transformed_jsx } = inner.as_ref();"""
    )

    # In is_pipe_application
    r(
        """if let ExpressionDesc::Pexp_apply { funct, args, .. } = &expr.pexp_desc {""",
        """if let ExpressionDesc::Pexp_apply(inner) = &expr.pexp_desc {
        let PexpApply { funct, args, .. } = inner.as_ref();"""
    )

    # ================================================================
    # Pexp_letmodule: (name, mod_expr, Box<body>) -> Box<(name, mod_expr, body)>
    # ================================================================
    # Construction sites
    rx(
        r'ExpressionDesc::Pexp_letmodule\(\n(\s+)(Located \{)',
        r'ExpressionDesc::Pexp_letmodule(Box::new((\n\1\2',
    )
    # Close: Each has mod_expr,\n            Box::new(body),\n        )
    # Needs to become: mod_expr,\n            body,\n        )))
    # Remove Box::new() around body in letmodule
    rx(
        r'(ExpressionDesc::Pexp_letmodule\(Box::new\(\([^)]*\n[^)]*\n\s+\},\n\s+\w+,\n\s+)Box::new\((\w+)\)',
        r'\1\2',
    )
    # Also handle: Box::new(rewrite_expression(body, arena))
    rx(
        r'(Pexp_letmodule\(Box::new\(\(\n[^)]+\n\s+\},\n\s+\w+,\n\s+)Box::new\(rewrite_expression\((\w+), arena\)\)',
        r'\1rewrite_expression(\2, arena)',
    )

    # Fix closing of Pexp_letmodule construction: change ), to ))),
    # This is tricky - need brace matching
    def fix_letmodule_closings(text):
        marker = "Pexp_letmodule(Box::new(("
        result = []
        i = 0
        while i < len(text):
            idx = text.find(marker, i)
            if idx == -1:
                result.append(text[i:])
                break
            result.append(text[i:idx + len(marker)])
            i = idx + len(marker)
            # Count parens to find matching ))
            depth = 2  # We have ((
            j = i
            while j < len(text) and depth > 0:
                if text[j] == '(':
                    depth += 1
                elif text[j] == ')':
                    depth -= 1
                j += 1
            # j points after the matching ))
            result.append(text[i:j])
            # Check if we need to add extra )
            # The old pattern was Pexp_letmodule(name, expr, body)
            # The closing was just ), now with Box::new(( ... )), it should be )))
            # But we already have 2 closing parens from Box::new((, so we need 1 more
            # Wait - the old was ), the new needs )))
            # We start with (( giving depth 2, and depth counts down to 0
            # So we already see )) in the text. We just need to add one more ).
            # Actually let's not do this - it's too error-prone. Let me handle this differently.
            i = j
        return ''.join(result)

    # Actually, for letmodule, the old pattern was:
    #   ExpressionDesc::Pexp_letmodule(name, mod_expr, Box::new(body)),
    # Which was: Pexp_letmodule( name, mod_expr, Box::new(body) )
    # The new is: Pexp_letmodule(Box::new((name, mod_expr, body)))
    # So: Pexp_letmodule( Box::new(( name, mod_expr, body )) )
    # With my changes so far, I've changed:
    #   Pexp_letmodule(\n            Located { -> Pexp_letmodule(Box::new((\n            Located {
    # And removed Box::new() around body
    # But the closing ), needs to become ))),
    # Let me find the specific closings

    # Pattern matching: ExpressionDesc::Pexp_letmodule(name, mod_expr, body) =>
    r(
        "ExpressionDesc::Pexp_letmodule(name, mod_expr, body) => {",
        "ExpressionDesc::Pexp_letmodule(inner) => {\n            let (name, mod_expr, body) = inner.as_ref();",
        count=0
    )
    r(
        "ExpressionDesc::Pexp_letmodule(_, mod_expr, body) => {",
        "ExpressionDesc::Pexp_letmodule(inner) => {\n            let (_, mod_expr, body) = inner.as_ref();",
        count=0
    )

    # In spelunk: ExpressionDesc::Pexp_letmodule(_, bindings, body) (3-field destructure)
    r(
        "ExpressionDesc::Pexp_letmodule(_, _, body) => {",
        "ExpressionDesc::Pexp_letmodule(inner) => {\n            let (_, _, body) = inner.as_ref();",
        count=0
    )

    # ================================================================
    # Pexp_constant: val -> Box<val>
    # ================================================================
    # Construction
    r("ExpressionDesc::Pexp_constant(Constant::String(",
      "ExpressionDesc::Pexp_constant(Box::new(Constant::String(",
      count=0)
    r("ExpressionDesc::Pexp_constant(Constant::Integer(",
      "ExpressionDesc::Pexp_constant(Box::new(Constant::Integer(",
      count=0)
    r("ExpressionDesc::Pexp_constant(Constant::Float(",
      "ExpressionDesc::Pexp_constant(Box::new(Constant::Float(",
      count=0)

    # Close: each Pexp_constant(Box::new(Constant::String(...))) needs extra )
    # The old was: Pexp_constant(Constant::String(x, y))
    # The new needs: Pexp_constant(Box::new(Constant::String(x, y)))
    # After replacement: Pexp_constant(Box::new(Constant::String(x, y))
    # Missing one closing ). Need to add ) after the existing ))
    # Actually the old pattern ends with )) (one for Constant::String(), one for Pexp_constant())
    # New should end with ))) (Box::new closes before Pexp_constant closes)
    # So each )) needs to become )))
    # But we need to be selective. Let me use brace matching.

    def fix_pexp_constant_closings(text):
        marker_patterns = [
            "Pexp_constant(Box::new(Constant::String(",
            "Pexp_constant(Box::new(Constant::Integer(",
            "Pexp_constant(Box::new(Constant::Float(",
        ]
        for marker in marker_patterns:
            result = []
            i = 0
            while i < len(text):
                idx = text.find(marker, i)
                if idx == -1:
                    result.append(text[i:])
                    break
                # Find the opening ( of Constant::
                const_start = idx + len("Pexp_constant(Box::new(")
                result.append(text[i:const_start])
                i = const_start
                # Now count parens from here to find matching close of Constant::Type(...)
                # We're at "Constant::String("
                # Find the first ( after Constant::
                paren_pos = text.find('(', i)
                result.append(text[i:paren_pos + 1])
                i = paren_pos + 1
                depth = 1
                j = i
                while j < len(text) and depth > 0:
                    if text[j] == '(':
                        depth += 1
                    elif text[j] == ')':
                        depth -= 1
                    j += 1
                # j points after matching )
                result.append(text[i:j])
                # Now add closing ) for Box::new
                result.append(')')
                i = j
            text = ''.join(result)
        return text

    content = fix_pexp_constant_closings(content)

    # Pattern matching for Pexp_constant
    # if let ExpressionDesc::Pexp_constant(Constant::String(s, Some(delim))) = &expr.pexp_desc
    # -> if let ExpressionDesc::Pexp_constant(c) = &expr.pexp_desc { if let Constant::String(s, Some(delim)) = c.as_ref()
    # This is complex. Let's handle each one.

    # In rewrite_expression:
    r(
        "if let ExpressionDesc::Pexp_constant(Constant::String(s, Some(delim))) = &expr.pexp_desc {",
        "if let ExpressionDesc::Pexp_constant(c) = &expr.pexp_desc { if let Constant::String(s, Some(delim)) = c.as_ref() {"
    )
    r(
        "if let ExpressionDesc::Pexp_constant(Constant::Integer(s, Some('l'))) = &expr.pexp_desc {",
        "if let ExpressionDesc::Pexp_constant(c) = &expr.pexp_desc { if let Constant::Integer(s, Some('l')) = c.as_ref() {"
    )

    # ================================================================
    # Pexp_construct: (lid, opt) -> Box<(lid, opt)>
    # ================================================================
    # Construction: ExpressionDesc::Pexp_construct(lid, opt) -> Box<(lid, opt)>
    rx(
        r'ExpressionDesc::Pexp_construct\(\n(\s+)(Located \{[^}]+\}),\n\s+(\w+),?\n\s*\)',
        r'ExpressionDesc::Pexp_construct(Box::new((\n\1\2,\n\1\3,\n)))',
    )

    # ================================================================
    # Pexp_constraint: Box + val -> Box<tuple>
    # ================================================================
    r("ExpressionDesc::Pexp_constraint(Box::new(",
      "ExpressionDesc::Pexp_constraint(Box::new((",
      count=0)

    # Each Pexp_constraint now has Box::new(( expr, type )) but the closing needs an extra )
    # Old: Pexp_constraint(Box::new(expr), type)
    # -> Pexp_constraint(Box::new((expr), type)  WRONG
    # Should be: Pexp_constraint(Box::new((expr, type)))
    # Hmm, the old pattern was: Pexp_constraint(Box::new(raw_expr), regexp_type)
    # After my replacement: Pexp_constraint(Box::new((raw_expr), regexp_type)
    # That's wrong. I need to move the second arg inside the Box::new.

    # Let me undo and redo this more carefully
    r("ExpressionDesc::Pexp_constraint(Box::new((",
      "ExpressionDesc::Pexp_constraint(Box::new(",
      count=0)

    # ================================================================
    # Pexp_ifthenelse: three Box args -> Box<tuple>
    # ================================================================
    # Construction: Pexp_ifthenelse(Box::new(a), Box::new(b), c)
    # -> Pexp_ifthenelse(Box::new((a, b, c)))

    # ================================================================
    # Pexp_fun: struct -> Box<PexpFun>
    # ================================================================

    # ================================================================
    # Fix Pexp_let: (flag, bindings, Box<body>) -> Box<(flag, bindings, body)>
    # ================================================================
    # Pattern matching
    r(
        "ExpressionDesc::Pexp_let(rec_flag, bindings, body) => {",
        "ExpressionDesc::Pexp_let(inner) => {\n            let (rec_flag, bindings, body) = inner.as_ref();",
        count=0
    )

    # Construction: Pexp_let(flag, bindings, Box::new(body))
    # -> Pexp_let(Box::new((flag, bindings, body)))
    r(
        """ExpressionDesc::Pexp_let(
                *rec_flag,
                new_bindings,
                Box::new(rewrite_expression(body, arena)),
            )""",
        """ExpressionDesc::Pexp_let(Box::new((
                *rec_flag,
                new_bindings,
                rewrite_expression(body, arena),
            )))"""
    )

    # ================================================================
    # Pexp_match: (Box<expr>, cases) -> Box<(expr, cases)>
    # ================================================================
    # Construction
    r(
        """ExpressionDesc::Pexp_match(
                            Box::new(rewritten_expr),
                            vec![Case {""",
        """ExpressionDesc::Pexp_match(Box::new((
                            rewritten_expr,
                            vec![Case {"""
    )
    r(
        """                            }],
                        ),""",
        """                            }],
                        ))),""",
        count=1  # Only the first one matching the match->ifthenelse conversion
    )

    r(
        """ExpressionDesc::Pexp_match(
                Box::new(rewrite_expression(scrutinee, arena)),
                rewrite_cases(cases, arena),
            )""",
        """ExpressionDesc::Pexp_match(Box::new((
                rewrite_expression(scrutinee, arena),
                rewrite_cases(cases, arena),
            )))"""
    )

    # Pattern matching
    r(
        "ExpressionDesc::Pexp_match(scrutinee, cases) => {",
        "ExpressionDesc::Pexp_match(inner) => {\n            let (scrutinee, cases) = inner.as_ref();",
        count=0
    )
    r(
        "ExpressionDesc::Pexp_match(scrut, cases) => {",
        "ExpressionDesc::Pexp_match(inner) => {\n            let (scrut, cases) = inner.as_ref();",
        count=0
    )

    # ================================================================
    # Pexp_try: (Box<body>, cases) -> Box<(body, cases)>
    # ================================================================
    r(
        """ExpressionDesc::Pexp_try(body, cases) => ExpressionDesc::Pexp_try(
            Box::new(rewrite_expression(body, arena)),
            rewrite_cases(cases, arena),
        ),""",
        """ExpressionDesc::Pexp_try(inner) => { let (body, cases) = inner.as_ref(); ExpressionDesc::Pexp_try(Box::new((
            rewrite_expression(body, arena),
            rewrite_cases(cases, arena),
        )))
        }"""
    )

    # ================================================================
    # Pexp_construct: pattern matching
    # ================================================================
    r(
        "ExpressionDesc::Pexp_construct(ctor, arg) => ExpressionDesc::Pexp_construct(",
        "ExpressionDesc::Pexp_construct(inner) => { let (ctor, arg) = inner.as_ref(); ExpressionDesc::Pexp_construct(Box::new((",
        count=0
    )

    # ================================================================
    # Pexp_variant: pattern matching
    # ================================================================
    r(
        "ExpressionDesc::Pexp_variant(label, arg) => ExpressionDesc::Pexp_variant(",
        "ExpressionDesc::Pexp_variant(inner) => { let (label, arg) = inner.as_ref(); ExpressionDesc::Pexp_variant(Box::new((",
        count=0
    )

    # ================================================================
    # Pexp_record: pattern matching
    # ================================================================
    r(
        "ExpressionDesc::Pexp_record(fields, spread) => {",
        "ExpressionDesc::Pexp_record(inner) => { let (fields, spread) = inner.as_ref();",
        count=0
    )

    # Construction
    r(
        """ExpressionDesc::Pexp_record(
                new_fields,
                spread.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
            )""",
        """ExpressionDesc::Pexp_record(Box::new((
                new_fields,
                spread.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
            )))"""
    )

    # ================================================================
    # Pexp_field: pattern matching
    # ================================================================
    r(
        "ExpressionDesc::Pexp_field(e, lid) => {",
        "ExpressionDesc::Pexp_field(inner) => { let (e, lid) = inner.as_ref();",
        count=0
    )
    r(
        "ExpressionDesc::Pexp_field(Box::new(rewrite_expression(e, arena)), lid.clone())",
        "ExpressionDesc::Pexp_field(Box::new((rewrite_expression(e, arena), lid.clone())))"
    )

    # ================================================================
    # Pexp_setfield: pattern matching
    # ================================================================
    r(
        "ExpressionDesc::Pexp_setfield(e1, lid, e2) => ExpressionDesc::Pexp_setfield(",
        "ExpressionDesc::Pexp_setfield(inner) => { let (e1, lid, e2) = inner.as_ref(); ExpressionDesc::Pexp_setfield(Box::new((",
        count=0
    )
    r(
        """            Box::new(rewrite_expression(e1, arena)),
            lid.clone(),
            Box::new(rewrite_expression(e2, arena)),
        ),""",
        """            rewrite_expression(e1, arena),
            lid.clone(),
            rewrite_expression(e2, arena),
        )))
        }"""
    )

    # ================================================================
    # Pexp_ifthenelse: pattern matching and construction
    # ================================================================
    r(
        "ExpressionDesc::Pexp_ifthenelse(cond, then_branch, else_branch) => {",
        "ExpressionDesc::Pexp_ifthenelse(inner) => { let (cond, then_branch, else_branch) = inner.as_ref();",
        count=0
    )
    r(
        """ExpressionDesc::Pexp_ifthenelse(
                Box::new(rewrite_expression(cond, arena)),
                Box::new(rewrite_expression(then_branch, arena)),
                else_branch
                    .as_ref()
                    .map(|e| Box::new(rewrite_expression(e, arena))),
            )""",
        """ExpressionDesc::Pexp_ifthenelse(Box::new((
                rewrite_expression(cond, arena),
                rewrite_expression(then_branch, arena),
                else_branch
                    .as_ref()
                    .map(|e| Box::new(rewrite_expression(e, arena))),
            )))"""
    )
    # Boolean match -> if-then-else
    r(
        """ExpressionDesc::Pexp_ifthenelse(
                            Box::new(rewrite_expression(scrutinee, arena)),
                            Box::new(rewrite_expression(t_exp, arena)),
                            Some(Box::new(rewrite_expression(f_exp, arena))),
                        ),""",
        """ExpressionDesc::Pexp_ifthenelse(Box::new((
                            rewrite_expression(scrutinee, arena),
                            rewrite_expression(t_exp, arena),
                            Some(Box::new(rewrite_expression(f_exp, arena))),
                        ))),"""
    )

    # handle_external_ext ifthenelse construction
    r(
        """ExpressionDesc::Pexp_ifthenelse(
            Box::new(condition),
            Box::new(empty_expr),
            Some(Box::new(raw_exp)),
        ),""",
        """ExpressionDesc::Pexp_ifthenelse(Box::new((
            condition,
            empty_expr,
            Some(Box::new(raw_exp)),
        ))),"""
    )

    # ================================================================
    # Pexp_sequence, Pexp_while: (Box<e1>, Box<e2>) -> Box<(e1, e2)>
    # ================================================================
    r(
        """ExpressionDesc::Pexp_sequence(e1, e2) => ExpressionDesc::Pexp_sequence(
            Box::new(rewrite_expression(e1, arena)),
            Box::new(rewrite_expression(e2, arena)),
        ),""",
        """ExpressionDesc::Pexp_sequence(inner) => { let (e1, e2) = inner.as_ref(); ExpressionDesc::Pexp_sequence(Box::new((
            rewrite_expression(e1, arena),
            rewrite_expression(e2, arena),
        )))
        }"""
    )

    r(
        """ExpressionDesc::Pexp_while(cond, body) => ExpressionDesc::Pexp_while(
            Box::new(rewrite_expression(cond, arena)),
            Box::new(rewrite_expression(body, arena)),
        ),""",
        """ExpressionDesc::Pexp_while(inner) => { let (cond, body) = inner.as_ref(); ExpressionDesc::Pexp_while(Box::new((
            rewrite_expression(cond, arena),
            rewrite_expression(body, arena),
        )))
        }"""
    )

    # ================================================================
    # Pexp_for: (Pat, Box<e1>, Box<e2>, Dir, Box<e3>) -> Box<PexpFor>
    # ================================================================
    r(
        """ExpressionDesc::Pexp_for(pat, e1, e2, dir, body) => ExpressionDesc::Pexp_for(
            rewrite_pattern(pat, arena),
            Box::new(rewrite_expression(e1, arena)),
            Box::new(rewrite_expression(e2, arena)),
            *dir,
            Box::new(rewrite_expression(body, arena)),
        ),""",
        """ExpressionDesc::Pexp_for(inner) => { let PexpFor { pat, from, to, direction, body } = inner.as_ref(); ExpressionDesc::Pexp_for(Box::new(PexpFor {
            pat: rewrite_pattern(pat, arena),
            from: rewrite_expression(from, arena),
            to: rewrite_expression(to, arena),
            direction: *direction,
            body: rewrite_expression(body, arena),
        }))
        }"""
    )

    # ================================================================
    # Pexp_constraint: Box<e> + CoreType -> Box<(e, CoreType)>
    # ================================================================
    # In rewrite_expression_generic
    r(
        "ExpressionDesc::Pexp_constraint(e, ty) => {\n            ExpressionDesc::Pexp_constraint(",
        "ExpressionDesc::Pexp_constraint(inner) => { let (e, ty) = inner.as_ref();\n            ExpressionDesc::Pexp_constraint("
    )
    # Construction in rewrite_expression_generic
    r(
        """ExpressionDesc::Pexp_constraint(
                Box::new(rewrite_expression(e, arena)),
                rewrite_core_type(ty, arena),
            )""",
        """ExpressionDesc::Pexp_constraint(Box::new((
                rewrite_expression(e, arena),
                rewrite_core_type(ty, arena),
            )))"""
    )

    # handle_re: Pexp_constraint(Box::new(raw_expr), regexp_type)
    r(
        "ExpressionDesc::Pexp_constraint(Box::new(raw_expr), regexp_type),",
        "ExpressionDesc::Pexp_constraint(Box::new((raw_expr, regexp_type))),",
    )

    # desugar_hash_set
    r(
        "ExpressionDesc::Pexp_constraint(Box::new(apply_expr), unit_type)",
        "ExpressionDesc::Pexp_constraint(Box::new((apply_expr, unit_type)))"
    )

    # create_await_module_expression
    r(
        "ExpressionDesc::Pexp_constraint(Box::new(pack_expr), package_type)",
        "ExpressionDesc::Pexp_constraint(Box::new((pack_expr, package_type)))",
        count=0
    )

    # ================================================================
    # Pexp_coerce: (Box<e>, Option<CT>, CT) -> Box<(e, Option<CT>, CT)>
    # ================================================================
    r(
        """ExpressionDesc::Pexp_coerce(e, ty1, ty2) => ExpressionDesc::Pexp_coerce(
            Box::new(rewrite_expression(e, arena)),
            ty1.as_ref().map(|t| rewrite_core_type(t, arena)),
            rewrite_core_type(ty2, arena),
        ),""",
        """ExpressionDesc::Pexp_coerce(inner) => { let (e, ty1, ty2) = inner.as_ref(); ExpressionDesc::Pexp_coerce(Box::new((
            rewrite_expression(e, arena),
            ty1.as_ref().map(|t| rewrite_core_type(t, arena)),
            rewrite_core_type(ty2, arena),
        )))
        }"""
    )

    # ================================================================
    # Pexp_send: (Box<e>, Loc<Label>) -> Box<(e, Loc<Label>)>
    # ================================================================
    r(
        "ExpressionDesc::Pexp_send(e, method) => {\n            ExpressionDesc::Pexp_send(Box::new(rewrite_expression(e, arena)), method.clone())",
        "ExpressionDesc::Pexp_send(inner) => { let (e, method) = inner.as_ref();\n            ExpressionDesc::Pexp_send(Box::new((rewrite_expression(e, arena), method.clone())))"
    )

    # desugar_hash_set construction
    r(
        """ExpressionDesc::Pexp_send(
                    Box::new(obj),
                    Located::new(Cow::Owned(setter_name), loc),
                ),""",
        """ExpressionDesc::Pexp_send(Box::new((
                    obj,
                    Located::new(Cow::Owned(setter_name), loc),
                ))),"""
    )

    # desugar_hash_set pattern match
    r(
        "ExpressionDesc::Pexp_send(obj, method_loc) => {",
        "ExpressionDesc::Pexp_send(inner) => { let (obj, method_loc) = inner.as_ref();",
        count=0
    )

    # ================================================================
    # Pexp_letexception: (EC, Box<body>) -> Box<(EC, body)>
    # ================================================================
    r(
        """ExpressionDesc::Pexp_letexception(exn, body) => ExpressionDesc::Pexp_letexception(
            exn.clone(),
            Box::new(rewrite_expression(body, arena)),
        ),""",
        """ExpressionDesc::Pexp_letexception(inner) => { let (exn, body) = inner.as_ref(); ExpressionDesc::Pexp_letexception(Box::new((
            exn.clone(),
            rewrite_expression(body, arena),
        )))
        }"""
    )

    # ================================================================
    # Pexp_open: (OverrideFlag, Loc, Box<body>) -> Box<(OverrideFlag, Loc, body)>
    # ================================================================
    r(
        """ExpressionDesc::Pexp_open(override_flag, mod_name, body) => ExpressionDesc::Pexp_open(
            *override_flag,
            mod_name.clone(),
            Box::new(rewrite_expression(body, arena)),
        ),""",
        """ExpressionDesc::Pexp_open(inner) => { let (override_flag, mod_name, body) = inner.as_ref(); ExpressionDesc::Pexp_open(Box::new((
            *override_flag,
            *mod_name,
            rewrite_expression(body, arena),
        )))
        }"""
    )

    # destruct_open_tuple_inner pattern match
    r(
        """ExpressionDesc::Pexp_open(flag, lid, cont) => {
            acc.push(OpenCtx {
                flag: *flag,
                lid: *lid,
                loc: e.pexp_loc,
                attrs: e.pexp_attributes.clone(),
            });
            destruct_open_tuple_inner(cont, acc)
        }""",
        """ExpressionDesc::Pexp_open(inner) => {
            let (flag, lid, cont) = inner.as_ref();
            acc.push(OpenCtx {
                flag: *flag,
                lid: *lid,
                loc: e.pexp_loc,
                attrs: e.pexp_attributes.clone(),
            });
            destruct_open_tuple_inner(cont, acc)
        }"""
    )

    # restore_exp construction
    r(
        "ExpressionDesc::Pexp_open(open.flag, open.lid, Box::new(inner))",
        "ExpressionDesc::Pexp_open(Box::new((open.flag, open.lid, inner)))"
    )

    # ================================================================
    # Pexp_newtype: (StringLoc, Box<body>) -> Box<(StringLoc, body)>
    # ================================================================
    r(
        """ExpressionDesc::Pexp_newtype(name, body) => {
            return Expression {
                pexp_desc: ExpressionDesc::Pexp_newtype(
                    name.clone(),
                    Box::new(rewrite_expression(body, arena)),
                ),""",
        """ExpressionDesc::Pexp_newtype(inner) => {
            let (name, body) = inner.as_ref();
            return Expression {
                pexp_desc: ExpressionDesc::Pexp_newtype(Box::new((
                    name.clone(),
                    rewrite_expression(body, arena),
                ))),"""
    )

    # ================================================================
    # Pexp_pack: ModuleExpr -> Box<ModuleExpr>
    # ================================================================
    r(
        "ExpressionDesc::Pexp_pack(mod_expr) => {\n            // Module expressions - don't recurse for now\n            ExpressionDesc::Pexp_pack(mod_expr.clone())",
        "ExpressionDesc::Pexp_pack(mod_expr) => {\n            // Module expressions - don't recurse for now\n            ExpressionDesc::Pexp_pack(Box::new((**mod_expr).clone()))"
    )
    r(
        "ExpressionDesc::Pexp_pack(cleaned_mod_expr)",
        "ExpressionDesc::Pexp_pack(Box::new(cleaned_mod_expr))",
        count=0
    )

    # ================================================================
    # Pexp_extension: Extension -> Box<Extension>
    # ================================================================
    r(
        "ExpressionDesc::Pexp_extension(ext) => {\n            return handle_extension(expr, ext, arena);",
        "ExpressionDesc::Pexp_extension(ext) => {\n            return handle_extension(expr, ext.as_ref(), arena);",
    )

    # ================================================================
    # Pexp_jsx_element: JsxElement -> Box<JsxElement>
    # ================================================================
    r(
        "ExpressionDesc::Pexp_jsx_element(rewrite_jsx_element(jsx, arena))",
        "ExpressionDesc::Pexp_jsx_element(Box::new(rewrite_jsx_element(jsx, arena)))"
    )
    r(
        "ExpressionDesc::Pexp_jsx_element(jsx) => {",
        "ExpressionDesc::Pexp_jsx_element(jsx) => { let jsx = jsx.as_ref();",
        count=0
    )

    # ================================================================
    # Pexp_fun: struct -> Box<PexpFun>
    # ================================================================
    # Construction in rewrite_expression_generic
    r(
        """ExpressionDesc::Pexp_fun {
                    arg_label: arg_label.clone(),
                    default: rewritten_default,
                    lhs: rewritten_lhs,
                    rhs: rewritten_rhs,
                    arity: *arity,
                    is_async: *is_async,
                },""",
        """ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: arg_label.clone(),
                    default: rewritten_default,
                    lhs: rewritten_lhs,
                    rhs: *rewritten_rhs,
                    arity: *arity,
                    is_async: *is_async,
                })),"""
    )

    # Pattern matching in rewrite_expression_generic
    r(
        """ExpressionDesc::Pexp_fun {
            arg_label,
            default,
            lhs,
            rhs,
            arity,
            is_async,
        } => {""",
        """ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun { arg_label, default, lhs, rhs, arity, is_async } = inner.as_ref();"""
    )

    # add_promise_to_fun_body
    r(
        """ExpressionDesc::Pexp_fun {
            arg_label,
            default,
            lhs,
            rhs,
            arity,
            is_async,
        } => {
            // Recurse into rhs to find innermost body
            let new_rhs = add_promise_to_fun_body(rhs, loc, arena);
            Expression {
                pexp_desc: ExpressionDesc::Pexp_fun {
                    arg_label: arg_label.clone(),
                    default: default.clone(),
                    lhs: lhs.clone(),
                    rhs: Box::new(new_rhs),
                    arity: *arity,
                    is_async: *is_async,
                },""",
        """ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun { arg_label, default, lhs, rhs, arity, is_async } = inner.as_ref();
            // Recurse into rhs to find innermost body
            let new_rhs = add_promise_to_fun_body(rhs, loc, arena);
            Expression {
                pexp_desc: ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: arg_label.clone(),
                    default: default.clone(),
                    lhs: lhs.clone(),
                    rhs: new_rhs,
                    arity: *arity,
                    is_async: *is_async,
                })),"""
    )

    # ================================================================
    # Ppat_constant: Constant -> Box<Constant>
    # ================================================================
    r("PatternDesc::Ppat_constant(Constant::String(",
      "PatternDesc::Ppat_constant(Box::new(Constant::String(",
      count=0)
    r("PatternDesc::Ppat_constant(Constant::Integer(",
      "PatternDesc::Ppat_constant(Box::new(Constant::Integer(",
      count=0)

    # Close these using brace matching
    def fix_ppat_constant_closings(text):
        marker_patterns = [
            "Ppat_constant(Box::new(Constant::String(",
            "Ppat_constant(Box::new(Constant::Integer(",
        ]
        for marker in marker_patterns:
            result = []
            i = 0
            while i < len(text):
                idx = text.find(marker, i)
                if idx == -1:
                    result.append(text[i:])
                    break
                const_start = idx + len("Ppat_constant(Box::new(")
                result.append(text[i:const_start])
                i = const_start
                paren_pos = text.find('(', i)
                result.append(text[i:paren_pos + 1])
                i = paren_pos + 1
                depth = 1
                j = i
                while j < len(text) and depth > 0:
                    if text[j] == '(':
                        depth += 1
                    elif text[j] == ')':
                        depth -= 1
                    j += 1
                result.append(text[i:j])
                result.append(')')
                i = j
            text = ''.join(result)
        return text

    content = fix_ppat_constant_closings(content)

    # Pattern matching: PatternDesc::Ppat_constant(Constant::String(s, Some(delim)))
    r(
        "PatternDesc::Ppat_constant(Constant::String(s, Some(delim))) => {",
        "PatternDesc::Ppat_constant(c) if matches!(c.as_ref(), Constant::String(_, Some(_))) => { let Constant::String(s, Some(delim)) = c.as_ref() else { unreachable!() };",
    )
    r(
        "PatternDesc::Ppat_constant(Constant::Integer(s, Some('l'))) => {",
        "PatternDesc::Ppat_constant(c) if matches!(c.as_ref(), Constant::Integer(_, Some('l'))) => { let Constant::Integer(s, _) = c.as_ref() else { unreachable!() };",
    )
    r(
        "PatternDesc::Ppat_constant(c) => PatternDesc::Ppat_constant(c.clone()),",
        "PatternDesc::Ppat_constant(c) => PatternDesc::Ppat_constant(c.clone()),"
    )

    # ================================================================
    # Ppat_alias: Box + StringLoc -> Box<(Pattern, StringLoc)>
    # ================================================================
    r(
        "PatternDesc::Ppat_alias(inner, name) => {\n            PatternDesc::Ppat_alias(Box::new(rewrite_pattern(inner, arena)), name.clone())",
        "PatternDesc::Ppat_alias(inner) => { let (ref inner_pat, ref name) = **inner;\n            PatternDesc::Ppat_alias(Box::new((rewrite_pattern(inner_pat, arena), name.clone())))"
    )
    # is_simple_pattern
    r(
        "PatternDesc::Ppat_constraint(inner, _) => is_simple_pattern(inner),",
        "PatternDesc::Ppat_constraint(inner) => { let (ref inner_pat, _) = **inner; is_simple_pattern(inner_pat) }",
    )

    # ================================================================
    # Ppat_construct: (Loc, Option<Box<Pat>>) -> Box<(Loc, Option<Box<Pat>>)>
    # ================================================================
    r(
        """PatternDesc::Ppat_construct(lid, opt_p) => {
            PatternDesc::Ppat_construct(
                lid.clone(),
                opt_p.as_ref().map(|p| Box::new(rewrite_pattern(p, arena))),
            )""",
        """PatternDesc::Ppat_construct(inner) => { let (lid, opt_p) = inner.as_ref();
            PatternDesc::Ppat_construct(Box::new((
                lid.clone(),
                opt_p.as_ref().map(|p| Box::new(rewrite_pattern(p, arena))),
            )))"""
    )

    # ================================================================
    # Ppat_variant: (Label, Option<Box<Pat>>) -> Box<(Label, Option<Box<Pat>>)>
    # ================================================================
    r(
        """PatternDesc::Ppat_variant(label, opt_p) => {
            PatternDesc::Ppat_variant(
                label.clone(),
                opt_p.as_ref().map(|p| Box::new(rewrite_pattern(p, arena))),
            )""",
        """PatternDesc::Ppat_variant(inner) => { let (label, opt_p) = inner.as_ref();
            PatternDesc::Ppat_variant(Box::new((
                label.clone(),
                opt_p.as_ref().map(|p| Box::new(rewrite_pattern(p, arena))),
            )))"""
    )

    # ================================================================
    # Ppat_record: (Vec<PRF>, ClosedFlag) -> Box<(Vec<PRF>, ClosedFlag)>
    # ================================================================
    r(
        """PatternDesc::Ppat_record(fields, flag) => {
            PatternDesc::Ppat_record(""",
        """PatternDesc::Ppat_record(inner) => { let (fields, flag) = inner.as_ref();
            PatternDesc::Ppat_record(Box::new(("""
    )
    r(
        """                *flag,
            )
        }

        // Array pattern""",
        """                *flag,
            )))
        }

        // Array pattern"""
    )

    # ================================================================
    # Ppat_or: (Box<Pat>, Box<Pat>) -> Box<(Pat, Pat)>
    # ================================================================
    r(
        """PatternDesc::Ppat_or(p1, p2) => {
            PatternDesc::Ppat_or(
                Box::new(rewrite_pattern(p1, arena)),
                Box::new(rewrite_pattern(p2, arena)),
            )""",
        """PatternDesc::Ppat_or(inner) => { let (p1, p2) = inner.as_ref();
            PatternDesc::Ppat_or(Box::new((
                rewrite_pattern(p1, arena),
                rewrite_pattern(p2, arena),
            )))"""
    )

    # ================================================================
    # Ppat_constraint: (Box<Pat>, CoreType) -> Box<(Pat, CoreType)>
    # ================================================================
    r(
        """PatternDesc::Ppat_constraint(inner_pat, core_type) => {
            PatternDesc::Ppat_constraint(
                Box::new(rewrite_pattern(inner_pat, arena)),
                rewrite_core_type(core_type, arena),
            )""",
        """PatternDesc::Ppat_constraint(inner) => { let (inner_pat, core_type) = inner.as_ref();
            PatternDesc::Ppat_constraint(Box::new((
                rewrite_pattern(inner_pat, arena),
                rewrite_core_type(core_type, arena),
            )))"""
    )

    # ================================================================
    # Ppat_open: (Loc, Box<Pat>) -> Box<(Loc, Pat)>
    # ================================================================
    r(
        "PatternDesc::Ppat_open(lid, inner) => {\n            PatternDesc::Ppat_open(lid.clone(), Box::new(rewrite_pattern(inner, arena)))",
        "PatternDesc::Ppat_open(inner) => { let (lid, ref inner_pat) = **inner;\n            PatternDesc::Ppat_open(Box::new((lid.clone(), rewrite_pattern(inner_pat, arena))))"
    )

    # ================================================================
    # Ppat_extension: Extension -> Box<Extension>
    # ================================================================
    r(
        "PatternDesc::Ppat_extension((name, payload)) => {\n            PatternDesc::Ppat_extension((name.clone(), rewrite_payload(payload, arena)))",
        "PatternDesc::Ppat_extension(ext) => { let (name, payload) = ext.as_ref();\n            PatternDesc::Ppat_extension(Box::new((name.clone(), rewrite_payload(payload, arena))))"
    )

    # ================================================================
    # Ppat_interval: (Constant, Constant) -> Box<(Constant, Constant)>
    # ================================================================
    r(
        "PatternDesc::Ppat_interval(c1, c2) => PatternDesc::Ppat_interval(c1.clone(), c2.clone()),",
        "PatternDesc::Ppat_interval(inner) => { let (c1, c2) = inner.as_ref(); PatternDesc::Ppat_interval(Box::new((c1.clone(), c2.clone()))) },"
    )

    # ================================================================
    # Payload::PTyp: Box<CoreType> -> CoreType (unboxed)
    # ================================================================
    # No change needed for PTyp - it was Box<CoreType>, now CoreType

    # Payload::PPat: (Box<Pat>, Option<Box<Expr>>) -> Box<(Pat, Option<Box<Expr>>)>
    r(
        """Payload::PPat(pat, guard) => {
            Payload::PPat(
                Box::new(rewrite_pattern(pat, arena)),
                guard.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
            )""",
        """Payload::PPat(inner) => { let (pat, guard) = inner.as_ref();
            Payload::PPat(Box::new((
                rewrite_pattern(pat, arena),
                guard.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
            )))"""
    )

    with open(path, 'w') as f:
        f.write(content)

    if content != original:
        print("File updated successfully")
    else:
        print("No changes were made")

if __name__ == '__main__':
    main()
