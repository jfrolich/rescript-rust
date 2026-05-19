#!/usr/bin/env python3
"""Categorize bsc-ast parity failures by their primary failure pattern.

For each failing file, generates both OCaml and Rust binary ASTs, compares
them using the inspect_binary_ast.py infrastructure, and categorizes the
FIRST difference by type.
"""

import sys
import os
import subprocess
import tempfile
import collections
import json
import time

# Add project root to path so we can import the inspection module
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, SCRIPT_DIR)

from inspect_binary_ast import (
    BinaryAstFile, compare_trees, MarshalDecoder,
    SharedNode, BlockNode, StringNode, IntNode, DoubleNode
)

def rescript_platform():
    platform_script = os.path.join(SCRIPT_DIR, "platform.sh")
    result = subprocess.run(
        [platform_script],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


# Binary paths
OCAML_BSC = os.environ.get(
    "OCAML_BSC",
    os.path.join(PROJECT_ROOT, "packages/@rescript", rescript_platform(), "bin/bsc.exe"),
)
RUST_TARGET = os.environ.get("RUST_TARGET", "debug")
RUST_BSC = os.environ.get(
    "RUST_BSC",
    os.path.join(PROJECT_ROOT, "compiler-rust", "target", RUST_TARGET, "bsc"),
)

# Baseline file
BASELINE_FILE = os.path.join(PROJECT_ROOT, "tests/parity_baselines/bsc_ast.txt")

# Test files root
TESTS_DIR = os.path.join(PROJECT_ROOT, "tests")


def get_failing_files():
    """Get list of files that fail bsc-ast parity."""
    # Get all test files
    result = subprocess.run(
        ["find",
         "syntax_tests/data/idempotency",
         "syntax_tests/data/printer",
         "syntax_tests/data/ppx",
         "syntax_tests/data/conversion",
         "syntax_tests/data/ast-mapping",
         "syntax_tests/data/parsing",
         "(", "-name", "*.res", "-o", "-name", "*.resi", ")",
         "-not", "-path", "*/errors/*",
         "-not", "-path", "*/recovery/*",
         "-not", "-path", "*/infiniteLoops/*",
         "-not", "-path", "*/ffi/export.res",
         "-not", "-path", "*/parsing/other/gentype.res"],
        capture_output=True, text=True, cwd=TESTS_DIR
    )
    all_files = set(result.stdout.strip().split("\n"))

    # Get baseline (passing) files
    with open(BASELINE_FILE) as f:
        baseline_files = set(line.strip() for line in f if line.strip())

    # Failing = all - baseline
    failing = sorted(all_files - baseline_files)
    return failing


def generate_ast(bsc_path, source_file, output_file):
    """Run a bsc compiler to generate a binary AST file."""
    cmd = [bsc_path, "-bs-ast", source_file, "-o", output_file]
    result = subprocess.run(cmd, capture_output=True, timeout=10)
    if result.returncode != 0:
        return False

    # Handle .resi files that produce .iast regardless of -o
    if not os.path.exists(output_file):
        # Try .iast extension
        base, ext = os.path.splitext(output_file)
        iast_file = base + ".iast"
        if os.path.exists(iast_file):
            os.rename(iast_file, output_file)
            return True
        return False
    return True


def resolve_shared_target(node, decoder_objects):
    """Resolve a SharedNode to its actual target object."""
    if isinstance(node, SharedNode):
        return decoder_objects.get(node.target_idx)
    return node


def describe_node(node, decoder_objects=None):
    """Get a short description of a node for categorization."""
    if isinstance(node, SharedNode):
        target = None
        if decoder_objects:
            target = decoder_objects.get(node.target_idx)
        if target:
            return f"SHARED -> {describe_node(target)}"
        return f"SHARED -> [{node.target_idx}]"
    if isinstance(node, BlockNode):
        hint = f" ({node.type_hint})" if node.type_hint else ""
        return f"BLOCK tag={node.tag} size={len(node.children)}{hint}"
    if isinstance(node, StringNode):
        return f"STRING {node.value!r}"
    if isinstance(node, IntNode):
        return f"INT {node.value}"
    if isinstance(node, DoubleNode):
        return f"DOUBLE {node.value}"
    return repr(node)


def is_empty_pstr(node, decoder_objects):
    """Check if a node is PStr([]) - a block with tag=0, size=0 (empty list/unit)."""
    resolved = resolve_shared_target(node, decoder_objects) if isinstance(node, SharedNode) else node
    if isinstance(resolved, BlockNode):
        return resolved.tag == 0 and len(resolved.children) == 0
    return False


def is_location_block(node, decoder_objects):
    """Check if a node is a Location block."""
    resolved = resolve_shared_target(node, decoder_objects) if isinstance(node, SharedNode) else node
    if isinstance(resolved, BlockNode):
        return resolved.type_hint in ("Location", "Location?")
    return False


def is_position_block(node, decoder_objects):
    """Check if a node is a Position block."""
    resolved = resolve_shared_target(node, decoder_objects) if isinstance(node, SharedNode) else node
    if isinstance(resolved, BlockNode):
        return resolved.type_hint == "Position"
    return False


def describe_block_short(node, decoder_objects, depth=0):
    """Describe a block node in a short readable form, recursing shallowly."""
    if depth > 3:
        return "..."
    if isinstance(node, SharedNode):
        target = decoder_objects.get(node.target_idx)
        if target:
            return f"SHARED->{describe_block_short(target, decoder_objects, depth+1)}"
        return f"SHARED->[{node.target_idx}]"
    if isinstance(node, StringNode):
        return f"STR({node.value!r})"
    if isinstance(node, IntNode):
        return f"INT({node.value})"
    if isinstance(node, BlockNode):
        hint = f"({node.type_hint})" if node.type_hint else ""
        kids = ""
        if depth < 2 and len(node.children) <= 3:
            parts = [describe_block_short(c, decoder_objects, depth+1) for c in node.children]
            kids = " [" + ", ".join(parts) + "]"
        return f"BLOCK(t={node.tag},s={len(node.children)}){hint}{kids}"
    return repr(node)


def classify_shared_target(target_obj, decoder_objects):
    """Classify a shared target into a meaningful category string.

    Returns a tuple of (category, detail_string) where category is the
    broad bucket and detail provides specifics.
    """
    if isinstance(target_obj, StringNode):
        if target_obj.value == "":
            return "String_sharing", "empty string ''"
        return "String_sharing", "string %r" % target_obj.value

    if isinstance(target_obj, BlockNode):
        tag = target_obj.tag
        size = len(target_obj.children)

        # Empty block (tag=0, size=0) = PStr([]) / [] / None
        if tag == 0 and size == 0:
            return "PStr_empty", "tag=0 size=0 (empty list/PStr([]))"

        # Location
        if target_obj.type_hint in ("Location", "Location?"):
            return "Location_sharing", "Location block"
        if target_obj.type_hint == "Position":
            return "Location_sharing", "Position block"

        # tag=0 size=1: Some/Wrapper - check what it wraps
        if tag == 0 and size == 1:
            child = target_obj.children[0]
            rc = child
            if isinstance(child, SharedNode):
                rc = decoder_objects.get(child.target_idx, child)
            if isinstance(rc, IntNode):
                # Some(INT N) - this is a wrapped enum variant like Some(Nolabel)
                # INT 0 = Nolabel, first constant constructor
                # INT 1 = second constant constructor (e.g. Public)
                return "Some_int_sharing", "Some(INT %d)" % rc.value
            if isinstance(rc, StringNode):
                # Some(string) or Lident(string) - wrapping a string
                return "Lident_sharing", "Lident/Some(%r)" % rc.value
            if isinstance(rc, BlockNode):
                inner_hint = rc.type_hint or "t%ds%d" % (rc.tag, len(rc.children))
                return "Some_block_sharing", "Some(%s)" % inner_hint
            return "Some_other_sharing", "Some(%s)" % type(rc).__name__

        # tag=0 size=2: Pair/Record2 - check children to identify
        if tag == 0 and size == 2:
            child0 = target_obj.children[0]
            child1 = target_obj.children[1]
            rc0 = child0
            rc1 = child1
            if isinstance(child0, SharedNode):
                rc0 = decoder_objects.get(child0.target_idx, child0)
            if isinstance(child1, SharedNode):
                rc1 = decoder_objects.get(child1.target_idx, child1)

            # (string, Location) = Asttypes.loc - identifier with location
            if isinstance(rc0, StringNode) and isinstance(rc1, BlockNode) and rc1.type_hint in ("Location", "Location?"):
                return "Loc_record_sharing", "{txt=%r; loc=...}" % rc0.value
            # (Record2, INT) - could be {txt: lid; loc} with loc as int
            if isinstance(rc0, BlockNode) and isinstance(rc1, IntNode):
                return "Pair_sharing", "(Block(t%ds%d), INT %d)" % (rc0.tag, len(rc0.children), rc1.value)
            if isinstance(rc0, BlockNode) and isinstance(rc1, BlockNode):
                h0 = rc0.type_hint or "t%ds%d" % (rc0.tag, len(rc0.children))
                h1 = rc1.type_hint or "t%ds%d" % (rc1.tag, len(rc1.children))
                return "Pair_sharing", "(%s, %s)" % (h0, h1)
            return "Pair_sharing", "generic pair"

        # Longident Ldot = tag=1 size=2, also cons list cells
        if tag == 1 and size == 2:
            child0 = target_obj.children[0]
            rc0 = child0
            if isinstance(child0, SharedNode):
                rc0 = decoder_objects.get(child0.target_idx, child0)
            if isinstance(rc0, BlockNode) and rc0.tag == 0 and len(rc0.children) == 1:
                # Ldot(Lident(s), field) - Longident
                return "Longident_sharing", "Ldot longident"
            if isinstance(rc0, StringNode):
                # Could be Ldot or cons cell
                return "Longident_sharing", "Ldot or cons"
            return "Cons_list_sharing", "cons cell (tag=1 size=2)"

        # tag=0 size=3 - could be Location or any triple
        if tag == 0 and size == 3:
            return "Triple_sharing", "tag=0 size=3 (3-field record)"

        return "Block_sharing", "Block(tag=%d, size=%d)" % (tag, size)

    return "Unknown_sharing", type(target_obj).__name__


def categorize_first_diff(diff, ocaml_decoder, rust_decoder):
    """Categorize the first difference found in tree comparison."""
    kind = diff["kind"]
    a_str = diff["a"]
    b_str = diff["b"]
    path = diff["path"]

    if kind == "type_mismatch":
        # One side is SHARED, the other is an actual node
        a_is_shared = a_str.startswith("SHARED")
        b_is_shared = b_str.startswith("SHARED")

        if a_is_shared and not b_is_shared:
            # OCaml shares something that Rust doesn't (Rust under-shares)
            target_idx = None
            try:
                idx_start = a_str.index("[") + 1
                idx_end = a_str.index("]")
                target_idx = int(a_str[idx_start:idx_end])
            except (ValueError, IndexError):
                pass

            if target_idx is not None:
                target_obj = ocaml_decoder.objects.get(target_idx)
                if target_obj is not None:
                    cat, detail = classify_shared_target(target_obj, ocaml_decoder.objects)
                    return "undersharing:%s" % cat, detail

            return "undersharing:unknown", None

        elif b_is_shared and not a_is_shared:
            # Rust shares something that OCaml doesn't (Rust over-shares)
            target_idx = None
            try:
                idx_start = b_str.index("[") + 1
                idx_end = b_str.index("]")
                target_idx = int(b_str[idx_start:idx_end])
            except (ValueError, IndexError):
                pass

            if target_idx is not None:
                target_obj = rust_decoder.objects.get(target_idx)
                if target_obj is not None:
                    cat, detail = classify_shared_target(target_obj, rust_decoder.objects)
                    return "oversharing:%s" % cat, detail

            return "oversharing:unknown", None

        else:
            # Both shared or both not shared but types differ
            return "Structural", None

    elif kind == "shared_target":
        # Both sides share but to different targets - this cascades from earlier differences
        return "Cascaded_shared_offset", None

    elif kind == "obj_idx":
        # Object index shifted - cascading from earlier sharing difference
        return "Cascaded_obj_idx", None

    elif kind == "string_value":
        return "Structural_string", None

    elif kind == "int_value":
        return "Structural_int", None

    elif kind == "block_tag":
        return "Structural_block_tag", None

    elif kind == "block_size":
        return "Structural_block_size", None

    elif kind == "double_value":
        return "Structural_double", None

    return "Unknown", None


def analyze_file(file_path):
    """Analyze a single failing file and return its category."""
    source = os.path.join(TESTS_DIR, file_path)
    if not os.path.exists(source):
        return "Error_source_not_found", None

    with tempfile.TemporaryDirectory() as tmpdir:
        ocaml_out = os.path.join(tmpdir, "ocaml.ast")
        rust_out = os.path.join(tmpdir, "rust.ast")

        # Generate both ASTs
        try:
            if not generate_ast(OCAML_BSC, source, ocaml_out):
                return "Error_ocaml_bsc", None
        except subprocess.TimeoutExpired:
            return "Error_ocaml_timeout", None
        except Exception as e:
            return "Error_ocaml_exception", str(e)

        try:
            if not generate_ast(RUST_BSC, source, rust_out):
                return "Error_rust_bsc", None
        except subprocess.TimeoutExpired:
            return "Error_rust_timeout", None
        except Exception as e:
            return "Error_rust_exception", str(e)

        # Check if identical (shouldn't be since these are "failing" files)
        with open(ocaml_out, "rb") as f:
            ocaml_data = f.read()
        with open(rust_out, "rb") as f:
            rust_data = f.read()

        if ocaml_data == rust_data:
            return "Actually_passing", None

        # Parse and compare
        try:
            ocaml_ast = BinaryAstFile(ocaml_out)
            rust_ast = BinaryAstFile(rust_out)

            ocaml_root, ocaml_dec = ocaml_ast.decode_ast()
            rust_root, rust_dec = rust_ast.decode_ast()

            diffs = compare_trees(ocaml_root, rust_root)

            if not diffs:
                return "Encoding_only", None  # Trees match but binary differs

            # Categorize the FIRST difference
            first_diff = diffs[0]
            category, sub_detail = categorize_first_diff(first_diff, ocaml_dec, rust_dec)

            detail = "%s: A=%s  B=%s" % (first_diff['kind'], first_diff['a'][:80], first_diff['b'][:80])
            if sub_detail:
                detail = "%s [%s]" % (sub_detail, detail)
            return category, detail

        except Exception as e:
            return "Error_analysis", str(e)


def main():
    print("=" * 80)
    print("BSC-AST Failure Categorization")
    print("=" * 80)
    print()

    # Get failing files
    print("Finding failing files...")
    failing_files = get_failing_files()
    total_failing = len(failing_files)
    print(f"Found {total_failing} failing files")
    print()

    # Check binaries exist
    for name, path in [("OCaml BSC", OCAML_BSC), ("Rust BSC", RUST_BSC)]:
        if not os.path.exists(path):
            print(f"Error: {name} not found at {path}")
            sys.exit(1)

    # Analyze all failing files (or sample)
    sample_size = total_failing  # Analyze all
    files_to_analyze = failing_files[:sample_size]

    print(f"Analyzing {len(files_to_analyze)} files...")
    print()

    categories = collections.Counter()
    category_examples = collections.defaultdict(list)
    results = []

    start_time = time.time()

    for i, file_path in enumerate(files_to_analyze):
        if (i + 1) % 25 == 0 or i == 0:
            elapsed = time.time() - start_time
            rate = (i + 1) / elapsed if elapsed > 0 else 0
            remaining = (len(files_to_analyze) - i - 1) / rate if rate > 0 else 0
            print(f"  [{i+1}/{len(files_to_analyze)}] ({rate:.1f} files/sec, ~{remaining:.0f}s remaining) {file_path}")

        category, detail = analyze_file(file_path)
        categories[category] += 1
        results.append((file_path, category, detail))

        # Keep first 3 examples per category
        if len(category_examples[category]) < 3:
            category_examples[category].append((file_path, detail))

    elapsed = time.time() - start_time
    print()
    print(f"Analysis complete in {elapsed:.1f}s")
    print()

    # Print summary
    print("=" * 80)
    print("SUMMARY: Failure categories (by first difference)")
    print("=" * 80)
    print()

    # Group by direction
    undersharing = []   # OCaml shares, Rust doesn't
    oversharing = []    # Rust shares, OCaml doesn't
    structural = []
    error_cats = []

    for cat, count in categories.most_common():
        if cat.startswith("Error_") or cat == "Actually_passing" or cat == "Encoding_only":
            error_cats.append((cat, count))
        elif cat.startswith("undersharing:"):
            undersharing.append((cat, count))
        elif cat.startswith("oversharing:"):
            oversharing.append((cat, count))
        else:
            structural.append((cat, count))

    total_under = sum(c for _, c in undersharing)
    total_over = sum(c for _, c in oversharing)
    total_structural = sum(c for _, c in structural)
    total_error = sum(c for _, c in error_cats)
    n = len(files_to_analyze)

    if undersharing:
        print(f"UNDERSHARING: Rust doesn't share what OCaml shares ({total_under} files, {100*total_under/n:.1f}%)")
        print("-" * 75)
        for cat, count in sorted(undersharing, key=lambda x: -x[1]):
            pct = 100.0 * count / n
            subcat = cat.split(":", 1)[1]
            bar = "#" * max(1, int(pct / 2))
            print(f"  {subcat:45s} {count:5d}  ({pct:5.1f}%)  {bar}")
        print()

    if oversharing:
        print(f"OVERSHARING: Rust shares what OCaml doesn't ({total_over} files, {100*total_over/n:.1f}%)")
        print("-" * 75)
        for cat, count in sorted(oversharing, key=lambda x: -x[1]):
            pct = 100.0 * count / n
            subcat = cat.split(":", 1)[1]
            bar = "#" * max(1, int(pct / 2))
            print(f"  {subcat:45s} {count:5d}  ({pct:5.1f}%)  {bar}")
        print()

    if structural:
        print(f"STRUCTURAL: Non-sharing differences ({total_structural} files, {100*total_structural/n:.1f}%)")
        print("-" * 75)
        for cat, count in sorted(structural, key=lambda x: -x[1]):
            pct = 100.0 * count / n
            bar = "#" * max(1, int(pct / 2))
            print(f"  {cat:45s} {count:5d}  ({pct:5.1f}%)  {bar}")
        print()

    if error_cats:
        print(f"ERRORS: ({total_error} files)")
        print("-" * 75)
        for cat, count in sorted(error_cats, key=lambda x: -x[1]):
            pct = 100.0 * count / n
            bar = "#" * max(1, int(pct / 2))
            print(f"  {cat:45s} {count:5d}  ({pct:5.1f}%)  {bar}")
        print()

    # Grand total
    print("=" * 75)
    print(f"  {'TOTAL UNDERSHARING':45s} {total_under:5d}  ({100.0*total_under/n:5.1f}%)")
    print(f"  {'TOTAL OVERSHARING':45s} {total_over:5d}  ({100.0*total_over/n:5.1f}%)")
    print(f"  {'TOTAL STRUCTURAL':45s} {total_structural:5d}  ({100.0*total_structural/n:5.1f}%)")
    print(f"  {'TOTAL ERRORS':45s} {total_error:5d}  ({100.0*total_error/n:5.1f}%)")
    print(f"  {'GRAND TOTAL':45s} {n:5d}")
    print("=" * 75)
    print()

    # Consolidated summary for actionable bucket grouping
    print()
    print("=" * 80)
    print("ACTIONABLE BUCKETS (grouped by fix strategy)")
    print("=" * 80)
    print()

    bucket_counts = collections.Counter()
    for cat, count in undersharing + oversharing:
        parts = cat.split(":", 1)
        direction = parts[0]
        subcat = parts[1] if len(parts) > 1 else ""
        bucket_counts["%s: %s" % (direction, subcat)] += count

    for cat, count in structural:
        bucket_counts["structural: %s" % cat] += count

    for bucket, count in sorted(bucket_counts.items(), key=lambda x: -x[1]):
        pct = 100.0 * count / n
        bar = "#" * max(1, int(pct / 2))
        print("  %-55s %5d  (%5.1f%%)  %s" % (bucket, count, pct, bar))

    print()

    # Show examples for each category
    print()
    print("=" * 80)
    print("EXAMPLES (first 3 per category)")
    print("=" * 80)
    for cat in sorted(category_examples.keys()):
        print()
        print(f"--- {cat} ({categories[cat]} files) ---")
        for file_path, detail in category_examples[cat]:
            print(f"  {file_path}")
            if detail:
                print(f"    {detail}")

    # Dump all results to a JSON for further analysis
    output_file = os.path.join(PROJECT_ROOT, "scripts/failure_categories.json")
    with open(output_file, "w") as f:
        json.dump([
            {"file": r[0], "category": r[1], "detail": r[2]}
            for r in results
        ], f, indent=2)
    print()
    print(f"Full results written to: {output_file}")


if __name__ == "__main__":
    main()
