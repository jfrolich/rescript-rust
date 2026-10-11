#!/usr/bin/env python3
"""Binary AST inspection tool for ReScript compiler debugging.

Decodes and compares binary AST files (.ast, .iast) produced by the
OCaml and Rust compilers. Useful for debugging parity issues.

Usage:
    python3 scripts/inspect_binary_ast.py decode <file.ast>
    python3 scripts/inspect_binary_ast.py compare <ocaml.ast> <rust.ast>
    python3 scripts/inspect_binary_ast.py summary <file.ast>
    python3 scripts/inspect_binary_ast.py sharing <file.ast>
    python3 scripts/inspect_binary_ast.py test <source.res>
"""

import struct
import sys
import os
import subprocess
import collections
import platform as platform_mod

# Large AST files produce deeply nested cons lists that exceed Python's
# default recursion limit of 1000.  Bump it as a safety net; the critical
# functions below are also converted to iterative algorithms.
sys.setrecursionlimit(50_000)

# ── Marshal format opcodes ──────────────────────────────────────────────

CODE_INT8 = 0x00
CODE_INT16 = 0x01
CODE_INT32 = 0x02
CODE_INT64 = 0x03
CODE_SHARED8 = 0x04
CODE_SHARED16 = 0x05
CODE_SHARED32 = 0x06
CODE_BLOCK32 = 0x08
CODE_STRING8 = 0x09
CODE_STRING32 = 0x0A
CODE_DOUBLE_BIG = 0x0B
CODE_DOUBLE_LITTLE = 0x0C
CODE_BLOCK64 = 0x13

MARSHAL_MAGIC = b"\x84\x95\xa6\xbe"

# ── AST type heuristics ────────────────────────────────────────────────
# Block tag+size patterns used to annotate AST nodes

def infer_block_type(tag, size, depth, parent_type):
    """Heuristic: infer an AST type annotation from block tag and size."""
    if tag == 0 and size == 4:
        # Position: { fname; lnum; bol; cnum }
        return "Position"
    if tag == 0 and size == 3:
        # Could be Location: { loc_start; loc_end; loc_ghost }
        # or many other things - we annotate tentatively
        return "Location?"
    if tag == 0 and size == 2:
        return "Pair/Record2"
    if tag == 0 and size == 1:
        return "Some/Wrapper"
    if tag == 0 and size == 0:
        return "Unit/None/[]"
    if tag == 1 and size == 2:
        return "Cons/Variant1"
    return None


# ── Binary reader helpers ───────────────────────────────────────────────

class BinaryReader:
    """Read binary data from a bytes buffer with position tracking."""

    def __init__(self, data):
        self.data = data
        self.pos = 0

    def remaining(self):
        return len(self.data) - self.pos

    def read_bytes(self, n):
        if self.pos + n > len(self.data):
            raise ValueError(f"Unexpected EOF at offset {self.pos}, wanted {n} bytes")
        result = self.data[self.pos:self.pos + n]
        self.pos += n
        return result

    def read_u8(self):
        return self.read_bytes(1)[0]

    def read_u16(self):
        return struct.unpack(">H", self.read_bytes(2))[0]

    def read_u32(self):
        return struct.unpack(">I", self.read_bytes(4))[0]

    def read_i32(self):
        return struct.unpack(">i", self.read_bytes(4))[0]

    def read_i64(self):
        return struct.unpack(">q", self.read_bytes(8))[0]

    def read_f64_big(self):
        return struct.unpack(">d", self.read_bytes(8))[0]

    def read_f64_little(self):
        return struct.unpack("<d", self.read_bytes(8))[0]

    def read_string(self, length):
        return self.read_bytes(length)


# ── Marshal node representation ─────────────────────────────────────────

class MarshalNode:
    """Represents a decoded marshal value."""
    pass

class IntNode(MarshalNode):
    def __init__(self, value, encoding="small"):
        self.value = value
        self.encoding = encoding  # "small", "INT8", "INT16", "INT32", "INT64"

    def __repr__(self):
        if self.encoding == "small":
            return f"INT {self.value}"
        return f"{self.encoding} {self.value}"

class StringNode(MarshalNode):
    def __init__(self, value, obj_idx, encoding="small"):
        self.value = value
        self.obj_idx = obj_idx
        self.encoding = encoding

    def __repr__(self):
        return f"[{self.obj_idx}] STRING {self.value!r}"

class BlockNode(MarshalNode):
    def __init__(self, tag, children, obj_idx, encoding="small", type_hint=None):
        self.tag = tag
        self.children = children
        self.obj_idx = obj_idx
        self.encoding = encoding
        self.type_hint = type_hint

    def __repr__(self):
        hint = f" ({self.type_hint})" if self.type_hint else ""
        return f"[{self.obj_idx}] BLOCK tag={self.tag} size={len(self.children)}{hint}"

class SharedNode(MarshalNode):
    def __init__(self, target_idx, offset, encoding="SHARED8"):
        self.target_idx = target_idx
        self.offset = offset
        self.encoding = encoding

    def __repr__(self):
        return f"SHARED -> [{self.target_idx}] (offset={self.offset})"

class DoubleNode(MarshalNode):
    def __init__(self, value, obj_idx, encoding="big"):
        self.value = value
        self.obj_idx = obj_idx
        self.encoding = encoding

    def __repr__(self):
        return f"[{self.obj_idx}] DOUBLE {self.value}"


# ── Marshal decoder ─────────────────────────────────────────────────────

class _PendingBlock:
    """Temporary object used during iterative decoding to represent
    a block whose children have not all been decoded yet."""
    __slots__ = ("tag", "size", "depth", "encoding", "idx", "type_hint", "children")

    def __init__(self, tag, size, depth, encoding, idx, type_hint):
        self.tag = tag
        self.size = size
        self.depth = depth
        self.encoding = encoding
        self.idx = idx
        self.type_hint = type_hint
        self.children = []


class MarshalDecoder:
    """Decode an OCaml marshal payload into a tree of MarshalNodes.

    Uses an iterative algorithm with an explicit stack so that deeply
    nested structures (e.g. long cons-lists) do not blow Python's call
    stack.
    """

    def __init__(self, data):
        self.reader = BinaryReader(data)
        self.obj_counter = 0
        self.objects = {}  # obj_idx -> node

    def decode(self):
        """Decode the marshal payload (after the 20-byte header)."""
        value = self._read_atom(depth=0)

        # Fast path: root is a leaf node
        if not isinstance(value, _PendingBlock):
            return value

        # Iterative decoding using an explicit stack.  Each entry is a
        # _PendingBlock that still needs children decoded.
        stack = [value]

        while stack:
            top = stack[-1]
            if len(top.children) < top.size:
                child = self._read_atom(depth=top.depth + 1)
                if isinstance(child, _PendingBlock):
                    # Descend into the child block before continuing
                    stack.append(child)
                else:
                    top.children.append(child)
            else:
                # All children collected – finalize this block
                stack.pop()
                node = self._finalize_block(top)
                if stack:
                    stack[-1].children.append(node)
                else:
                    return node

        # Should not be reached
        raise ValueError("Unexpected end of decode loop")

    # ------------------------------------------------------------------
    # _read_atom: read the next opcode and return either a leaf
    # MarshalNode or a _PendingBlock (for blocks whose children still
    # need to be decoded).
    # ------------------------------------------------------------------

    def _read_atom(self, depth):
        byte = self.reader.read_u8()

        # Small positive integer: 0x40-0x7F -> 0..63
        if 0x40 <= byte <= 0x7F:
            return IntNode(byte - 0x40, "small")

        # Small block: 0x80-0xFF
        if 0x80 <= byte <= 0xFF:
            code = byte - 0x80
            tag = code & 0x0F
            size = (code >> 4) & 0x07
            return self._start_block(tag, size, depth, "small")

        # Small string: 0x20-0x3F
        if 0x20 <= byte <= 0x3F:
            length = byte - 0x20
            return self._decode_string(length, "small")

        # Extended opcodes
        if byte == CODE_INT8:
            val = self.reader.read_u8()
            if val >= 128:
                val -= 256
            return IntNode(val, "INT8")

        if byte == CODE_INT16:
            val = self.reader.read_u16()
            if val >= 32768:
                val -= 65536
            return IntNode(val, "INT16")

        if byte == CODE_INT32:
            val = self.reader.read_i32()
            return IntNode(val, "INT32")

        if byte == CODE_INT64:
            val = self.reader.read_i64()
            return IntNode(val, "INT64")

        if byte == CODE_SHARED8:
            offset = self.reader.read_u8()
            target = self.obj_counter - offset
            return SharedNode(target, offset, "SHARED8")

        if byte == CODE_SHARED16:
            offset = self.reader.read_u16()
            target = self.obj_counter - offset
            return SharedNode(target, offset, "SHARED16")

        if byte == CODE_SHARED32:
            offset = self.reader.read_u32()
            target = self.obj_counter - offset
            return SharedNode(target, offset, "SHARED32")

        if byte == CODE_BLOCK32:
            header = self.reader.read_u32()
            tag = header & 0xFF
            size = header >> 10
            return self._start_block(tag, size, depth, "BLOCK32")

        if byte == CODE_BLOCK64:
            header = self.reader.read_i64()
            tag = header & 0xFF
            size = header >> 10
            return self._start_block(tag, size, depth, "BLOCK64")

        if byte == CODE_STRING8:
            length = self.reader.read_u8()
            return self._decode_string(length, "STRING8")

        if byte == CODE_STRING32:
            length = self.reader.read_u32()
            return self._decode_string(length, "STRING32")

        if byte == CODE_DOUBLE_BIG:
            idx = self.obj_counter
            self.obj_counter += 1
            val = self.reader.read_f64_big()
            node = DoubleNode(val, idx, "big")
            self.objects[idx] = node
            return node

        if byte == CODE_DOUBLE_LITTLE:
            idx = self.obj_counter
            self.obj_counter += 1
            val = self.reader.read_f64_little()
            node = DoubleNode(val, idx, "little")
            self.objects[idx] = node
            return node

        raise ValueError(f"Unknown marshal opcode 0x{byte:02X} at offset {self.reader.pos - 1}")

    def _start_block(self, tag, size, depth, encoding):
        """Begin decoding a block.  Returns a _PendingBlock if size > 0,
        otherwise returns the finalised BlockNode immediately."""
        idx = self.obj_counter
        self.obj_counter += 1
        type_hint = infer_block_type(tag, size, depth, None)

        if size == 0:
            node = BlockNode(tag, [], idx, encoding, type_hint)
            self.objects[idx] = node
            return node

        return _PendingBlock(tag, size, depth, encoding, idx, type_hint)

    def _finalize_block(self, pending):
        """Convert a fully-populated _PendingBlock into a BlockNode."""
        type_hint = pending.type_hint
        children = pending.children

        # Refine Location? hint: check if first two children are Position blocks
        if type_hint == "Location?" and len(children) >= 2:
            c0, c1 = children[0], children[1]
            def is_pos_or_shared_pos(c):
                return (
                    (isinstance(c, BlockNode) and c.type_hint == "Position") or
                    (isinstance(c, SharedNode) and c.target_idx in self.objects and
                     isinstance(self.objects[c.target_idx], BlockNode) and
                     self.objects[c.target_idx].type_hint == "Position")
                )
            if is_pos_or_shared_pos(c0) and is_pos_or_shared_pos(c1):
                type_hint = "Location"
            else:
                type_hint = None  # Not a location after all

        node = BlockNode(pending.tag, children, pending.idx, pending.encoding, type_hint)
        self.objects[pending.idx] = node
        return node

    def _decode_string(self, length, encoding):
        idx = self.obj_counter
        self.obj_counter += 1
        data = self.reader.read_string(length)
        try:
            value = data.decode("utf-8")
        except UnicodeDecodeError:
            value = data.hex()
        node = StringNode(value, idx, encoding)
        self.objects[idx] = node
        return node


# ── Binary AST file parser ──────────────────────────────────────────────

class BinaryAstFile:
    """Parse a binary AST file (.ast / .iast) into its sections."""

    def __init__(self, filepath):
        self.filepath = filepath
        with open(filepath, "rb") as f:
            self.raw = f.read()
        self.reader = BinaryReader(self.raw)
        self.deps = []
        self.source_path = ""
        self.marshal_header = {}
        self.marshal_payload = b""
        self._parse()

    def _parse(self):
        r = self.reader

        # Section 1: dependency section size (4 bytes big-endian)
        self.dep_section_size = r.read_u32()

        # Section 2: dependencies + source path
        dep_end = r.pos + self.dep_section_size
        # First byte should be '\n'
        sep = r.read_u8()
        if sep != 0x0A:
            raise ValueError(f"Expected \\n separator at offset {r.pos - 1}, got 0x{sep:02X}")

        # Read dependency names (newline-separated until dep_end)
        dep_data = r.read_bytes(self.dep_section_size - 1)
        dep_lines = dep_data.decode("utf-8").split("\n")
        # Filter empty strings
        self.deps = [d for d in dep_lines if d]

        # Source path follows deps section, terminated by '\n'
        source_bytes = bytearray()
        while True:
            b = r.read_u8()
            if b == 0x0A:
                break
            source_bytes.append(b)
        self.source_path = source_bytes.decode("utf-8")

        # Section 3: Marshal data
        self.marshal_offset = r.pos
        magic = r.read_bytes(4)
        if magic != MARSHAL_MAGIC:
            raise ValueError(f"Invalid marshal magic: {magic.hex()}")

        data_len = r.read_u32()
        num_objects = r.read_u32()
        size_32 = r.read_u32()
        size_64 = r.read_u32()
        self.marshal_header = {
            "data_len": data_len,
            "num_objects": num_objects,
            "size_32": size_32,
            "size_64": size_64,
        }

        self.marshal_payload = r.read_bytes(data_len)

    def decode_ast(self):
        """Decode the marshal payload into a node tree."""
        decoder = MarshalDecoder(self.marshal_payload)
        root = decoder.decode()
        return root, decoder


# ── Tree printing ────────────────────────────────────────────────────────

_CLOSE_BRACE = object()  # sentinel for deferred closing braces


def print_tree(node, indent=0, max_depth=None, file=sys.stdout):
    """Print a MarshalNode tree in a human-readable format (iterative)."""
    # Stack items are either (node, indent) or (_CLOSE_BRACE, indent)
    stack = [(node, indent)]

    while stack:
        item, ind = stack.pop()
        prefix = "  " * ind

        if item is _CLOSE_BRACE:
            print(f"{prefix}}}", file=file)
            continue

        if max_depth is not None and ind > max_depth:
            print(f"{prefix}...", file=file)
            continue

        if isinstance(item, IntNode):
            print(f"{prefix}    {item}", file=file)
        elif isinstance(item, StringNode):
            print(f"{prefix}{item}", file=file)
        elif isinstance(item, SharedNode):
            print(f"{prefix}    {item}", file=file)
        elif isinstance(item, DoubleNode):
            print(f"{prefix}{item}", file=file)
        elif isinstance(item, BlockNode):
            hint = f" ({item.type_hint})" if item.type_hint else ""
            enc = f" {item.encoding}" if item.encoding not in ("small",) else ""
            print(f"{prefix}[{item.obj_idx}] BLOCK{enc} tag={item.tag} size={len(item.children)}{hint} {{", file=file)
            # Push closing brace first (processed last)
            stack.append((_CLOSE_BRACE, ind))
            # Push children in reverse so first child is on top
            for child in reversed(item.children):
                stack.append((child, ind + 1))
        else:
            print(f"{prefix}??? {item!r}", file=file)


def node_to_lines(node, indent=0):
    """Convert a node tree to a list of (indent, line_str, node) tuples for diffing (iterative)."""
    lines = []
    # Stack items: (node, indent) or (_CLOSE_BRACE, indent)
    stack = [(node, indent)]

    while stack:
        item, ind = stack.pop()

        if item is _CLOSE_BRACE:
            lines.append((ind, "}", None))
            continue

        if isinstance(item, IntNode):
            lines.append((ind, f"INT {item.value}", item))
        elif isinstance(item, StringNode):
            lines.append((ind, f"[{item.obj_idx}] STRING {item.value!r}", item))
        elif isinstance(item, SharedNode):
            lines.append((ind, f"SHARED -> [{item.target_idx}]", item))
        elif isinstance(item, DoubleNode):
            lines.append((ind, f"[{item.obj_idx}] DOUBLE {item.value}", item))
        elif isinstance(item, BlockNode):
            hint = f" ({item.type_hint})" if item.type_hint else ""
            lines.append((ind, f"[{item.obj_idx}] BLOCK tag={item.tag} size={len(item.children)}{hint} {{", item))
            stack.append((_CLOSE_BRACE, ind))
            for child in reversed(item.children):
                stack.append((child, ind + 1))

    return lines


# ── Gather statistics ────────────────────────────────────────────────────

def gather_stats(node, stats=None):
    """Walk the tree and gather statistics (iterative)."""
    if stats is None:
        stats = {
            "blocks": 0,
            "strings": 0,
            "ints": 0,
            "shared_refs": 0,
            "doubles": 0,
            "shared_targets": collections.Counter(),
            "block_types": collections.Counter(),
            "string_values": collections.Counter(),
            "type_hints": collections.Counter(),
        }

    stack = [node]
    while stack:
        node = stack.pop()
        if isinstance(node, IntNode):
            stats["ints"] += 1
        elif isinstance(node, StringNode):
            stats["strings"] += 1
            stats["string_values"][node.value] += 1
        elif isinstance(node, SharedNode):
            stats["shared_refs"] += 1
            stats["shared_targets"][node.target_idx] += 1
        elif isinstance(node, DoubleNode):
            stats["doubles"] += 1
        elif isinstance(node, BlockNode):
            stats["blocks"] += 1
            key = f"tag={node.tag} size={len(node.children)}"
            stats["block_types"][key] += 1
            if node.type_hint:
                stats["type_hints"][node.type_hint] += 1
            for child in reversed(node.children):
                stack.append(child)

    return stats


# ── Compare two trees ────────────────────────────────────────────────────

def compare_trees(node_a, node_b, path="root", context_before=5):
    """Walk two trees in parallel, reporting the first divergence.

    Returns a list of difference descriptions. Stops at first divergence
    with surrounding context.
    """
    diffs = []
    _compare_recursive(node_a, node_b, path, diffs, max_diffs=10)
    return diffs


def compare_value_trees(node_a, node_b, decoder_a, decoder_b, max_diffs=10):
    """Compare decoded values while ignoring Marshal object-sharing layout.

    OCaml's Marshal encoder may emit a shared reference where another encoder
    emits the same value inline. Dereference those nodes before comparing the
    complete AST value, including block tags, shapes, and inferred type hints.
    """
    diffs = []
    stack = [(node_a, node_b, "root")]

    def deref(node, decoder):
        while isinstance(node, SharedNode):
            target = decoder.objects.get(node.target_idx)
            if target is None:
                break
            node = target
        return node

    while stack and len(diffs) < max_diffs:
        a, b, path = stack.pop()
        a = deref(a, decoder_a)
        b = deref(b, decoder_b)

        if type(a) is not type(b):
            diffs.append({"path": path, "kind": "type_mismatch"})
            continue

        if isinstance(a, IntNode):
            if a.value != b.value:
                diffs.append({"path": path, "kind": "int_value"})
        elif isinstance(a, StringNode):
            if a.value != b.value:
                diffs.append({"path": path, "kind": "string_value"})
        elif isinstance(a, DoubleNode):
            if a.value != b.value:
                diffs.append({"path": path, "kind": "double_value"})
        elif isinstance(a, BlockNode):
            if (
                a.tag != b.tag
                or len(a.children) != len(b.children)
                or a.type_hint != b.type_hint
            ):
                diffs.append({"path": path, "kind": "block_mismatch"})
                continue
            for i in range(len(a.children) - 1, -1, -1):
                stack.append((a.children[i], b.children[i], f"{path}/[{i}]"))
        elif repr(a) != repr(b):
            diffs.append({"path": path, "kind": "repr_mismatch"})

    return diffs


def _compare_recursive(a, b, path, diffs, max_diffs):
    """Iterative tree comparison using an explicit stack."""
    stack = [(a, b, path)]

    while stack:
        if len(diffs) >= max_diffs:
            return

        a, b, path = stack.pop()

        type_a = type(a).__name__
        type_b = type(b).__name__

        if type_a != type_b:
            diffs.append({
                "path": path,
                "kind": "type_mismatch",
                "a": repr(a),
                "b": repr(b),
            })
            continue

        if isinstance(a, IntNode):
            if a.value != b.value:
                diffs.append({
                    "path": path,
                    "kind": "int_value",
                    "a": f"INT {a.value}",
                    "b": f"INT {b.value}",
                })
        elif isinstance(a, StringNode):
            if a.value != b.value:
                diffs.append({
                    "path": path,
                    "kind": "string_value",
                    "a": f"STRING {a.value!r}",
                    "b": f"STRING {b.value!r}",
                })
            if a.obj_idx != b.obj_idx:
                diffs.append({
                    "path": path,
                    "kind": "obj_idx",
                    "a": f"obj_idx={a.obj_idx}",
                    "b": f"obj_idx={b.obj_idx}",
                })
        elif isinstance(a, SharedNode):
            if a.target_idx != b.target_idx:
                diffs.append({
                    "path": path,
                    "kind": "shared_target",
                    "a": f"SHARED -> [{a.target_idx}]",
                    "b": f"SHARED -> [{b.target_idx}]",
                })
        elif isinstance(a, DoubleNode):
            if a.value != b.value:
                diffs.append({
                    "path": path,
                    "kind": "double_value",
                    "a": f"DOUBLE {a.value}",
                    "b": f"DOUBLE {b.value}",
                })
        elif isinstance(a, BlockNode):
            if a.tag != b.tag:
                diffs.append({
                    "path": path,
                    "kind": "block_tag",
                    "a": f"tag={a.tag}",
                    "b": f"tag={b.tag}",
                })
                continue  # Children won't be comparable

            if len(a.children) != len(b.children):
                diffs.append({
                    "path": path,
                    "kind": "block_size",
                    "a": f"size={len(a.children)}",
                    "b": f"size={len(b.children)}",
                })
                continue

            hint = f" ({a.type_hint})" if a.type_hint else ""
            # Push children in reverse so index 0 is processed first
            for i in range(len(a.children) - 1, -1, -1):
                child_path = f"{path}/[{a.obj_idx}]BLOCK(tag={a.tag},sz={len(a.children)}){hint}/{i}"
                stack.append((a.children[i], b.children[i], child_path))


# ── Subcommand: decode ──────────────────────────────────────────────────

def cmd_decode(args):
    """Decode a binary AST file and print its structure."""
    if len(args) < 1:
        print("Usage: inspect_binary_ast.py decode <file.ast> [--max-depth N]", file=sys.stderr)
        sys.exit(1)

    filepath = args[0]
    max_depth = None
    if "--max-depth" in args:
        idx = args.index("--max-depth")
        max_depth = int(args[idx + 1])

    ast_file = BinaryAstFile(filepath)

    print(f"File: {filepath}")
    print(f"Size: {len(ast_file.raw)} bytes")
    print(f"Dependencies ({len(ast_file.deps)}): {', '.join(ast_file.deps) if ast_file.deps else '(none)'}")
    print(f"Source path: {ast_file.source_path}")
    print()

    hdr = ast_file.marshal_header
    print(f"Marshal header:")
    print(f"  data_len={hdr['data_len']}  num_objects={hdr['num_objects']}  "
          f"size_32={hdr['size_32']}  size_64={hdr['size_64']}")
    print()

    root, decoder = ast_file.decode_ast()
    print(f"Decoded {decoder.obj_counter} objects")
    print()

    print("AST tree:")
    print_tree(root, max_depth=max_depth)


# ── Subcommand: compare ─────────────────────────────────────────────────

def cmd_compare(args):
    """Compare two binary AST files."""
    if len(args) < 2:
        print("Usage: inspect_binary_ast.py compare <ocaml.ast> <rust.ast>", file=sys.stderr)
        sys.exit(1)

    file_a, file_b = args[0], args[1]

    ast_a = BinaryAstFile(file_a)
    ast_b = BinaryAstFile(file_b)

    # Header comparison
    print(f"=== Comparing ===")
    print(f"  A: {file_a} ({len(ast_a.raw)} bytes)")
    print(f"  B: {file_b} ({len(ast_b.raw)} bytes)")
    print()

    # Check binary identity first
    if ast_a.raw == ast_b.raw:
        print("Files are byte-identical!")
        return

    # Deps comparison
    if ast_a.deps != ast_b.deps:
        print("Dependencies differ:")
        print(f"  A: {ast_a.deps}")
        print(f"  B: {ast_b.deps}")
        print()
    else:
        print(f"Dependencies: identical ({len(ast_a.deps)} deps)")

    # Source path comparison
    if ast_a.source_path != ast_b.source_path:
        print(f"Source path differs:")
        print(f"  A: {ast_a.source_path}")
        print(f"  B: {ast_b.source_path}")
        print()
    else:
        print(f"Source path: {ast_a.source_path}")

    # Marshal header comparison
    hdr_a, hdr_b = ast_a.marshal_header, ast_b.marshal_header
    header_match = all(hdr_a[k] == hdr_b[k] for k in hdr_a)
    if not header_match:
        print()
        print("Marshal header differs:")
        for key in ("data_len", "num_objects", "size_32", "size_64"):
            va, vb = hdr_a[key], hdr_b[key]
            marker = " <--" if va != vb else ""
            print(f"  {key:15s}  A={va:8d}  B={vb:8d}{marker}")
    else:
        print(f"Marshal header: identical (data_len={hdr_a['data_len']}, objects={hdr_a['num_objects']})")

    print()

    # Decode both
    root_a, dec_a = ast_a.decode_ast()
    root_b, dec_b = ast_b.decode_ast()

    # Find first byte difference in marshal payload
    payload_a = ast_a.marshal_payload
    payload_b = ast_b.marshal_payload
    first_byte_diff = None
    for i in range(min(len(payload_a), len(payload_b))):
        if payload_a[i] != payload_b[i]:
            first_byte_diff = i
            break
    if first_byte_diff is None and len(payload_a) != len(payload_b):
        first_byte_diff = min(len(payload_a), len(payload_b))

    if first_byte_diff is not None:
        print(f"First byte difference in marshal payload at offset {first_byte_diff}")
        # Show hex context
        start = max(0, first_byte_diff - 8)
        end_a = min(len(payload_a), first_byte_diff + 16)
        end_b = min(len(payload_b), first_byte_diff + 16)
        print(f"  A: ...{payload_a[start:end_a].hex(' ')}...")
        print(f"  B: ...{payload_b[start:end_b].hex(' ')}...")
        print()

    # Tree comparison
    diffs = compare_trees(root_a, root_b)
    if not diffs:
        print("AST trees are structurally identical (but binary encoding differs)")
    else:
        print(f"Found {len(diffs)} difference(s) in AST tree:")
        print()
        for i, diff in enumerate(diffs):
            print(f"  [{i+1}] {diff['kind']} at {diff['path']}")
            print(f"      A: {diff['a']}")
            print(f"      B: {diff['b']}")
            print()

    # Stats comparison
    stats_a = gather_stats(root_a)
    stats_b = gather_stats(root_b)
    print("Object counts:")
    print(f"  {'':20s}  {'A':>8s}  {'B':>8s}")
    for key in ("blocks", "strings", "ints", "shared_refs", "doubles"):
        va, vb = stats_a[key], stats_b[key]
        marker = " <--" if va != vb else ""
        print(f"  {key:20s}  {va:8d}  {vb:8d}{marker}")


# ── Subcommand: summary ─────────────────────────────────────────────────

def cmd_summary(args):
    """Show a quick overview of a binary AST file."""
    if len(args) < 1:
        print("Usage: inspect_binary_ast.py summary <file.ast>", file=sys.stderr)
        sys.exit(1)

    filepath = args[0]
    ast_file = BinaryAstFile(filepath)

    print(f"File: {filepath}")
    print(f"Size: {len(ast_file.raw)} bytes")
    print(f"Dependencies ({len(ast_file.deps)}): {', '.join(ast_file.deps) if ast_file.deps else '(none)'}")
    print(f"Source path: {ast_file.source_path}")
    print()

    hdr = ast_file.marshal_header
    print(f"Marshal header:")
    print(f"  data_len    = {hdr['data_len']}")
    print(f"  num_objects = {hdr['num_objects']}")
    print(f"  size_32     = {hdr['size_32']}")
    print(f"  size_64     = {hdr['size_64']}")
    print()

    root, decoder = ast_file.decode_ast()
    stats = gather_stats(root)

    print(f"Object statistics:")
    print(f"  Blocks:      {stats['blocks']}")
    print(f"  Strings:     {stats['strings']}")
    print(f"  Integers:    {stats['ints']}")
    print(f"  Shared refs: {stats['shared_refs']}")
    print(f"  Doubles:     {stats['doubles']}")
    print(f"  Total objects (blocks+strings+doubles): {decoder.obj_counter}")
    print()

    # Block type histogram
    print(f"Block type histogram (top 15):")
    for key, count in stats["block_types"].most_common(15):
        print(f"  {key:35s}  {count:6d}")
    print()

    # Type hint histogram
    if stats["type_hints"]:
        print(f"Inferred types:")
        for key, count in stats["type_hints"].most_common():
            print(f"  {key:20s}  {count:6d}")
        print()

    # Top shared targets
    if stats["shared_targets"]:
        print(f"Top shared targets (most referenced, top 10):")
        for target_idx, count in stats["shared_targets"].most_common(10):
            target_obj = decoder.objects.get(target_idx)
            if target_obj:
                desc = _describe_object(target_obj)
            else:
                desc = "???"
            print(f"  [{target_idx:5d}] referenced {count:4d}x  {desc}")
    print()

    # Top string values
    print(f"Top string values (top 10):")
    for val, count in stats["string_values"].most_common(10):
        display = repr(val) if len(val) < 60 else repr(val[:57] + "...")
        print(f"  {display:40s}  {count:6d}")


def _describe_object(obj):
    """Short description of a decoded object for sharing reports."""
    if isinstance(obj, StringNode):
        val = repr(obj.value) if len(obj.value) < 40 else repr(obj.value[:37] + "...")
        return f"STRING {val}"
    if isinstance(obj, BlockNode):
        hint = f" ({obj.type_hint})" if obj.type_hint else ""
        return f"BLOCK tag={obj.tag} size={len(obj.children)}{hint}"
    if isinstance(obj, DoubleNode):
        return f"DOUBLE {obj.value}"
    return repr(obj)


# ── Subcommand: sharing ─────────────────────────────────────────────────

def cmd_sharing(args):
    """Analyze sharing patterns in a binary AST file."""
    if len(args) < 1:
        print("Usage: inspect_binary_ast.py sharing <file.ast>", file=sys.stderr)
        sys.exit(1)

    filepath = args[0]
    ast_file = BinaryAstFile(filepath)
    root, decoder = ast_file.decode_ast()

    # Collect all shared references
    shared_refs = []
    _collect_shared_refs(root, shared_refs)

    print(f"File: {filepath}")
    print(f"Total objects: {decoder.obj_counter}")
    print(f"Total shared references: {len(shared_refs)}")
    print()

    # Group by target
    by_target = collections.defaultdict(list)
    for ref in shared_refs:
        by_target[ref.target_idx].append(ref)

    # Sort by reference count (most shared first)
    sorted_targets = sorted(by_target.items(), key=lambda x: -len(x[1]))

    print(f"Shared objects (grouped by target, {len(sorted_targets)} unique targets):")
    print()

    for target_idx, refs in sorted_targets:
        target_obj = decoder.objects.get(target_idx)
        desc = _describe_object(target_obj) if target_obj else "???"

        print(f"  [{target_idx:5d}] {desc}")
        print(f"         Referenced {len(refs)}x, offsets: {', '.join(str(r.offset) for r in refs[:20])}", end="")
        if len(refs) > 20:
            print(f" ... (+{len(refs)-20} more)", end="")
        print()

        # Show target content for Positions and strings
        if isinstance(target_obj, BlockNode) and target_obj.type_hint == "Position":
            _print_position_detail(target_obj)
        if isinstance(target_obj, BlockNode) and target_obj.type_hint == "Location":
            _print_location_detail(target_obj, decoder)
        print()


def _collect_shared_refs(node, refs):
    """Iteratively collect all SharedNode references."""
    stack = [node]
    while stack:
        node = stack.pop()
        if isinstance(node, SharedNode):
            refs.append(node)
        elif isinstance(node, BlockNode):
            for child in reversed(node.children):
                stack.append(child)


def _print_position_detail(pos_node):
    """Print details of a Position block."""
    if len(pos_node.children) == 4:
        fname = pos_node.children[0]
        lnum = pos_node.children[1]
        bol = pos_node.children[2]
        cnum = pos_node.children[3]
        fname_str = fname.value if isinstance(fname, StringNode) else (
            f"SHARED->{fname.target_idx}" if isinstance(fname, SharedNode) else "?")
        lnum_val = lnum.value if isinstance(lnum, IntNode) else "?"
        cnum_val = cnum.value if isinstance(cnum, IntNode) else "?"
        print(f"         Position: {fname_str}:{lnum_val}:{cnum_val}")


def _print_location_detail(loc_node, decoder):
    """Print details of a Location block."""
    if len(loc_node.children) == 3:
        start = loc_node.children[0]
        end = loc_node.children[1]
        ghost = loc_node.children[2]

        def resolve_pos(child):
            if isinstance(child, BlockNode) and child.type_hint == "Position":
                return child
            if isinstance(child, SharedNode):
                target = decoder.objects.get(child.target_idx)
                if isinstance(target, BlockNode) and target.type_hint == "Position":
                    return target
            return None

        start_pos = resolve_pos(start)
        end_pos = resolve_pos(end)

        if start_pos and end_pos:
            def pos_str(p):
                lnum = p.children[1].value if isinstance(p.children[1], IntNode) else "?"
                cnum = p.children[3].value if isinstance(p.children[3], IntNode) else "?"
                bol = p.children[2].value if isinstance(p.children[2], IntNode) else 0
                col = cnum - bol if isinstance(cnum, int) and isinstance(bol, int) else "?"
                return f"{lnum}:{col}"

            ghost_val = ghost.value if isinstance(ghost, IntNode) else "?"
            print(f"         Location: {pos_str(start_pos)}-{pos_str(end_pos)} ghost={ghost_val}")


# ── Subcommand: test ─────────────────────────────────────────────────────

def _find_project_root():
    """Find the project root by looking for Cargo.toml."""
    d = os.path.dirname(os.path.abspath(__file__))
    while d != "/":
        if os.path.exists(os.path.join(d, "compiler-rust", "Cargo.toml")):
            return d
        d = os.path.dirname(d)
    # Fallback
    return os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _get_platform():
    """Get platform string like darwin-arm64."""
    system = platform_mod.system()
    machine = platform_mod.machine()
    if system == "Darwin":
        if machine == "arm64":
            return "darwin-arm64"
        return "darwin-x64"
    if system == "Linux":
        if machine in ("aarch64", "arm64"):
            return "linux-arm64"
        return "linux-x64"
    return "unknown"


def cmd_test(args):
    """Run both compilers on a source file and compare outputs."""
    if len(args) < 1:
        print("Usage: inspect_binary_ast.py test <source.res>", file=sys.stderr)
        sys.exit(1)

    source = args[0]
    if not os.path.exists(source):
        print(f"Error: source file not found: {source}", file=sys.stderr)
        sys.exit(1)

    project_root = _find_project_root()
    plat = _get_platform()

    rust_target = os.environ.get("RUST_TARGET", "debug")
    subprocess.run([os.path.join(project_root, "scripts", "rust_compiler_links.sh"), rust_target], check=True)
    rust_bsc = os.path.join(project_root, "rewatch", "target", rust_target, "bsc")
    ocaml_bsc = os.path.join(project_root, "packages", "@rescript", plat, "bin", "bsc.exe")

    # Check executables
    for name, path in [("Rust bsc", rust_bsc), ("OCaml bsc", ocaml_bsc)]:
        if not os.path.exists(path):
            print(f"Error: {name} not found at {path}", file=sys.stderr)
            sys.exit(1)

    # Determine output extension
    is_interface = source.endswith(".resi")
    ext = ".iast" if is_interface else ".ast"

    import tempfile
    with tempfile.TemporaryDirectory() as tmpdir:
        ocaml_out = os.path.join(tmpdir, "ocaml" + ext)
        rust_out = os.path.join(tmpdir, "rust" + ext)

        # Run OCaml bsc
        print(f"Running OCaml bsc...")
        ocaml_cmd = [ocaml_bsc, "-bs-ast", source, "-o", ocaml_out]
        result = subprocess.run(ocaml_cmd, capture_output=True, timeout=10)
        if result.returncode != 0:
            print(f"OCaml bsc failed (exit {result.returncode}):")
            print(result.stderr.decode("utf-8", errors="replace"))
            sys.exit(1)

        # bsc may create .iast regardless of -o for interface files
        if not os.path.exists(ocaml_out):
            alt = os.path.join(tmpdir, "ocaml.iast")
            if os.path.exists(alt):
                ocaml_out = alt

        # Run Rust bsc
        print(f"Running Rust bsc...")
        rust_cmd = [rust_bsc, "-bs-ast", source, "-o", rust_out]
        result = subprocess.run(rust_cmd, capture_output=True, timeout=10)
        if result.returncode != 0:
            print(f"Rust bsc failed (exit {result.returncode}):")
            print(result.stderr.decode("utf-8", errors="replace"))
            sys.exit(1)

        if not os.path.exists(rust_out):
            alt = os.path.join(tmpdir, "rust.iast")
            if os.path.exists(alt):
                rust_out = alt

        # Check both exist
        if not os.path.exists(ocaml_out):
            print(f"Error: OCaml output not found at {ocaml_out}", file=sys.stderr)
            sys.exit(1)
        if not os.path.exists(rust_out):
            print(f"Error: Rust output not found at {rust_out}", file=sys.stderr)
            sys.exit(1)

        # Quick binary check
        with open(ocaml_out, "rb") as f:
            ocaml_data = f.read()
        with open(rust_out, "rb") as f:
            rust_data = f.read()

        if ocaml_data == rust_data:
            print(f"\nPARITY OK: Files are byte-identical ({len(ocaml_data)} bytes)")
            return

        print(f"\nPARITY MISMATCH: OCaml={len(ocaml_data)} bytes, Rust={len(rust_data)} bytes")
        print()

        # Run compare
        cmd_compare([ocaml_out, rust_out])


# ── Main entry point ────────────────────────────────────────────────────

SUBCOMMANDS = {
    "decode": cmd_decode,
    "compare": cmd_compare,
    "summary": cmd_summary,
    "sharing": cmd_sharing,
    "test": cmd_test,
}

def main():
    if len(sys.argv) < 2 or sys.argv[1] in ("-h", "--help"):
        print(__doc__)
        print("Subcommands:")
        for name, func in SUBCOMMANDS.items():
            doc = (func.__doc__ or "").strip().split("\n")[0]
            print(f"  {name:12s}  {doc}")
        sys.exit(0)

    subcmd = sys.argv[1]
    if subcmd not in SUBCOMMANDS:
        print(f"Unknown subcommand: {subcmd}", file=sys.stderr)
        print(f"Available: {', '.join(SUBCOMMANDS.keys())}", file=sys.stderr)
        sys.exit(1)

    SUBCOMMANDS[subcmd](sys.argv[2:])


if __name__ == "__main__":
    main()
