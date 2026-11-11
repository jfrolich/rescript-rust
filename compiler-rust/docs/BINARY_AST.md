# Binary AST Implementation

This document describes the binary AST serialization in the Rust compiler.

## Status

The `.ast` files are an intermediate representation that only this build
system reads; they are not compared with the OCaml compiler's (there is no
parse-tree or `bsc -bs-ast` parity test). Byte layout, position sharing and
FFI metadata encoding may all differ from OCaml as long as the Rust compiler
reads back what it wrote and the generated JavaScript is unchanged.

---

## Table of Contents

1. [Overview](#overview)
2. [Binary AST File Format](#binary-ast-file-format)
3. [OCaml Marshal Format Specification](#ocaml-marshal-format-specification)
4. [Arena-Based Identity Sharing](#arena-based-identity-sharing)
5. [Type System Mapping](#type-system-mapping)
6. [Parsetree0 Transformations](#parsetree0-transformations)
7. [References](#references)

---

## Overview

The ReScript compiler uses binary AST files (`.ast` for implementations, `.iast` for interfaces) as an intermediate format for:

1. **Incremental compilation**: Cached parsed ASTs avoid re-parsing unchanged files
2. **External PPXs** (not supported going forward): they read and write binary ASTs
3. **Build system integration**: `rewatch` uses binary AST files for dependency tracking

Byte-identical output with the OCaml compiler is not a goal.

---

## Binary AST File Format

The binary AST file has three sections:

```
+-----------------------------------------------------------------------+
| SECTION 1: Header                                                     |
+-----------------------------------------------------------------------+
| Offset 0-3: Dependency section size (4 bytes, big-endian u32)         |
+-----------------------------------------------------------------------+
| SECTION 2: Dependencies + Source Path                                 |
+-----------------------------------------------------------------------+
| Byte 4: '\n' (0x0A) - separator                                       |
| "ModuleName1\n"                                                       |
| "ModuleName2\n"                                                       |
| ...                                                                   |
| "/" - terminates deps AND starts absolute path                        |
| "Users/path/to/source.res\n" - rest of path + newline                 |
+-----------------------------------------------------------------------+
| SECTION 3: OCaml Marshal Data                                         |
+-----------------------------------------------------------------------+
| Magic: 0x84 0x95 0xA6 0xBE (4 bytes)                                  |
| Header: data_len(4) + obj_count(4) + size_32(4) + size_64(4)          |
| Payload: Encoded parsetree0 AST                                       |
+-----------------------------------------------------------------------+
```

### Section Details

#### Section 1: Size Header (4 bytes)
```
Offset  Size  Description
0       4     Big-endian u32: size of dependency section (including leading '\n')
```

#### Section 2: Dependencies + Source Path (variable)
The dependency section contains:
1. A leading newline `\n` (0x0A)
2. Module names, each followed by `\n`
3. A `/` character that terminates deps and starts the absolute source path

**Example** (file at `/Users/dev/project/src/Demo.res` with deps `Js` and `React`):
```
00000000: 00 00 00 0c                                      # Size = 12
00000004: 0a                                               # '\n'
00000005: 4a 73 0a                                         # "Js\n"
00000008: 52 65 61 63 74 0a                                # "React\n"
0000000e: 2f                                               # "/" (end deps + start path)
0000000f: 55 73 65 72 73 2f 64 65 76 2f ...               # "Users/dev/..."
         ... 44 65 6d 6f 2e 72 65 73 0a                   # "Demo.res\n"
```

---

## OCaml Marshal Format Specification

### Magic Number
```rust
const MAGIC_NUMBER_SMALL: u32 = 0x8495A6BE;  // Standard format
```

### Header Format (20 bytes)
```
Offset  Size  Description
0       4     Magic number (0x8495A6BE)
4       4     Data length (bytes after header)
8       4     Object count (number of objects in sharing table)
12      4     Size on 32-bit platform (words)
16      4     Size on 64-bit platform (words)
```

### Opcode Reference

#### Prefix Codes (Compact Encoding)
| Range     | Binary Pattern | Description                                          |
|-----------|----------------|------------------------------------------------------|
| 0x80-0xBF | `10xxxxxx`     | Small block: tag = (byte >> 4) & 0xF, size = byte & 0x7 |
| 0x40-0x7F | `01xxxxxx`     | Small int: value = byte & 0x3F (0-63)                |
| 0x20-0x3F | `001xxxxx`     | Small string: length = byte & 0x1F (0-31)            |

#### Explicit Codes
| Code            | Value | Description                                    |
|-----------------|-------|------------------------------------------------|
| `CODE_INT8`     | 0x00  | 8-bit signed integer follows                   |
| `CODE_INT16`    | 0x01  | 16-bit signed integer follows (big-endian)     |
| `CODE_INT32`    | 0x02  | 32-bit signed integer follows (big-endian)     |
| `CODE_INT64`    | 0x03  | 64-bit signed integer follows (big-endian)     |
| `CODE_SHARED8`  | 0x04  | Reference to shared object (8-bit distance)    |
| `CODE_SHARED16` | 0x05  | Reference to shared object (16-bit distance)   |
| `CODE_SHARED32` | 0x06  | Reference to shared object (32-bit distance)   |
| `CODE_BLOCK32`  | 0x08  | Block with 32-bit header (tag + size)          |
| `CODE_STRING8`  | 0x09  | String with 8-bit length                       |
| `CODE_STRING32` | 0x0A  | String with 32-bit length                      |

### Value Encoding

#### Integers
```rust
fn write_int(w: &mut Writer, n: i64) {
    if n >= 0 && n < 0x40 {
        w.write_u8(PREFIX_SMALL_INT + (n as u8));  // Single byte
    } else if n >= -128 && n < 128 {
        w.write_u8(CODE_INT8);
        w.write_i8(n as i8);
    } else if n >= -32768 && n < 32768 {
        w.write_u8(CODE_INT16);
        w.write_i16_be(n as i16);
    } else if n >= -1073741824 && n < 1073741824 {
        w.write_u8(CODE_INT32);
        w.write_i32_be(n as i32);
    } else {
        w.write_u8(CODE_INT64);
        w.write_i64_be(n);
    }
}
```

#### Strings
```rust
fn write_string(w: &mut Writer, s: &[u8]) {
    let len = s.len();
    if len < 0x20 {
        w.write_u8(PREFIX_SMALL_STRING + (len as u8));
    } else if len < 0x100 {
        w.write_u8(CODE_STRING8);
        w.write_u8(len as u8);
    } else {
        w.write_u8(CODE_STRING32);
        w.write_u32_be(len as u32);
    }
    w.write_bytes(s);
}
```

#### Blocks (Records, Variants, Tuples)

**CRITICAL**: Small block encoding is `PREFIX_SMALL_BLOCK + tag + (sz << 4)`:
- Bits 0-3: tag (0-15)
- Bits 4-6: size (0-7)
- Bit 7: always 1 (PREFIX_SMALL_BLOCK = 0x80)

```rust
fn write_block_header(w: &mut Writer, tag: u8, size: usize) {
    if tag < 16 && size < 8 {
        w.write_u8(PREFIX_SMALL_BLOCK + tag + ((size as u8) << 4));
    } else {
        let header = ((size as u64) << 10) | (tag as u64);
        w.write_u8(CODE_BLOCK32);
        w.write_u32_be(header as u32);
    }
}
```

### Sharing Reference Distance

When Marshal encounters a previously-seen object, it writes a shared reference with the distance from the current object counter:

| Distance  | Code            | Format                    |
|-----------|-----------------|---------------------------|
| 1-255     | CODE_SHARED8    | 1 byte offset             |
| 256-65535 | CODE_SHARED16   | 2 bytes big-endian offset |
| 65536+    | CODE_SHARED32   | 4 bytes big-endian offset |

---

## Arena-Based Identity Sharing

The Rust implementation uses arena indices to track object identity for sharing. This approach matches OCaml's pointer-based sharing semantics.

### Arena Index Types

| Type        | Purpose                              |
|-------------|--------------------------------------|
| `PosIdx`    | Position arena index                 |
| `LocIdx`    | Location arena index                 |
| `StrIdx`    | String arena index                   |
| `LidentIdx` | Longident arena index                |

### How It Works

1. **Scanner creates positions with unique IDs**: Each call to `scanner.position()` assigns a new `PosIdx`

2. **Clone preserves identity**: When a position is cloned (e.g., `prev_end_pos = end_pos.clone()`), the arena index is preserved

3. **Marshal uses identity for sharing**: The marshal writer tracks seen arena indices and emits `CODE_SHARED*` for previously-seen objects

### Position Sharing Pattern

The key sharing pattern occurs in the parser's `next()` function:

```
Token 1: "let" at positions 0-3
  Scanner creates: start_pos (id=1), end_pos (id=2)
  Parser assigns: p.start_pos <- id=1, p.end_pos <- id=2

Token 2: "x" at positions 4-5
  Scanner creates: start_pos (id=3), end_pos (id=4)
  Parser assigns:
    prev_end_pos <- p.end_pos (id=2)  <- SHARING: same ID as token 1's end
    p.start_pos <- id=3
    p.end_pos <- id=4
```

When serialized, the position with id=2 is written once, and subsequent references use `CODE_SHARED*`.

---

## Type System Mapping

### Core Types

#### Lexing.position
```ocaml
type position = {
  pos_fname : string;
  pos_lnum : int;
  pos_bol : int;
  pos_cnum : int;
}
```

Encoded as a block with tag 0, size 4.

#### Location.t
```ocaml
type t = {
  loc_start: Lexing.position;
  loc_end: Lexing.position;
  loc_ghost: bool;
}
```

Encoded as a block with tag 0, size 3.

#### Longident.t
```ocaml
type t =
  | Lident of string      (* tag 0 *)
  | Ldot of t * string    (* tag 1 *)
  | Lapply of t * t       (* tag 2 *)
```

### Asttypes (Constant Constructors = Integers)

| Type           | Constructor     | Value |
|----------------|-----------------|-------|
| rec_flag       | Nonrecursive    | 0     |
| rec_flag       | Recursive       | 1     |
| direction_flag | Upto            | 0     |
| direction_flag | Downto          | 1     |
| private_flag   | Private         | 0     |
| private_flag   | Public          | 1     |
| mutable_flag   | Immutable       | 0     |
| mutable_flag   | Mutable         | 1     |
| closed_flag    | Closed          | 0     |
| closed_flag    | Open            | 1     |

### Noloc.arg_label (Mixed)

| Constructor    | Encoding              |
|----------------|-----------------------|
| Nolabel        | int 0                 |
| Labelled(s)    | Block(tag=0, [s])     |
| Optional(s)    | Block(tag=1, [s])     |

### Constant

| Constructor                    | Tag |
|--------------------------------|-----|
| Pconst_integer(s, char_opt)    | 0   |
| Pconst_char(i)                 | 1   |
| Pconst_string(s, delim_opt)    | 2   |
| Pconst_float(s, char_opt)      | 3   |

---

## Parsetree0 Transformations

The current parsetree has evolved from parsetree0. When serializing to binary AST, several transformations are applied.

### Operator Rewriting

| Current | Parsetree0 |
|---------|------------|
| `->`    | `\|.` (pipe) |
| `++`    | `^` (string concat) |
| `==`    | `=` (structural equality) |
| `===`   | `==` (physical equality) |
| `!=`    | `<>` (structural inequality) |
| `!==`   | `!=` (physical inequality) |

### JSX Transformation

JSX nodes are transformed to function application with `[@JSX]` attribute:

```
// Current parsetree
<Comp prop="value">child</Comp>

// Parsetree0
Comp(~prop="value", ~children=[child], ())[@JSX]
```

### Arrow Type Arity

When arity is present, arrow types are wrapped in `function$` type constructor:

```
// Current: (int, int) => int with arity=2
// Parsetree0: function$<(int, int) => int, [#Has_arity2]>
```

### Function Arity and Async

- When arity is present, wrap in `Function$` constructor with `[@res.arity N]`
- When async is true, add `[@res.async]` attribute

### Await Expression

`Pexp_await(expr)` becomes the inner expression with `[@res.await]` attribute.

### Partial Application

When `partial: true`, add `[@res.partial]` attribute.

---

## References

### OCaml Sources
- `runtime/extern.c` - Marshal serialization
- `runtime/caml/intext.h` - Marshal format constants

### ReScript OCaml Sources
- `compiler/syntax/src/res_scanner.ml` - Position allocation
- `compiler/syntax/src/res_parser.ml` - Position assignment
- `compiler/depends/binary_ast.ml` - Binary AST writing
- `compiler/ml/parsetree0.ml` - The former PPX AST
- `compiler/common/ast_mapper_to0.ml` - Current -> parsetree0 mapping

### Rust Implementation
- `compiler-rust/src/location.rs` - Position/Location types with arena indices
- `compiler-rust/src/parser/scanner.rs` - Position creation
- `compiler-rust/src/parser/state.rs` - Parser position tracking
- `compiler-rust/src/binary_ast/marshal.rs` - Marshal serialization
- `compiler-rust/src/binary_ast/parsetree0.rs` - Parsetree0 types
- `compiler-rust/src/binary_ast/parsetree0_mapper.rs` - Parsetree -> parsetree0 mapping

---

