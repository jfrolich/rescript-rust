# RFC: Reserved words as record field names, argument labels and JSX props

Status: draft, not yet posted.

## Summary

Allow a reserved word (`type`, `open`, `in`, `as`, `for`, `module`, ...) wherever
the grammar expects a **label**: a record field name, a labelled-argument name
or a JSX prop name.

```rescript
type input = {type: string, mutable open: bool, in?: int}

let make = kind => {type: kind, open: false}
let kind = input => input.type
let close = input => input.open = false

let isText = input =>
  switch input {
  | {type: "text"} => true
  | _ => false
  }

let button = (~type as kind, ~for as target=?) => ...
let submit = button(~type="submit")
let el = <input type="text" />
```

Reserved words stay reserved wherever a name is **bound or looked up**: as a
variable, a type or a module. `let type = 1` remains an error, and so does
every shorthand that would need a variable with that name (`{type}`, `~type`,
`<input type />`).

This is the distinction JavaScript has made since ES5 between `Identifier` and
`IdentifierName`: `obj.class` and `{class: 1}` are valid, `let class` and the
shorthand `{class}` are not.

The change is confined to the parser and the printers. The AST, the type
checker and the generated JavaScript are untouched: a field named `type` can
already be written as `\"type"` today and compiles to the expected code.

## Motivation

### The workaround is boilerplate, and it leaks into user code

A record that mirrors a JavaScript object with a `type` key is written like
this today:

```rescript
type input = {
  @as("type") type_: string,
  @as("open") open_?: bool,
}

let kind = input => input.type_
```

Every reader has to know that `type_` means `type`, and every author has to
invent the name (`type_`, `_type`, `typ` and `kind` are all in use). The names
no longer match the JavaScript documentation of the library being bound.

`type` is one of the most common keys in JavaScript data: DOM attributes,
event objects, Redux-style actions, GeoJSON, JSON Schema, and nearly every
discriminated union. The standard library pays this cost itself:
`JsxDOM.domProps` declares `type_`, `as_`, `open_` and `in_` with an `@as` each,
and `JsxEvent` exposes `type_`.

### Every new keyword breaks field names

ReScript 13 makes `break` and `continue` keywords. A record with a field named
`continue` (a pagination cursor in several HTTP APIs) compiled in 12 and is a
syntax error in 13. If field names were not subject to keyword reservation,
adding a keyword would only affect variables of that name.

### Hyphenated JSX props fail with a misleading error

`<div data-type="a" />`, `<label aria-for="x" />` and `<div data-open />` are
rejected today with "JSX identifier cannot end with a hyphen", because the
segment after the hyphen is scanned as a keyword.

### The compiler already supports these names

Only the surface syntax stands in the way. With the escape syntax, a keyword
is accepted in every position this RFC covers. ReScript 12.3.1 compiles

```rescript
type t = {\"type": string, mutable \"open": bool, \"in"?: int}
let make = kind => {\"type": kind, \"open": false}
let get = r => r.\"type"
let close = r => r.\"open" = false
let f = r =>
  switch r {
  | {\"type": "a", \"in": ?x} => x
  | _ => None
  }
```

to

```js
function make(kind) {
  return {
    type: kind,
    open: false
  };
}

function get(r) {
  return r.type;
}

function close(r) {
  r.open = false;
}

function f(r) {
  if (r.type === "a") {
    return r.in;
  }
}
```

Labels and JSX props behave the same. A component declared with
`(~\"type" as kind)` gets a props record with a field `type`, reads
`props.type`, and `<Button \"type"="submit" />` passes `{type: "submit"}`.

The type checker, pattern-match compiler, JSX transform and code generator
need no change. Type errors already print the field as `type`.

The parser, too, already recognises the intent. Since
[rescript-lang/rescript#7784](https://github.com/rescript-lang/rescript/pull/7784)
it detects "keyword followed by `:` at a field position", reports "Cannot use
keyword `type` as a record field name", and recovers by building a field named
`type_`. This RFC turns that recovery path into the accepted path.

## Proposal

### The rule

> A reserved word is reserved only where a name is bound or looked up as a
> variable, type or module. Where the grammar expects a label, any
> identifier-shaped word is a name.

"Reserved word" means the 28 word-shaped keywords of `Res_token.keyword_table`:

```
and as assert await break constraint continue else exception external false
for if in include let module mutable of open private rec switch true try type
when while
```

`list{` and `dict{` are not included: `list` and `dict` are ordinary
identifiers already, and only the form glued to `{` is a token.

### Label positions

| Position | Accepted | How the parser knows |
|---|---|---|
| Field access | `r.type`, `r.M.type` | word directly after the `.` of a field access, on the same line |
| Field update | `r.type = v` | same |
| Record expression | `{type: v}`, `{...r, type: v}`, `{type: ?v}`, `{M.type: v}` | word followed by `:` where a row starts |
| Record pattern | `{type: p}`, `{type: ?p}`, `{M.type: p}` | word followed by `:` where a row starts |
| Record type | `{type: t}`, `{type?: t}`, `{mutable type: t}`, inline records in constructors | word followed by `:` or `?` where a field starts |
| Parameter | `(~type as p) => e`, `(~type as p=d) => e`, `(~type as p=?) => e` | word directly after `~` |
| Argument | `f(~type=v)`, `f(~type=?v)` | word directly after `~` |
| Function type | `(~type: t) => u`, `(~type: t=?) => u` | word directly after `~` |
| JSX prop | `<input type="a" />`, `<input type=?v />`, `<div data-type="a" />` | word where a prop starts, or after a `-` inside a prop name |

Every form in the "Accepted" column is a syntax error in ReScript 12.3.1
(tested, with `type`), so no program that compiles today changes meaning.

### What stays an error

A shorthand stands for a variable with the same name as the label, and a
variable cannot be named by a reserved word. These get a dedicated message
that shows the long form:

| Rejected | Message suggests |
|---|---|
| `{type}`, `{?type}` (expression) | `{type: value}` |
| `{type}`, `{?type}` (pattern) | `{type: kind}` |
| `type t = {type}` (field whose type has the same name) | `{type: t}` |
| `(~type) => e`, `(~type: t) => e`, `(~type=d) => e` | `~type as kind` |
| `f(~type)`, `f(~type?)`, `f(~type: t)` | `~type=value` |
| `<input type />`, `<input ?type />` | `type=value` |

Unchanged, and still errors: `let type = 1`, a function parameter or pattern
variable named `type`, a type or module named `type`, a value path `M.type`,
and a type variable `'type`.

The escape `\"type"` keeps working everywhere it works today. It is still
needed for a variable named like a keyword and for names that are not
identifier-shaped.

## Why this is unambiguous

The parser is recursive descent and always knows which production it is in.
Each label position is entered on a token that is not a keyword (`.`, `~`, `{`,
`,`, a JSX tag name), and inside it a keyword token currently has no meaning:
the parser reports an error. The proposal gives that slot a meaning without
taking one away. Per position:

**After `.`** A field access is the `.` that follows an operand. Nothing but a
field name or a module path can follow it. The legacy uncurried dot (`f(. x)`,
`(. int) => int`) is a different production: it appears where an argument or
parameter starts, never after an operand, so `f(. true)` is unaffected.

**After `~`** `~` is used for labels only. `~~~` is a separate token.

**JSX props** After the tag name, only prop names, `?`, `{...spread}`, `/` and
`>` can appear.

**Record patterns and record types** The row or field starts after `{` or `,`.
A keyword cannot start anything else there, apart from the `mutable` modifier
discussed below.

**Record expressions: the one place with a real choice.** `{` in expression
position starts either a record or a block, and a block may start with a
keyword: `{let x = 1; x}`, `{if a {b} else {c}}`, `{switch x {...}}`,
`{open M; e}`, `{true}`, `{await p}`. The proposal decides with one token of
lookahead: a reserved word followed by `:` starts a record. No block item
starts that way. `let`, `open`, `module`, `exception`, `if`, `switch`, `while`,
`for`, `try`, `assert` and `await` are each followed by a pattern, a path or an
expression; `true` and `false` are followed by an operator or the end of the
block (`{true ? a : b}` has `?` after `true`); `break` and `continue` stand
alone. The other reserved words cannot start a block item at all. A type
constraint needs parentheses, so `{true: bool}` is not an expression today.
This is the same test the parser already applies to produce the current error
message.

Three details need care:

1. **`mutable`** is itself a reserved word and a field modifier. In a record
   type, `mutable` followed by `:` or `?` is a field named `mutable`;
   otherwise it is the modifier. So `{mutable: bool}`, `{mutable x: int}` and
   `{mutable mutable: bool}` all parse.

2. **`let?`** is scanned as a single token when `?` directly follows `let`.
   Where a label is expected, the parser reads it as the name `let` followed
   by `?`. This matters for `type t = {let?: int}`.

3. **Line breaks after `.`** A reserved word is taken as a field name only if
   it is on the same line as the `.`. No valid program needs the other form,
   and the formatter never breaks between the `.` and the name. The rule
   protects code that is being typed:

   ```rescript
   let name = user.
   let age = 2
   ```

   Today the parser reports an error at `let` and still parses `let age = 2`
   as a binding, which is what editor completion relies on. Without the rule
   it would read `user.let` and lose the next binding. TypeScript's parser has
   a similar line-break check in `parseRightSideOfDot`, for the same reason.
   Ordinary identifiers may still follow a `.` on the next line, as they do
   now.

## Parser changes

All in `compiler/syntax/src`. No change to `parsetree.ml`, and therefore none
to `parsetree0.ml` or the PPX mapping.

### `res_token.ml`

Add `reserved_word : t -> string option`, returning the text of the 28 words
above. `Token.is_keyword` cannot be reused: it also answers true for `&&`, `||`,
`list{` and `dict{`.

### `res_core.ml`

One new helper does the work in most places:

```ocaml
(* A label: an identifier, or a reserved word standing for a name. *)
let parse_label_name p : (string * Location.t) option
```

It accepts `Lident`, and a token for which `Token.reserved_word` is `Some`. For
the token `Let {unwrap = true}` it returns `let` and leaves a `Question` token
in place of the consumed `let?`.

| Function | Today | Change |
|---|---|---|
| `parse_value_path_after_dot`, called from `parse_primary_expr` | accepts `Lident` or `Uident`, otherwise "unexpected token" | accept a reserved word on the same line as the `.`; the same for the last segment of `r.M.type` |
| `parse_braced_or_record_expr` | a keyword followed by `:` reports `keyword_field_in_expr` and recovers as `type_`; `break` and `continue` go to the block parser before that test | move the "reserved word followed by `:`" test first and build the row with the real name, no diagnostic |
| `parse_record_expr_row` | same recovery for later rows | same replacement; a reserved word without `:` reports the punning error |
| `parse_record_pattern_row` | same recovery, `keyword_field_in_pattern` | same replacement |
| `parse_field_declaration_region`, `parse_field_declaration` | consume `mutable`, then the same recovery, `keyword_field_in_type` | treat `mutable` as a name when `:` or `?` follows; accept a reserved word followed by `:` or `?` |
| `parse_parameter` | `parse_lident` after `~` | `parse_label_name`; for a reserved word, require `as` and report the punning error otherwise |
| `parse_argument2` | matches `Lident` after `~` | also match a reserved word; require `=` and report the punning error otherwise |
| `parse_type_parameter`, `parse_es6_arrow_type` | `parse_lident` after `~` | `parse_label_name` |
| `peek_ident`, used by `read_local_jsx_name` and `read_hyphen_chain` | `Lident` or `Uident` | for prop names and for segments after `-`, also a reserved word |
| `parse_jsx_prop` | starts on `Lident` or `?` | also on a reserved word; require `=` and report the punning error otherwise |

Qualified labels (`{M.type: v}`, `{M.type: p}`, `r.M.type`) go through a
`parse_field_path` that accepts a reserved word as the last segment.
`parse_value_path` itself stays as it is, because type constructor paths and
`with` constraints use it too and must keep rejecting keywords.

The lookahead that decides whether `(` starts an arrow function
(`is_es6_arrow_expression`) skips to the closing parenthesis without looking at
the tokens between, so `(~type as kind) => ...` needs no change there.

`Error_messages.keyword_field_in_expr`, `keyword_field_in_pattern` and
`keyword_field_in_type` are replaced by the punning messages.
`recover_keyword_field_name_if_probably_field` is removed.

### `res_grammar.ml`

The predicates that gate list parsing get the reserved words:
`is_pattern_record_item_start`, `is_record_decl_start` and
`is_jsx_attribute_start`. `is_record_row_start` and `is_field_decl_start` have
them already, for today's error recovery.

## Printer changes

`res_printer.ml` escapes any name that is a keyword: `print_ident_like` prints
`type` as `\"type"`. It gains a label mode that prints a reserved word bare,
used where labels are printed: field declarations, record expression and
pattern rows, field access and update, argument labels in definitions, calls
and types, and JSX prop names.

A punned row, argument or prop keeps its escape, because the pun names a
variable: `{\"type": \"type", name}` is printed as `{\"type", name}` today and
stays that way.

`res_outcome_printer.ml`, which prints types in error messages, hovers and
generated interfaces, gets the same treatment for record fields and labels.

The formatter therefore rewrites `{\"type": x}` to `{type: x}`. Parsing the
printed form gives the same AST.

## What does not change

- **AST and PPX.** A field named `type` is `Lident "type"`, the same node
  `\"type"` produces. PPXs see nothing new.
- **Type checker and generated JavaScript.** See the example under Motivation.
- **`.cmi`, `.cmt` and build artifacts.**
- **`@as`.** Still needed for runtime names that are not identifier-shaped
  (`@as("aria-label")`) and for renaming for other reasons.
- **`@deriving(accessors)`.** It generates a function named after each field.
  For a field named `type` that function can only be called as `\"type"`,
  as is already the case for escaped field names.

## Compatibility and migration

The change is additive. `type_` with `@as("type")` keeps compiling, and so
does `\"type"`. Nothing has to migrate.

Code that uses the new syntax does not parse with older compilers, and the
formatter of a new compiler rewrites escaped labels to the bare form. Both
are bounded by a project's pinned compiler version.

Changing `JsxDOM.domProps` from `type_`, `as_`, `open_` and `in_` to the bare
names is a separate, breaking step for the standard library and is not part
of this RFC.

## Tooling

- **Syntax highlighting.** The TextMate grammar in `rescript-vscode` and
  `tree-sitter-rescript` treat these words as keywords everywhere. Both need a
  rule for the label positions; until then `type` in `{type: x}` is coloured as
  a keyword, which is cosmetic.
- **Editor completion.** Field, label and prop completions should insert the
  bare name.
- **Documentation.** The "reserved keywords" page and the binding guides that
  recommend `@as("type") type_`.

## Prior art

- **JavaScript**, since ES5: reserved words are valid property names in
  object literals and after `.`, but not as bindings or in shorthand
  properties.
- **TypeScript**: the same, plus a line-break check after `.` for error
  recovery.
- **Swift**: SE-0001 allowed keywords as argument labels, and SE-0071 allowed
  them after `.` in member references.
- **ReScript**: attribute and extension names already accept keywords
  (`@module`, `@as`, `@private`, `%private`), through `parse_attribute_id`.
  Object types and object access use string labels, so `{"type": string}` and
  `obj["type"]` have never been restricted.

## Alternatives considered

- **Keep `@as`.** Costs nothing in the compiler, and keeps the costs listed
  under Motivation.
- **Mangle `type_` to `type` automatically.** JSX v3 did this for props, and
  JSX v4 removed it in favour of `@as`. Implicit renaming is hard to discover
  and hits names that really end in an underscore.
- **Make keywords fully contextual**, so `let type = 1` works. This is the
  ambiguous part of the grammar (`type` at the start of a block item, `open`
  before a module path) and would need unbounded lookahead or rules that
  depend on line breaks.
- **Allow punning by inventing a variable name.** `{type}` would have to bind
  something other than `type`; any choice is a surprise.
- **Field access only.** Smallest change, but a field that can be read and not
  declared or constructed does not remove the workaround.

## Drawbacks

- The same word is a keyword in one place and a name in another, which is
  harder to highlight with regular expressions.
- Punning does not work for these fields. JavaScript has the same asymmetry.
- Postfix syntax of the form `expr.keyword` (such as Rust's `.await`) can no
  longer be added later.

## Open questions

1. **Polymorphic variant tags.** `#type` is rejected today and has to be
   written `#"type"`. A keyword after `#` is as unambiguous as after `~`.
   Include it here, or leave it, since the string form exists and is what the
   formatter prints?
2. **Scope of the first step.** Record fields alone, or record fields together
   with labels and JSX props as proposed? Record fields alone do not let a
   component take a `type` prop without the escape.
3. **`true` and `false`** as labels: included for uniformity with JavaScript.
   Is there a reason to exclude them?
4. **Lowercase JSX tag names.** `<switch>` is an SVG element and is rejected
   today. It could be allowed by the same reasoning (`<` in operand position
   always starts JSX), but it is not a label and is left out for now.
5. **The line-break rule after `.`**: keep it as proposed, or accept any
   position and live with worse recovery while typing?

## Implementation plan

1. Parser, printer and outcome printer, with syntax tests for every row of
   both tables above, round-trip tests through the formatter, and updated
   snapshots for the existing keyword-field error tests.
2. Editor completion and the two highlighting grammars.
3. Documentation.
4. Separately: decide on the `JsxDOM` rename.
