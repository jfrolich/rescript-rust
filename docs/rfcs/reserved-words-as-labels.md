# RFC: Reserved words as labels, variant tags and JSX names, and ten contextual keywords

Status: draft, not yet posted.

## Summary

Two changes to how the parser treats keywords.

**1. Reserved words as names.** Allow a reserved word (`type`, `in`, `for`,
`module`, ...) wherever the grammar expects a **label** (a record field name, a
labelled-argument name or a JSX prop name), a **polymorphic variant tag** or a
**lowercase JSX tag name**.

```rescript
type request = {type: string, mutable continue: bool, include?: array<string>}

let make = kind => {type: kind, continue: false}
let kind = request => request.type
let resume = request => request.continue = true

let isQuery = request =>
  switch request {
  | {type: "query"} => true
  | _ => false
  }

let button = (~type as kind, ~for as target=?) => ...
let submit = button(~type="submit")
let el = <input type="text" />

type token = [#type | #module | #if]
let icon = <svg> <switch> ... </switch> </svg>
```

Reserved words stay reserved wherever a name is **bound or looked up**: as a
variable, a type or a module. `let type = 1` remains an error, and so does
every shorthand that would need a variable with that name (`{type}`, `~type`,
`<input type />`).

This is the distinction JavaScript has made since ES5 between `Identifier` and
`IdentifierName`: `obj.class` and `{class: 1}` are valid, `let class` and the
shorthand `{class}` are not.

**2. Contextual keywords.** Ten words stop being reserved: `as`, `constraint`,
`exception`, `external`, `mutable`, `of`, `open`, `private`, `rec` and `when`.
Each stays a keyword in the position where the grammar uses it and is an
ordinary identifier everywhere else, so it can name a variable and the
shorthands work:

```rescript
let open = dialog.open
let next = {...dialog, open}
let {private, as} = options
let render = (~as, ~open=false) => <Dialog as open />
errors->Array.forEach(exception => Console.error(exception))
```

`type` is not one of the ten. Making it contextual is left to a follow-up.

Both changes are confined to the parser and the printers. The AST, the type
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

### Variant tags and JSX elements have the same restriction

A polymorphic variant that mirrors a JavaScript string union cannot contain
`#type`, `#module`, `#if` or `#true`; these have to be written `#"type"`. The
SVG element `<switch>` cannot be written at all without the escape
(`<\"switch">`), although JSX in JavaScript accepts it.

### Shorthands need a variable of the same name

Labels alone leave the shorthands out: `{open}`, `(~as)` and
`<Dialog open />` need a variable named `open` or `as`. Ten of ReScript's
keywords are common names in JavaScript APIs (`open`, `as`, `of`, `when`,
`private`, `external`) and are used by the grammar in so few positions that
the parser can tell the keyword from a name. Nine of them are not reserved in
JavaScript at all; `private` is reserved in strict mode only.

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

### Part 1: reserved words as names

#### The rule

> A reserved word is reserved only where a name is bound or looked up as a
> variable, type or module. Where the grammar expects a label, a polymorphic
> variant tag or a lowercase JSX tag name, any identifier-shaped word is a
> name.

`Res_token.keyword_table` has 28 word-shaped keywords today. Ten of them
become contextual keywords (Part 2) and are plain identifiers in every
position of Part 1. "Reserved word" means the other 18, `true` and `false`
included:

```
and assert await break continue else false for if in include let module
switch true try type while
```

`list{` and `dict{` are not included: `list` and `dict` are ordinary
identifiers already, and only the form glued to `{` is a token.

#### Positions

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
| Variant tag | `#type`, `#type(payload)`, `\| #type => e`, `[#type \| #module]`, `[> #type]` | word directly after `#` |
| JSX tag name | `<switch>`, `</switch>`, `<switch />`, `<my-for />` | word directly after `<` or `</` where an element starts, or after a `-` inside a tag name |

Every form in the "Accepted" column is a syntax error in ReScript 12.3.1
(tested, with `type`), so no program that compiles today changes meaning.

#### What stays an error

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
a type variable `'type`, and a qualified JSX tag `<M.type />`, which looks up
the value `M.type`.

The escape `\"type"` keeps working everywhere it works today. It is still
needed for a variable named like a reserved word and for names that are not
identifier-shaped.

### Part 2: contextual keywords

These ten words stop being reserved:

```
as constraint exception external mutable of open private rec when
```

The scanner returns each as an identifier, and the parser recognises it as a
keyword in the position where the grammar uses it. Everywhere else it is a
name like any other: a variable, a parameter, a type name, a field, a label.
ReScript already has such words: `async`, `catch`, `finally`, `nonrec` and
`unpack`.

The rule that keeps existing code safe: **in its position, the word is a
keyword whenever today's parser would accept what follows it.** Only when the
next token rules the keyword out is the word read as a name. That takes at
most one token of lookahead.

| Word | Keyword position | Keyword | Name |
|---|---|---|---|
| `of` | after the pattern of a `for` header; after `module type` | always | |
| `when` | after the pattern of a `switch` case | always | |
| `as` | after a pattern or a `~label` | always | |
| `as` | after a type | when `'` follows: `t as 'a` | otherwise |
| `constraint` | after a type declaration | when `'` follows: `constraint 'a = int` | otherwise |
| `mutable` | start of a field in a record type | unless `:`, `?`, `,` or `}` follows: `{mutable x: int}` | `{mutable: bool}`, `{mutable mutable: bool}` |
| `private` | after the `=` of a type declaration or of `with type t =` | when the next token can start a type or a representation: `private A`, `private {...}`, `private int` | otherwise |
| `private` | after the second `=` of a type declaration; after `+=` | always | |
| `rec` | after `let` | unless `=` or `:` follows: `let rec f = ...` | `let rec = 1` |
| `rec` | after `type` | when a name follows: `type rec t = ...` | `type rec = int` |
| `rec` | after `module` | always | |
| `open` | start of a structure, signature or block item | when a module name or `!` follows: `open Belt`, `open! Belt` | `open(file)`, `open->close` |
| `external` | start of a structure or signature item | when a name follows: `external f: ...` | `external.contents`, `external(x)` |
| `exception` | start of a structure, signature or block item | when an uppercase name follows: `exception Foo` | `exception->Console.error` |
| `exception` | start of a pattern | when a pattern follows, other than `as`, `when` or `of`: `\| exception Not_found`, `\| exception e` | `\| exception => ...`, `(exception) => ...` |

This part has not been prototyped. The table comes from reading every match
site of the ten tokens in `res_core.ml` and from running the forms in the
"Keyword" column through ReScript 12.3.1 (`for ... of` is new in 13 and was
read from the parser only).

Why one token is enough:

- **After a pattern or a label, nothing but a keyword can come.** Patterns and
  labels are never followed directly by a name, so `of`, `when` and `as`
  there need no lookahead: `for of of items`, `| when when when > 0 => when`
  and `(~as as as)` all have one reading.
- **At the start of an item, the token after the keyword cannot follow a
  variable.** `open`, `external` and `exception` are followed by a name. An
  expression that starts with a variable continues with an operator, `(`, `.`
  or `->`, never with another name.
- **`let rec`** binds a pattern, and a pattern is followed by `=` or `:`. So
  `rec` followed by `=` or `:` is the pattern itself.
- **After a type**, `as` and `constraint` are followed by `'`, which cannot
  start an expression or a declaration.
- **In a pattern**, `exception` is followed by another pattern, and a variable
  pattern is not. `as`, `when` and `of` directly after `exception` are read as
  those keywords and not as a pattern, so `| exception when ready => ...` and
  `for exception of errors` work with a variable named `exception`.

Consequences of "the keyword wins":

1. `open`, `external` or `exception` as a statement of its own, followed by a
   line that fits the declaration (a name, or `!` after `open`), is read as
   the declaration. Such a statement has no effect, so no useful program is
   written that way. Likewise, an alias to a type named `private`
   (`type t = private`) is read as the keyword when the next line starts with
   a token that can start a type, such as `@`, `module` or a name. This case
   exists only if the ten words are allowed as type names; see "Open
   questions".
2. All forms that span a line break keep parsing as they do today: `open` and
   `Belt` on separate lines, `type t = private` followed by `| A` on the next
   line (which is what the formatter prints for a long variant), and
   `constraint 'a = int` on its own line.
3. An escaped name is the same token as the bare word, as `\"async"` is
   today (12.3.1 reformats `\"async" (x) => x` to `async x => x`). A program
   that parses today can therefore only parse differently if it uses one of
   the ten words as an escaped name, directly in one of the positions above,
   followed by a token that fits the keyword. Example: a bare statement
   `\"open"` followed by a line starting with a module name.

The backend needs no change. ReScript 12.3.1 already compiles all ten as
escaped variable names; `private` is a reserved word in JavaScript strict mode
and is emitted as `$$private`.

#### The words that stay reserved

JavaScript does not let a reserved word name a variable or be used in a
shorthand (checked in Node 24):

```js
let o = {class: 1}; o.class   // ok
let {class: cls} = o          // ok
let class = 1                 // SyntaxError
let o = {class}               // SyntaxError
let {class} = o               // SyntaxError
```

`const {type} = action` is valid JavaScript because `type` is not reserved
there, not because a reserved word can be punned. Of ReScript's 28 words, 14
are never reserved in JavaScript: nine of the ten above (`private` is reserved
in strict mode) and `and`, `assert`, `include`, `module`, `type`. Where
JavaScript and TypeScript use `as`, `of`, `type` and `module` as keywords,
they are contextual, as proposed here.

The remaining 18 cannot follow the same rule, or are left for later:

| Words | Why |
|---|---|
| `module`, `include`, `assert`, `await`, `if`, `switch`, `while`, `for`, `try` | `module(M)`, `include(M)`, `assert(x)`, `await(x)` and `if(x) {...}` are valid today and look exactly like a call |
| `and` | `let a = b` followed by `and(c)` is a call, or the start of `and (c, d) = ...`; bounded lookahead cannot tell |
| `break`, `continue`, `true`, `false` | the bare word is itself the statement or the literal |
| `let`, `else`, `in` | reserved in JavaScript as well |
| `type` | possible, see below |

**`type` is a follow-up.** From reading the parser, it fits the same rule as
`open`: at the start of an item it is always followed by a name (`type t`,
`type rec t`, `type M.t +=`), and in a parameter list by a name
(`(type a, x: a) => ...`); after `module`, `with` and `and` it is always the
keyword. It is kept out of this RFC because it is the keyword with the most
positions (14 match sites in `res_core.ml`, against one to five for each of
the ten), so it gets its own PR and review. Once it is contextual, `{type}`,
`(~type)` and `<input type />` work without any change to the rules of Part 1:
their errors apply only to words that are still reserved.

## Why Part 1 is unambiguous

Part 2 gives its reasons next to its table. This section covers the positions
of Part 1.

The parser is recursive descent and always knows which production it is in.
Each position is entered on a token that is not a keyword (`.`, `~`, `#`, `<`,
`{`, `,`, a JSX tag name), and inside it a keyword token currently has no
meaning: the parser reports an error. The proposal gives that slot a meaning
without taking one away. Per position:

**After `.`** A field access is the `.` that follows an operand. Nothing but a
field name or a module path can follow it. The legacy uncurried dot (`f(. x)`,
`(. int) => int`) is a different production: it appears where an argument or
parameter starts, never after an operand, so `f(. true)` is unaffected.

**After `~`** `~` is used for labels only. `~~~` is a separate token.

**JSX props** After the tag name, only prop names, `?`, `{...spread}`, `/` and
`>` can appear.

**After `#`** `#` starts a polymorphic variant tag and nothing else, in
expressions, patterns and types. The variant spread `#...t` and the operator
`#=` do not start with a word.

**JSX tag names** `<` where an operand is expected always starts a JSX
element; `<` as "less than" only follows an operand. So the word after that
`<`, or after the `</` of a closing tag, is a tag name. A lowercase tag is not
a variable: `<switch />` compiles to `ReactDOM.jsx("switch", {})`, as
`<\"switch" />` does today.

**Record patterns and record types** The row or field starts after `{` or `,`.
A keyword cannot start anything else there, apart from the `mutable` modifier
discussed below.

**Record expressions: the one place with a real choice.** `{` in expression
position starts either a record or a block, and a block may start with a
keyword: `{let x = 1; x}`, `{if a {b} else {c}}`, `{switch x {...}}`,
`{true}`, `{await p}`. The proposal decides with one token of lookahead: a
reserved word followed by `:` starts a record. No block item starts that way.
`let`, `module`, `if`, `switch`, `while`, `for`, `try`, `assert` and `await`
are each followed by a pattern, a path or an expression; `true` and `false`
are followed by an operator or the end of the block (`{true ? a : b}` has `?`
after `true`); `break` and `continue` stand alone. The other reserved words
cannot start a block item at all. A type constraint needs parentheses, so
`{true: bool}` is not an expression today. This is the same test the parser
already applies to produce the current error message.

Three details need care:

1. **`mutable`** is a field modifier and, as a contextual keyword, also a
   name. In a record type, `mutable` followed by `:`, `?`, `,` or `}` is a
   field named `mutable`; otherwise it is the modifier. So `{mutable: bool}`,
   `{mutable x: int}` and `{mutable mutable: bool}` all parse.

2. **`let?`** is scanned as a single token when `?` directly follows `let`.
   Where a label or tag is expected, the parser reads it as the name `let`
   followed by `?`. This matters for `type t = {let?: int}` and for
   `x == #let? a : b`.

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

Add `reserved_word : t -> string option`, returning the text of the 18
reserved words. `Token.is_keyword` cannot be reused: it also answers true for
`&&`, `||`, `list{` and `dict{`.

Remove the ten contextual keywords: the constructors `As`, `Constraint`,
`Exception`, `External`, `Mutable`, `Of`, `Open`, `Private`, `Rec` and `When`,
and their entries in `keyword_table`, `is_keyword` and `to_string`. The scanner
then returns `Lident` for them without a change to `res_scanner.ml`.

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
| `parse_field_declaration_region`, `parse_field_declaration` | consume `mutable`, then the same recovery, `keyword_field_in_type` | accept a reserved word followed by `:` or `?`; for `mutable` itself see the table below |
| `parse_parameter` | `parse_lident` after `~` | `parse_label_name`; for a reserved word, require `as` and report the punning error otherwise |
| `parse_argument2` | matches `Lident` after `~` | also match a reserved word; require `=` and report the punning error otherwise |
| `parse_type_parameter`, `parse_es6_arrow_type` | `parse_lident` after `~` | `parse_label_name` |
| `peek_ident`, used by `read_local_jsx_name` and `read_hyphen_chain` | `Lident` or `Uident` | for prop names and for segments after `-`, also a reserved word |
| `parse_jsx_prop` | starts on `Lident` or `?` | also on a reserved word; require `=` and report the punning error otherwise |
| `parse_hash_ident`, and the `Hash` branch of `parse_pattern` | a string, an integer or `parse_ident`, which reports "`type` is a reserved keyword" | accept a reserved word as the tag |
| `read_jsx_tag_name` | starts on `Lident` or `Uident` through `peek_ident`, otherwise "A jsx name must be a lowercase or uppercase name" | a reserved word starts a lowercase tag name; after `M.` it is still rejected |

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

#### Contextual keywords

About 35 match sites in `res_core.ml` change from a token to an identifier
with a guard, the way `Lident "async"` and `Lident "nonrec"` are matched today.
`Parser.peek2` gives the one token of lookahead.

| Word | Functions | Guard |
|---|---|---|
| `of` | `parse_for_rest`, `parse_module_type_of` | none |
| `when` | `parse_pattern_guard`, `parse_payload` | none |
| `as` | `parse_alias_pattern`, `parse_record_pattern_row`, `parse_parameter` | none |
| `as` | `parse_type_alias` | next is `'` |
| `constraint` | `parse_type_constraint` | next is `'` |
| `mutable` | `parse_field_declaration`, `parse_field_declaration_region` | next is not `:`, `?`, `,` or `}` |
| `private` | `parse_type_equation_and_representation`, `parse_with_constraint` | next starts a type or a representation |
| `private` | `parse_type_representation`, `parse_type_extension` | none |
| `rec` | `parse_let_bindings` | next is not `=` or `:` |
| `rec` | `parse_type_definition_or_extension` | next is a name |
| `rec` | `parse_maybe_rec_module_binding`, `parse_signature_item_region`, `parse_rec_module_spec` | none |
| `open` | `parse_structure_item_region`, `parse_signature_item_region`, `parse_expr_block_item`, `parse_braced_or_record_expr` | next is `Uident` or `!` |
| `external` | `parse_structure_item_region`, `parse_signature_item_region` | next is a name |
| `exception` | `parse_structure_item_region`, `parse_signature_item_region`, `parse_expr_block_item`, `parse_braced_or_record_expr` | next is `Uident` |
| `exception` | `parse_pattern` | next starts a pattern and is not `as`, `when` or `of` |

`parse_braced_or_record_expr` is in the list because `{open Belt; ...}` and
`{exception Foo; ...}` are blocks: the two guards are tested before its
existing branch for identifiers, next to the one for `async`.

### `res_grammar.ml`

The predicates that gate list parsing get the reserved words:
`is_pattern_record_item_start`, `is_record_decl_start` and
`is_jsx_attribute_start`. `is_record_row_start` and `is_field_decl_start` have
them already, for today's error recovery. `#` and `<` already start an
expression, a pattern and a type where they need to.

For the contextual keywords, `is_signature_item_start` and the
`TypeConstraint` case of the list predicates name the identifier instead of
the removed token. The other predicates accept `Lident` already.

## Printer changes

`res_printer.ml` escapes any name that is a keyword: `print_ident_like` prints
`type` as `\"type"`. It gains a label mode that prints a reserved word bare,
used where labels are printed: field declarations, record expression and
pattern rows, field access and update, argument labels in definitions, calls
and types, and JSX prop names.

`print_poly_var_ident` prints `#"type"` today and prints `#type` instead; tags
that are not identifier-shaped keep their quotes (`#"ease-in"`). Lowercase JSX
tag names are printed bare as well.

A punned row, argument or prop keeps its escape, because the pun names a
variable: `{\"type": \"type", name}` is printed as `{\"type", name}` today and
stays that way.

The ten contextual keywords need no printer code. `print_ident_like` decides
with `Token.is_keyword_txt`, which no longer knows them, so they print bare in
every position, bindings and shorthands included.

`res_outcome_printer.ml`, which prints types in error messages, hovers and
generated interfaces, gets the same treatment for record fields and labels.

The formatter therefore rewrites `{\"type": x}` to `{type: x}`, `#"type"` to
`#type`, `<\"switch" />` to `<switch />` and `let \"open" = 1` to
`let open = 1`. Parsing the printed form gives the same AST.

## What does not change

- **AST and PPX.** A field named `type` is `Lident "type"`, and a variable
  named `open` is `Ppat_var "open"`: the same nodes `\"type"` and `\"open"`
  produce today. PPXs see nothing new.
- **Type checker and generated JavaScript.** See the example under Motivation.
- **`.cmi`, `.cmt` and build artifacts.**
- **`@as`.** Still needed for runtime names that are not identifier-shaped
  (`@as("aria-label")`) and for renaming for other reasons.
- **`@deriving(accessors)`.** It generates a function named after each field.
  For a field named `type` that function can only be called as `\"type"`,
  as is already the case for escaped field names.

## Compatibility and migration

Part 1 is additive: every form it accepts is a syntax error today. `type_`
with `@as("type")` keeps compiling, and so does `\"type"`. Nothing has to
migrate.

Part 2 keeps every program that uses the ten words as keywords parsing as it
does today. The one way an existing program can parse differently is
consequence 3 of Part 2: an escaped name such as `\"open"` placed directly in
a keyword position. Syntax error messages that name one of the ten words as a
reserved keyword change.

Code that uses the new syntax does not parse with older compilers, and the
formatter of a new compiler rewrites escaped labels to the bare form. Both
are bounded by a project's pinned compiler version.

Changing `JsxDOM.domProps` from `type_`, `as_`, `open_` and `in_` to the bare
names is a separate, breaking step for the standard library and is not part
of this RFC.

## Tooling

- **Syntax highlighting.** The TextMate grammar in `rescript-vscode` and
  `tree-sitter-rescript` treat these words as keywords everywhere. Both need a
  rule for the label positions and for the contextual keywords; until then
  `type` in `{type: x}` and `open` in `let open = 1` are coloured as keywords,
  which is cosmetic.
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
- **JSX**: a tag name or attribute name may be any identifier-shaped word.
  `<switch>`, `<if />`, `<input type="a" class="b" for="c" in="d" />` and
  `<div data-type="a" />` all parse in TypeScript.
- **Contextual keywords in JavaScript and TypeScript**: `as`, `of`, `async`,
  `from`, `get` and `set` are keywords in one position and identifiers
  elsewhere (`for (of of [as]) {}` is valid JavaScript). TypeScript adds
  `type`, `module`, `namespace`, `declare` and `readonly` the same way:
  `let type = 1` and `{type}` are valid TypeScript.
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
- **Un-reserve every keyword.** Not possible for most of the remaining 18;
  see "The words that stay reserved".
- **Un-reserve none**, and keep this RFC to labels. Then `{open}`, `(~as)` and
  `let {private} = options` stay errors although nothing in the grammar needs
  them to be.
- **Field access only.** Smallest change, but a field that can be read and not
  declared or constructed does not remove the workaround.

## Drawbacks

- The same word is a keyword in one place and a name in another, which is
  harder to highlight with regular expressions.
- Punning does not work for the 18 words that stay reserved. JavaScript has
  the same asymmetry for its own reserved words.
- A misplaced contextual keyword gets a less specific error. `open belt`
  (a lowercase module name) is reported today as a broken `open`; it becomes
  the variable `open` followed by an unexpected name.
- There are two kinds of keyword to explain: 18 that are names in label
  positions only, and the contextual ones that are names everywhere.
- Postfix syntax of the form `expr.keyword` (such as Rust's `.await`) can no
  longer be added later.

## Scope

In scope:

- Reserved words as record field names, argument labels and JSX prop names.
- Reserved words as polymorphic variant tags and lowercase JSX tag names.
- `true` and `false` in all of these positions, as in JavaScript.
- The ten words that can be made contextual with at most one token of
  lookahead.

Out of scope:

- `type` as a contextual keyword: a follow-up.
- The words that cannot be made contextual (see "The words that stay
  reserved").
- Renaming the `type_`, `as_`, `open_` and `in_` props of `JsxDOM`.

## Open questions

1. **Contextual keywords as type names.** Because the scanner returns an
   identifier, `type open = int` and `type t = {mutable}` (a field `mutable`
   of type `mutable`) parse as well. Accept that, or reject the ten words as
   type names in the parser? Rejecting them removes the `private` case in
   consequence 1 of Part 2 and the name reading of `type rec = int`, but makes
   `type \"open" = int`, which compiles today, an error.

## Implementation plan

1. Labels, variant tags and JSX names: parser, printer and outcome printer,
   with syntax tests for every row of the "Positions" and "What stays an
   error" tables, round-trip tests through the formatter, and updated
   snapshots for the existing keyword-field error tests.
2. The ten contextual keywords, as a second PR: one syntax test per row of the
   Part 2 table for the keyword reading and one for the name reading, and the
   full syntax test suite as the check that no existing source parses
   differently.
3. `type` as a contextual keyword, as a follow-up PR.
4. Editor completion and the two highlighting grammars.
5. Documentation.
6. Separately: decide on the `JsxDOM` rename.
