# N-ary Port Spec: upstream semantic changes since `0a51c27b7`

All references are to `upstream/master` at `fe15b978f1d950c4b55fd2470204ad6bb5f6fe9f`.
This document is the implementation brief for porting upstream's n-ary function/arrow
semantics into `compiler-rust`. Produced by review agent bks-b60530c2.

## 1. Unification, equality, inclusion, and coercion

### 1.1 `Tarrow` is structurally n-ary; arity is the parameter-list length

Shape: `Tarrow (params, ret)`. No separate arity field, no commutability cell.
Every strict compatibility operation compares `List.length params`, then pairs parameters positionally.

#### Speculative compatibility (`mcomp`) — ctype.ml:1785-1796

```ocaml
| Tarrow (params1, ret1), Tarrow (params2, ret2)
  when List.length params1 = List.length params2
       && List.for_all2
            (fun (a1 : Types.arg) (a2 : Types.arg) ->
              Asttypes.same_arg_label a1.lbl a2.lbl
              || not (is_optional a1.lbl || is_optional a2.lbl))
            params1 params2 ->
  List.iter2 (fun a1 a2 -> mcomp type_pairs env a1.typ a2.typ) params1 params2;
  mcomp type_pairs env ret1 ret2
```

- parameter counts must match;
- labels may differ only when **both labels are non-optional**;
- parameter types compared positionally, then return types.

#### Actual unification (`unify3`) — ctype.ml:2204-2215

```ocaml
| Tarrow (params1, ret1), Tarrow (params2, ret2)
  when List.length params1 = List.length params2
       && List.for_all2
            (fun (a1 : Types.arg) (a2 : Types.arg) ->
              Asttypes.same_arg_label a1.lbl a2.lbl
              || !umode = Pattern
                 && not (is_optional a1.lbl || is_optional a2.lbl))
            params1 params2 ->
  List.iter2 (fun a1 a2 -> unify env a1.typ a2.typ) params1 params2;
  unify env ret1 ret2
```

Guard semantics:
- counts must match always;
- in `Expression` mode every positional label must satisfy `same_arg_label`;
- in `Pattern` mode mismatched labels tolerated only if neither side is optional;
- optional-vs-nonoptional and differently named optional labels still fail.

No post-unification commutable-state mutation exists anymore.

#### Inclusion / moregeneral — ctype.ml:2754-2764

```ocaml
| Tarrow (params1, ret1), Tarrow (params2, ret2)
  when List.length params1 = List.length params2
       && List.for_all2 (fun a1 a2 -> Asttypes.same_arg_label a1.lbl a2.lbl) params1 params2 ->
  List.iter2 (fun a1 a2 -> moregen inst_nongen type_pairs env a1.typ a2.typ) params1 params2;
  moregen inst_nongen type_pairs env ret1 ret2
```

Unlike mcomp/pattern unification this requires exact positional labels.

#### Type equality — ctype.ml:3031-3041

Same guard as moregen (`same_arg_label` pairwise), then `eqtype` per param + ret.

#### Subtyping/coercion — ctype.ml:3446-3458

```ocaml
| Tarrow (params1, ret1), Tarrow (params2, ret2)
  when List.length params1 = List.length params2
       && List.for_all2 (fun a1 a2 -> Asttypes.same_arg_label a1.lbl a2.lbl) params1 params2 ->
  let cstrs =
    List.fold_left2
      (fun cstrs (a1 : Types.arg) (a2 : Types.arg) ->
        subtype_rec env ((a2.typ, a1.typ) :: trace) a2.typ a1.typ cstrs)
      cstrs params1 params2
  in
  subtype_rec env ((ret1, ret2) :: trace) ret1 ret2 cstrs
```

Parameters contravariant (`a2 <: a1`), returns covariant, equal count, exact labels.
This is the structural equivalent of 8fafaf916. A nested `int => int => int` and an
n-ary `(int, int) => int` can NOT pass inclusion/equality/coercion.

### 1.2 Inclusion diagnostics expose nested arity mismatch — includemod.ml:496-529

Recursively expands/reprs both types, cycle-checks physical pairs, compares n-ary counts,
descends only through equal-label arrows; prints "implementation contains a function taking
%s where the interface expects one taking %s" (531-543), used for Value_descriptions (549-554).

### 1.3 Arrow filtering is exact-arity — ctype.ml:2643-2660 `filter_arrow_n`

```ocaml
let filter_arrow_n ~env t (labels : arg_label list) =
  ...
  | Tvar _ -> let params = List.map (fun l -> {lbl = l; typ = newvar2 lv}) labels in
    ... link_type t (newty2 lv (Tarrow (params, t2)));
  | Tarrow (params, ret)
    when List.length params = List.length labels
         && List.for_all2 (fun l p -> Asttypes.same_arg_label l p.lbl) labels params -> ...
  | _ -> raise (Unify [])
```

Do NOT peel one arrow at a time in the Rust port.

### 1.4 Labeled arguments any-order at call sites — d96662e62

Removed legacy commutable flag and `Incoherent_label_order`. Call typing always scans
declared parameter order using label extraction from remaining syntax arguments
(typecore.ml:4089-4100; see §2). **Call-site labels commute; function types do not.**

## 2. Application typing and optional tails (typecore.ml:4030-4213)

The acceptance of `Int.toString(x)` as `string` when its type is
`int -> (~radix: int=?) -> string` is application elaboration, NOT arrow-unification exception.

1. Total call of unknown function commits the variable to one n-ary arrow matching
   call-site count/labels (4049-4069):
```ocaml
| Tvar _ when total_app ->
  let params = List.map (fun (l1, _) -> {Types.lbl = l1; typ = newvar ()}) sargs in
  let ty_ret = newvar () in ... unify env ty_fun (newty (Tarrow (params, ty_ret)))
```
2. For known `Tarrow (params, ty_ret)`: iterate parameters in DECLARED order, extracting
   matching source arguments by label (4087-4100).
3. Missing optional parameter auto-materialized as `None` when syntax denotes total
   application (`not partial`) or an unlabeled argument remains (4134-4146):
```ocaml
| None ->
  if optional && (total_app || label_assoc Nolabel !remaining) then (
    ignored := (l, ty, lv) :: !ignored;
    rev_args := (l, Some (fun () -> option_none (instance env ty) Location.none)) :: !rev_args)
  else (
    omitted := {Types.lbl = l; typ = ty} :: !omitted;
    if !remaining <> [] then rev_args := (l, None) :: !rev_args)
```
   So normal `Int.toString(x)` has total_app=true; omitted `~radix?` becomes typed `None`;
   result is `string`.
4. Explicit partial application has total_app=false; missing params accumulate in `omitted`;
   result type remains an arrow over exactly those omitted params (4191-4200):
```ocaml
let provided = List.length !ignored + nargs in
let newarity = arity - provided in
let fully_applied = newarity <= 0 in
if total_app && not fully_applied then raise ...;
let ret_t =
  if fully_applied && !omitted = [] then instance env ty_ret
  else instance env (newty2 lv (Tarrow (List.rev !omitted, ty_ret)))
```
5. Typed argument thunks forced in PARAMETER order, not source order (4183-4190).
6. Missing nonoptional param in a total call → arity mismatch error (4194-4195).

## 3. Lambda/backend semantics

### 3.1 Function definitions are direct multi-parameter lambdas

36b14d6c1 removed `Pjs_fn_make`, `Pjs_fn_make_unit`, `Lam_eta_conversion.unsafe_adjust_to_arity`.

translcore.ml:615-642 lowers typed function directly:
```ocaml
| Texp_function {params = fparams; body; async} ->
  let params, lbody, return_unit = transl_function e.exp_loc fparams body in
  let one_unit_arg = match (fparams, (Ctype.expand_head e.exp_env e.exp_type).desc) with
    | [{fp_pat}], Tarrow ([{lbl = Nolabel; typ}], _)
      when Typedtree.pat_bound_idents fp_pat = [] -> ... unit ...
    | _ -> false
  in ... Lfunction {params; body = lbody; attr; loc}
```
No wrapper primitive. lam_convert.ml:418-430 converts `Lfunction` directly with
`arity = List.length params`. lam_compile.ml:1975-2002 emits `E.ocaml_fun params ~return_unit ~async ~one_unit_arg`.
Recursive functions same model (lam_compile.ml:390-451), params=[] for one_unit_arg.

### 3.2 function_param lowering

typecore.ml:3799-3804 creates `{fp_lbl = p.p_lbl; fp_param = name_pattern "param" [case]; fp_pat = pat; fp_partial = partial}`.
translcore.ml:1005-1020 lowers recursively:
```ocaml
| [{fp_param; fp_pat; fp_partial}] ->
  ([fp_param], Matching.for_function loc None (Lvar fp_param) [(fp_pat, transl_exp body)] fp_partial,
   is_base_type body.exp_env body.exp_type Predef.path_unit)
| {fp_param; fp_pat; fp_partial} :: rest ->
  let lparams, lbody, return_unit = transl_function loc rest body in
  (fp_param :: lparams, Matching.for_function loc None (Lvar fp_param) [(fp_pat, lbody)] fp_partial, return_unit)
```
Old `Parmatch.inactive` branch that split active patterns into nested curried Lfunctions is GONE.
Always produce one n-ary lambda.

### 3.3 Applications and partial applications

Ordinary applications: one `Lapply` with all args (translcore.ml:913-924);
lam_convert.ml:405-417 converts with ap_status=App_uncurry. Omitted args = None slots;
generic transl_apply eta-expands around such slots protecting effectful parts (926-962).
Explicit partial applications use known function arity (715-732), build ONE wrapper lambda
with missing-slot IDs plus trailing extra IDs (964-997):
```ocaml
let extra_arity = arity - List.length sargs in
...
Lfunction { params = List.rev_append !none_ids extra_ids;
            body = Lapply {ap_func = lam; ap_args = args @ extra_args; ...}; ... }
```
Remaining primitives: Pjs_fn_method (%unsafe_to_method only), Pjs_apply/Pjs_runtime_apply,
Pfn_arity. Pcurry_apply n maps to Pjs_apply (lam_convert.ml:314).

### 3.4 Inlined argument evaluation order (124bc4bdd)

lam_beta_reduce.ml:66-77 and 105-119: final wrapper uses `fold_left` (not fold_right) over
reverse-order bindings so first source argument's strict let is outermost:
```ocaml
Ext_list.fold_left rest_bindings new_body (fun l (param, arg) ->
  ... Lam_util.refine_let ~kind:Strict param arg l)
```

## 4. Parsetree/type-expression/function/pattern shapes

### 4.1 Arrow types
parsetree.ml:76-85: `and arg = {attrs; lbl; typ}` ; `Ptyp_arrow of {params: arg list; ret}`.
Invariant params <> []. typetexp.ml:307-337 translates all params, wraps optional types in
option, constructs ONE Types.Tarrow(params, ret), emits one Ttyp_arrow(params, ret).

### 4.2 Function expressions
parsetree.ml:235-251: `Pexp_fun of {newtypes: (string loc * attributes) list; params: fun_param list; body; async}`.
parsetree.ml:409-414: `fun_param = {p_attrs; p_lbl; p_default: expression option; p_pat}`.
typecore.ml:2468-2489 peels newtypes into nested type scopes, calls n-ary type_function once.
type_function at typecore.ml:3529-3823: desugars defaults per param (defaults see only
preceding params, 3531-3539/3721-3739), commits expected type to one arrow of same
labels/count, types param patterns left-to-right, body once, emits ONE Texp_function.

### 4.3 Record-rest patterns
parsetree.ml:164-168: `record_pat_rest = {rest_loc; rest_name: string loc; rest_type: core_type option}`.
parsetree.ml:193-200: `Ppat_record of pattern record_element list * closed_flag * record_pat_rest option`.
typecore.ml:1498-1588 consumes it: rest makes missing-field checking Open (1553-1561),
Typecore_record_rest.type_record_pat_rest types/validates (1563-1578),
stores Tpat_record(..., closed, typed_rest) (1580-1587).
typecore_record_rest.ml:121-246 checker constraints:
- requires explicit rest record type (rest_type=None → Requires_type_annotation, 126-132)
- rest type must be non-private boxed record (145-164)
- source may not be unboxed or have mutable fields (84-92)
- explicit/rest fields must partition source fields; duplicate only allowed for optional explicit matching w/ warning (187-214)
- field source types and runtime names must match (215-237)
Typed shape typedtree.ml:38-43,59-62:
`record_pat_rest = {rest_ident; rest_name; rest_type; excluded_runtime_labels}`.
matching.ml:538-575 binds with `Precord_rest excluded_runtime_labels`.
Backend: lam_compile_primitive.ml:617-626; JS IR `Record_rest`; js_dump.ml:524-542 +
js_pass_record_rest.ml desugars to object destructuring.

## 5. Other JS-output/diagnostic parity changes

- **Large record mutation consolidation (767e553f1)** — lam_compile.ml:1919-1970 recognizes
  `let copy = Pduprecord init` + sequence of Psetfields on copy ending in copy var; evaluates
  init then overrides in source order emitting `E.obj ~dup:init_val props` (`{...init, field: v}`).
  js_dump.ml:667-691 also recognizes shape in transformed JSX.
- **Record rest (6a38beace)** — chain per §4.3; changes Lambda AND JS snapshots.
- **First-class tagged templates (9810ed82e)** — predef abstract `taggedTemplate<'param,'output>`
  arity 2 (predef.ml:351-358,393); typecore.ml:2517-2575 requires tag value unify with that
  constructor, string chunks array<string>, interpolations 'param w/ TaggedTemplateValue context,
  yields 'output. Not a function type. translcore.ml:643-660 emits `Ptagged_template [tag; strings; values]`;
  lam_compile_primitive.ml:97-106 emits real JS tagged-template AST. Old @taggedTemplate FFI removed.
- **Abstract Jsx.component (b8fdd38d3)** — runtime contravariant abstract `component<-'props>` +
  `%component_identity` coercion (Jsx.res:18-27); maps to Pidentity (translcore.ml:239);
  nonexpansive when args nonexpansive (typecore.ml:1829-1880); JsxComponent clash context (2513-2515).
- **Avoid boxing Some(React.component) (27147f09a)** — @notUndefined on abstract Jsx.component
  (Jsx.res:23-24) feeds Typeopt.type_cannot_contain_undefined → Blk_some_not_nested (translcore.ml:783-788).
- **Default-argument diagnostics (709f46fa0)** — generated match annotated #optional_arg_default
  recognized as call_context=Function not Switch (typecore.ml:3575-3578, 3760-3770).
- **Warning 56/dict-pattern blowup (c18f4c25d)** — parmatch.ml:2037-2054 replaces dict subpatterns
  with opaque wildcards; during warning-56 refinement rows containing dict patterns filtered (2233-2241).
- **@warning("-102") (4d9336427)** — polymorphic-compare warning moved INTO translcore
  (translcore.ml:447-454, call sites 464/693): warn for poly compare/order/min/max except
  null/undefined eq/neq. Do NOT emit warning 102 in Rust JS lowering.
- **UTF-8 code-frame wrapping (2f97455e0)** — code_frame.ml:39-56: max_width counts Unicode
  scalars preserving byte boundaries (get_utf_8_uchar |> utf_decode_length). Wrap by chars,
  never split UTF-8 bytes.
