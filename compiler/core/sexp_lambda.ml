(* Sexp printer for Lambda IR - used for parity testing between OCaml and Rust compilers *)

open Asttypes

(* Sexp module - simple string-based pretty printing *)
module Sexp = struct
  type t = Atom of string | List of t list

  let atom s = Atom s
  let list l = List l

  let rec to_string_indent indent t =
    let spaces = String.make (indent * 2) ' ' in
    match t with
    | Atom s -> s
    | List [] -> "()"
    | List [Atom s] -> "(" ^ s ^ ")"
    | List [sexpr] -> "(" ^ to_string_indent indent sexpr ^ ")"
    | List items ->
      let inner = String.concat ("\n" ^ spaces ^ "  ")
        (List.map (to_string_indent (indent + 1)) items) in
      "(" ^ inner ^ ")"

  let to_string sexpr = to_string_indent 0 sexpr
end

(* Helper functions *)
let string txt = Sexp.atom ("\"" ^ String.escaped txt ^ "\"")

let opt_string = function
  | None -> Sexp.atom "None"
  | Some s -> Sexp.list [Sexp.atom "Some"; string s]

let opt f = function
  | None -> Sexp.atom "None"
  | Some x -> Sexp.list [Sexp.atom "Some"; f x]

let bool b = Sexp.atom (if b then "true" else "false")

let int32 i = Sexp.atom (Int32.to_string i)

let int i = Sexp.atom (string_of_int i)

let location ~with_locs loc =
  if with_locs then
    Sexp.list [
      Sexp.atom "loc";
      Sexp.atom (string_of_int loc.Location.loc_start.Lexing.pos_lnum);
      Sexp.atom (string_of_int (loc.Location.loc_start.Lexing.pos_cnum - loc.Location.loc_start.Lexing.pos_bol));
      Sexp.atom (string_of_int loc.Location.loc_end.Lexing.pos_lnum);
      Sexp.atom (string_of_int (loc.Location.loc_end.Lexing.pos_cnum - loc.Location.loc_end.Lexing.pos_bol));
    ]
  else
    Sexp.list []

(* Ident printer - name only for determinism *)
let ident id = string (Ident.name id)

(* Direction flag *)
let direction_flag = function
  | Upto -> Sexp.atom "Upto"
  | Downto -> Sexp.atom "Downto"

(* Comparison *)
let comparison (cmp : Lambda.comparison) =
  match cmp with
  | Ceq -> Sexp.atom "Ceq"
  | Cneq -> Sexp.atom "Cneq"
  | Clt -> Sexp.atom "Clt"
  | Cle -> Sexp.atom "Cle"
  | Cgt -> Sexp.atom "Cgt"
  | Cge -> Sexp.atom "Cge"

(* Let kind *)
let let_kind (k : Lambda.let_kind) =
  match k with
  | Alias -> Sexp.atom "Alias"
  | Strict -> Sexp.atom "Strict"
  | StrictOpt -> Sexp.atom "StrictOpt"
  | Variable -> Sexp.atom "Variable"

(* Inline attribute *)
let inline_attribute (attr : Lambda.inline_attribute) =
  match attr with
  | Always_inline -> Sexp.atom "Always_inline"
  | Never_inline -> Sexp.atom "Never_inline"
  | Default_inline -> Sexp.atom "Default_inline"

(* Mutable flag *)
let mutable_flag_sexp = function
  | Mutable -> Sexp.atom "Mutable"
  | Immutable -> Sexp.atom "Immutable"

(* Semantic variant runtime information. *)
let variant_instance instance =
  Sexp.atom (Variant_runtime.Instance.to_string instance)

let variant_block_type = function
  | Variant_runtime.IntType -> Sexp.atom "IntType"
  | StringType -> Sexp.atom "StringType"
  | FloatType -> Sexp.atom "FloatType"
  | BigintType -> Sexp.atom "BigintType"
  | BooleanType -> Sexp.atom "BooleanType"
  | InstanceType instance ->
    Sexp.list [Sexp.atom "InstanceType"; variant_instance instance]
  | FunctionType -> Sexp.atom "FunctionType"
  | ObjectType -> Sexp.atom "ObjectType"
  | UnknownType -> Sexp.atom "UnknownType"

let variant_tag_type = function
  | Variant_runtime.String value -> Sexp.list [Sexp.atom "String"; string value]
  | Int value -> Sexp.list [Sexp.atom "Int"; int value]
  | Float value -> Sexp.list [Sexp.atom "Float"; string value]
  | BigInt value -> Sexp.list [Sexp.atom "BigInt"; string value]
  | Bool value -> Sexp.list [Sexp.atom "Bool"; bool value]
  | Null -> Sexp.atom "Null"
  | Undefined -> Sexp.atom "Undefined"
  | Untagged block_type ->
    Sexp.list [Sexp.atom "Untagged"; variant_block_type block_type]

let variant_tag ({name; tag_type} : Variant_runtime.tag) =
  Sexp.list
    [
      Sexp.atom "tag";
      string name;
      (match tag_type with
      | None -> Sexp.atom "None"
      | Some tag_type -> Sexp.list [Sexp.atom "Some"; variant_tag_type tag_type]);
    ]

let variant_block_runtime
    ({tag; tag_name; untagged} : Variant_runtime.block_runtime) =
  Sexp.list
    [
      Sexp.atom "runtime";
      variant_tag tag;
      (match tag_name with
      | None -> Sexp.atom "None"
      | Some name -> Sexp.list [Sexp.atom "Some"; string name]);
      bool untagged;
    ]

let variant_constructor_case = function
  | Variant_runtime.Constant tag ->
    Sexp.list [Sexp.atom "Constant"; variant_tag tag]
  | Block {runtime; block_type} ->
    Sexp.list
      [
        Sexp.atom "Block";
        variant_block_runtime runtime;
        (match block_type with
        | None -> Sexp.atom "None"
        | Some block_type ->
          Sexp.list [Sexp.atom "Some"; variant_block_type block_type]);
      ]

let variant_matching_facts
    ({
       tag_name;
       block_types;
       literal_tags;
       has_null;
       has_undefined;
       has_other_literal;
     } : Variant_runtime.matching_facts) =
  Sexp.list
    [
      Sexp.atom "matching_facts";
      (match tag_name with
      | None -> Sexp.atom "None"
      | Some name -> Sexp.list [Sexp.atom "Some"; string name]);
      Sexp.list (List.map variant_block_type block_types);
      Sexp.list (List.map variant_tag_type literal_tags);
      bool has_null;
      bool has_undefined;
      bool has_other_literal;
    ]

(* Tag info *)
let tag_info (info : Lambda.tag_info) =
  match info with
  | Blk_constructor {name; num_nonconst; runtime} ->
    Sexp.list
      [
        Sexp.atom "Blk_constructor";
        string name;
        int num_nonconst;
        variant_block_runtime runtime;
      ]
  | Blk_tuple -> Sexp.atom "Blk_tuple"
  | Blk_poly_var -> Sexp.atom "Blk_poly_var"
  | Blk_record {fields; mutable_flag} ->
    Sexp.list [
      Sexp.atom "Blk_record";
      Sexp.list (List.map (fun (name, _) -> string name) (Array.to_list fields));
      mutable_flag_sexp mutable_flag;
    ]
  | Blk_record_inlined
      {name; num_nonconst; fields; mutable_flag; runtime} ->
    Sexp.list
      [
        Sexp.atom "Blk_record_inlined";
        string name;
        int num_nonconst;
        variant_block_runtime runtime;
        Sexp.list (List.map (fun (name, _) -> string name) (Array.to_list fields));
        mutable_flag_sexp mutable_flag;
      ]
  | Blk_module fields ->
    Sexp.list (Sexp.atom "Blk_module" :: List.map string fields)
  | Blk_module_export _ ->
    Sexp.atom "Blk_module_export"
  | Blk_extension -> Sexp.atom "Blk_extension"
  | Blk_record_ext {fields; mutable_flag} ->
    Sexp.list [
      Sexp.atom "Blk_record_ext";
      Sexp.list (List.map string (Array.to_list fields));
      mutable_flag_sexp mutable_flag;
    ]

(* Field debug info *)
let field_dbg_info (info : Lambda.field_dbg_info) =
  match info with
  | Fld_record {name} ->
    Sexp.list [Sexp.atom "Fld_record"; string name]
  | Fld_module {name} -> Sexp.list [Sexp.atom "Fld_module"; string name]
  | Fld_record_inline {name} -> Sexp.list [Sexp.atom "Fld_record_inline"; string name]
  | Fld_record_extension {name} -> Sexp.list [Sexp.atom "Fld_record_extension"; string name]
  | Fld_tuple -> Sexp.atom "Fld_tuple"
  | Fld_poly_var_tag -> Sexp.atom "Fld_poly_var_tag"
  | Fld_poly_var_content -> Sexp.atom "Fld_poly_var_content"
  | Fld_extension -> Sexp.atom "Fld_extension"
  | Fld_variant -> Sexp.atom "Fld_variant"
  | Fld_cons -> Sexp.atom "Fld_cons"

(* Set field debug info *)
let set_field_dbg_info (info : Lambda.set_field_dbg_info) =
  match info with
  | Fld_record_set s -> Sexp.list [Sexp.atom "Fld_record_set"; string s]
  | Fld_record_inline_set s -> Sexp.list [Sexp.atom "Fld_record_inline_set"; string s]
  | Fld_record_extension_set s -> Sexp.list [Sexp.atom "Fld_record_extension_set"; string s]

(* Constant *)
let rec constant (c : Lambda.structured_constant) =
  match c with
  | Const_js_null -> Sexp.atom "Const_js_null"
  | Const_js_undefined {is_unit} ->
    Sexp.list [Sexp.atom "Const_js_undefined"; bool is_unit]
  | Const_js_true -> Sexp.atom "Const_js_true"
  | Const_js_false -> Sexp.atom "Const_js_false"
  | Const_int i -> Sexp.list [Sexp.atom "Const_int"; int32 i]
  | Const_polyvar s -> Sexp.list [Sexp.atom "Const_polyvar"; string s]
  | Const_assertfalse -> Sexp.atom "Const_assertfalse"
  | Const_constructor tag ->
    Sexp.list [Sexp.atom "Const_constructor"; variant_tag tag]
  | Const_char c -> Sexp.list [Sexp.atom "Const_char"; int c]
  | Const_string s -> Sexp.list [Sexp.atom "Const_string"; string s]
  | Const_float f -> Sexp.list [Sexp.atom "Const_float"; string f]
  | Const_bigint (sign, s) ->
    Sexp.list [Sexp.atom "Const_bigint"; bool sign; string s]
  | Const_block (info, elements) ->
    Sexp.list
      [
        Sexp.atom "Const_block";
        tag_info info;
        Sexp.list (List.map constant elements);
      ]
  | Const_some c -> Sexp.list [Sexp.atom "Const_some"; constant c]
  | Const_module_alias -> Sexp.atom "Const_module_alias"

(* Primitive *)
let primitive ~with_locs (prim : Lambda.primitive) =
  match prim with
  | Pcreate_extension s -> Sexp.list [Sexp.atom "Pcreate_extension"; string s]
  | Pinit_mod -> Sexp.atom "Pinit_mod"
  | Pupdate_mod -> Sexp.atom "Pupdate_mod"
  | Pjs_object_get name -> Sexp.list [Sexp.atom "Pjs_object_get"; string name]
  | Pjs_object_set name -> Sexp.list [Sexp.atom "Pjs_object_set"; string name]
  | Pjs_fn_method -> Sexp.atom "Pjs_fn_method"
  | Pdebugger -> Sexp.atom "Pdebugger"
  | Praw_js_code {code; code_info = Exp _} ->
    Sexp.list [Sexp.atom "Praw_js_code_exp"; string code]
  | Praw_js_code {code; code_info = Stmt _} ->
    Sexp.list [Sexp.atom "Praw_js_code_stmt"; string code]
  | Ptypeof -> Sexp.atom "Ptypeof"
  | Pnull_to_opt -> Sexp.atom "Pnull_to_opt"
  | Pnull_undefined_to_opt -> Sexp.atom "Pnull_undefined_to_opt"
  | Pis_null -> Sexp.atom "Pis_null"
  | Pis_not_none -> Sexp.atom "Pis_not_none"
  | Psome -> Sexp.atom "Psome"
  | Psome_not_nest -> Sexp.atom "Psome_not_nest"
  | Pval_from_option -> Sexp.atom "Pval_from_option"
  | Pval_from_option_not_nest -> Sexp.atom "Pval_from_option_not_nest"
  | Pis_undefined -> Sexp.atom "Pis_undefined"
  | Pis_null_undefined -> Sexp.atom "Pis_null_undefined"
  | Pimport src ->
    Sexp.list [Sexp.atom "Pimport"; string (Ffi_debug.import_source src)]
  | Pmakeblock info ->
    Sexp.list
      [
        Sexp.atom "Pmakeblock";
        tag_info info;
        mutable_flag_sexp (Lambda.mutable_flag_of_tag_info info);
      ]
  | Pfield (n, info) ->
    Sexp.list [Sexp.atom "Pfield"; int n; field_dbg_info info]
  | Psetfield (n, info) ->
    Sexp.list [Sexp.atom "Psetfield"; int n; set_field_dbg_info info]
  | Pduprecord -> Sexp.atom "Pduprecord"
  | Pjs_call {prim_name; arg_types = _; ffi = _; transformed_jsx} ->
    Sexp.list [
      Sexp.atom "Pjs_call";
      string prim_name;
      (* Skip arg_types and ffi for brevity *)
      bool transformed_jsx;
    ]
  | Pjs_object_create _ -> Sexp.atom "Pjs_object_create"
  | Praise -> Sexp.atom "Praise"
  | Pobjcomp cmp -> Sexp.list [Sexp.atom "Pobjcomp"; comparison cmp]
  | Pobjorder -> Sexp.atom "Pobjorder"
  | Pobjmin -> Sexp.atom "Pobjmin"
  | Pobjmax -> Sexp.atom "Pobjmax"
  | Pobjtag -> Sexp.atom "Pobjtag"
  | Pobjsize -> Sexp.atom "Pobjsize"
  | Psequand -> Sexp.atom "Psequand"
  | Psequor -> Sexp.atom "Psequor"
  | Pnot -> Sexp.atom "Pnot"
  | Pboolcomp cmp -> Sexp.list [Sexp.atom "Pboolcomp"; comparison cmp]
  | Pboolorder -> Sexp.atom "Pboolorder"
  | Pboolmin -> Sexp.atom "Pboolmin"
  | Pboolmax -> Sexp.atom "Pboolmax"
  | Pnegint -> Sexp.atom "Pnegint"
  | Paddint -> Sexp.atom "Paddint"
  | Pstringadd -> Sexp.atom "Pstringadd"
  | Psubint -> Sexp.atom "Psubint"
  | Pmulint -> Sexp.atom "Pmulint"
  | Pdivint -> Sexp.atom "Pdivint"
  | Pmodint -> Sexp.atom "Pmodint"
  | Ppowint -> Sexp.atom "Ppowint"
  | Pandint -> Sexp.atom "Pandint"
  | Porint -> Sexp.atom "Porint"
  | Pxorint -> Sexp.atom "Pxorint"
  | Pnotint -> Sexp.atom "Pnotint"
  | Plslint -> Sexp.atom "Plslint"
  | Plsrint -> Sexp.atom "Plsrint"
  | Pasrint -> Sexp.atom "Pasrint"
  | Pintcomp cmp -> Sexp.list [Sexp.atom "Pintcomp"; comparison cmp]
  | Pintorder -> Sexp.atom "Pintorder"
  | Pintmin -> Sexp.atom "Pintmin"
  | Pintmax -> Sexp.atom "Pintmax"
  | Pintoffloat -> Sexp.atom "Pintoffloat"
  | Pfloatofint -> Sexp.atom "Pfloatofint"
  | Pnegfloat -> Sexp.atom "Pnegfloat"
  | Paddfloat -> Sexp.atom "Paddfloat"
  | Psubfloat -> Sexp.atom "Psubfloat"
  | Pmulfloat -> Sexp.atom "Pmulfloat"
  | Pdivfloat -> Sexp.atom "Pdivfloat"
  | Pmodfloat -> Sexp.atom "Pmodfloat"
  | Ppowfloat -> Sexp.atom "Ppowfloat"
  | Pfloatcomp cmp -> Sexp.list [Sexp.atom "Pfloatcomp"; comparison cmp]
  | Pfloatorder -> Sexp.atom "Pfloatorder"
  | Pfloatmin -> Sexp.atom "Pfloatmin"
  | Pfloatmax -> Sexp.atom "Pfloatmax"
  | Pnegbigint -> Sexp.atom "Pnegbigint"
  | Paddbigint -> Sexp.atom "Paddbigint"
  | Psubbigint -> Sexp.atom "Psubbigint"
  | Pmulbigint -> Sexp.atom "Pmulbigint"
  | Pdivbigint -> Sexp.atom "Pdivbigint"
  | Pmodbigint -> Sexp.atom "Pmodbigint"
  | Ppowbigint -> Sexp.atom "Ppowbigint"
  | Pandbigint -> Sexp.atom "Pandbigint"
  | Porbigint -> Sexp.atom "Porbigint"
  | Pxorbigint -> Sexp.atom "Pxorbigint"
  | Pnotbigint -> Sexp.atom "Pnotbigint"
  | Plslbigint -> Sexp.atom "Plslbigint"
  | Pasrbigint -> Sexp.atom "Pasrbigint"
  | Pbigintcomp cmp -> Sexp.list [Sexp.atom "Pbigintcomp"; comparison cmp]
  | Pbigintorder -> Sexp.atom "Pbigintorder"
  | Pbigintmin -> Sexp.atom "Pbigintmin"
  | Pbigintmax -> Sexp.atom "Pbigintmax"
  | Pjscomp cmp -> Sexp.list [Sexp.atom "Pjscomp"; comparison cmp]
  | Pstringlength -> Sexp.atom "Pstringlength"
  | Pstringrefu -> Sexp.atom "Pstringrefu"
  | Pstringrefs -> Sexp.atom "Pstringrefs"
  | Pstringcomp cmp -> Sexp.list [Sexp.atom "Pstringcomp"; comparison cmp]
  | Pstringorder -> Sexp.atom "Pstringorder"
  | Pstringmin -> Sexp.atom "Pstringmin"
  | Pstringmax -> Sexp.atom "Pstringmax"
  | Parraylength -> Sexp.atom "Parraylength"
  | Pmakearray -> Sexp.atom "Pmakearray"
  | Pmakelist -> Sexp.atom "Pmakelist"
  | Pmakedict -> Sexp.atom "Pmakedict"
  | Pdict_has -> Sexp.atom "Pdict_has"
  | Parrayrefu -> Sexp.atom "Parrayrefu"
  | Parraysetu -> Sexp.atom "Parraysetu"
  | Parrayrefs -> Sexp.atom "Parrayrefs"
  | Parraysets -> Sexp.atom "Parraysets"
  | Pisint -> Sexp.atom "Pisint"
  | Pis_poly_var_block -> Sexp.atom "Pis_poly_var_block"
  | Pawait -> Sexp.atom "Pawait"
  | Ptagged_template raw_sources ->
    Sexp.list (Sexp.atom "Ptagged_template" :: List.map string raw_sources)
  | Ptemplate segments ->
    Sexp.list
      (Sexp.atom "Ptemplate"
      :: List.map
           (fun segment ->
             Sexp.list
               [
                 string (String_literal.template_source segment);
                 string (String_literal.template_semantic segment);
               ])
           segments)
  | Precord_rest excluded ->
    Sexp.list (Sexp.atom "Precord_rest" :: List.map string excluded)
  | Phash -> Sexp.atom "Phash"
  | Phash_mixint -> Sexp.atom "Phash_mixint"
  | Phash_mixstring -> Sexp.atom "Phash_mixstring"
  | Phash_finalmix -> Sexp.atom "Phash_finalmix"

(* Function attributes *)
let function_attribute (attr : Lambda.function_attribute) =
  Sexp.list [
    Sexp.atom "function_attribute";
    Sexp.list [Sexp.atom "inline"; inline_attribute attr.inline];
    Sexp.list [Sexp.atom "is_a_functor"; bool attr.is_a_functor];
    Sexp.list [Sexp.atom "return_unit"; bool attr.return_unit];
    Sexp.list [Sexp.atom "async"; bool attr.async];
    Sexp.list [Sexp.atom "directive"; opt_string attr.directive];
    Sexp.list [Sexp.atom "one_unit_arg"; bool attr.one_unit_arg];
  ]

(* Lambda *)
let rec lambda ~with_locs (lam : Lambda.t) =
  match lam with
  | Lvar id ->
    Sexp.list [Sexp.atom "Lvar"; ident id]
  | Lglobal_module id -> Sexp.list [Sexp.atom "Lglobal_module"; ident id]
  | Lconst c ->
    Sexp.list [Sexp.atom "Lconst"; constant c]
  | Lapply {ap_func; ap_args; ap_info; ap_transformed_jsx} ->
    Sexp.list [
      Sexp.atom "Lapply";
      lambda ~with_locs ap_func;
      Sexp.list (List.map (lambda ~with_locs) ap_args);
      ap_info_sexp ~with_locs ap_info;
      bool ap_transformed_jsx;
    ]
  | Lfunction {params; body; attr} ->
    Sexp.list [
      Sexp.atom "Lfunction";
      Sexp.list (List.map ident params);
      lambda ~with_locs body;
      function_attribute attr;
    ]
  | Llet (kind, id, arg, body) ->
    Sexp.list [
      Sexp.atom "Llet";
      let_kind kind;
      ident id;
      lambda ~with_locs arg;
      lambda ~with_locs body;
    ]
  | Lletrec (bindings, body) ->
    Sexp.list [
      Sexp.atom "Lletrec";
      Sexp.list (List.map (fun (id, lam) ->
        Sexp.list [ident id; lambda ~with_locs lam]
      ) bindings);
      lambda ~with_locs body;
    ]
  | Lprim {primitive = prim; args; loc} ->
    let loc_sexp = if with_locs then [location ~with_locs loc] else [] in
    Sexp.list ([
      Sexp.atom "Lprim";
      primitive ~with_locs prim;
      Sexp.list (List.map (lambda ~with_locs) args);
    ] @ loc_sexp)
  | Lswitch (arg, sw) ->
    Sexp.list [
      Sexp.atom "Lswitch";
      lambda ~with_locs arg;
      lambda_switch ~with_locs sw;
    ]
  | Lstringswitch (arg, cases, default) ->
    Sexp.list [
      Sexp.atom "Lstringswitch";
      lambda ~with_locs arg;
      Sexp.list (List.map (fun (s, lam) ->
        Sexp.list [string s; lambda ~with_locs lam]
      ) cases);
      opt (lambda ~with_locs) default;
    ]
  | Lstaticraise (id, args) ->
    Sexp.list [
      Sexp.atom "Lstaticraise";
      int id;
      Sexp.list (List.map (lambda ~with_locs) args);
    ]
  | Lstaticcatch (body, (id, params), handler) ->
    Sexp.list [
      Sexp.atom "Lstaticcatch";
      lambda ~with_locs body;
      int id;
      Sexp.list (List.map ident params);
      lambda ~with_locs handler;
    ]
  | Ltrywith (body, exn, handler) ->
    Sexp.list [
      Sexp.atom "Ltrywith";
      lambda ~with_locs body;
      ident exn;
      lambda ~with_locs handler;
    ]
  | Lifthenelse (cond, then_, else_) ->
    Sexp.list [
      Sexp.atom "Lifthenelse";
      lambda ~with_locs cond;
      lambda ~with_locs then_;
      lambda ~with_locs else_;
    ]
  | Lsequence (first, second) ->
    Sexp.list [
      Sexp.atom "Lsequence";
      lambda ~with_locs first;
      lambda ~with_locs second;
    ]
  | Lwhile (cond, body) ->
    Sexp.list [
      Sexp.atom "Lwhile";
      lambda ~with_locs cond;
      lambda ~with_locs body;
    ]
  | Lfor (var, start, end_, dir, body) ->
    Sexp.list [
      Sexp.atom "Lfor";
      ident var;
      lambda ~with_locs start;
      lambda ~with_locs end_;
      direction_flag dir;
      lambda ~with_locs body;
    ]
  | Lassign (var, value) ->
    Sexp.list [
      Sexp.atom "Lassign";
      ident var;
      lambda ~with_locs value;
    ]
  | Lbreak -> Sexp.list [Sexp.atom "Lbreak"]
  | Lcontinue -> Sexp.list [Sexp.atom "Lcontinue"]
  | Lfor_of _ -> Sexp.list [Sexp.atom "Lfor_of"]
  | Lfor_await_of _ -> Sexp.list [Sexp.atom "Lfor_await_of"]

and ap_info_sexp ~with_locs (info : Lambda.ap_info) =
  let loc_sexp = if with_locs then [location ~with_locs info.ap_loc] else [] in
  Sexp.list ([
    Sexp.atom "ap_info";
    inline_attribute info.ap_inlined;
  ] @ loc_sexp)

and switch_key_sexp = function
  | Lambda.Switch_int value -> Sexp.list [Sexp.atom "Switch_int"; int value]
  | Switch_constructor case ->
    Sexp.list [Sexp.atom "Switch_constructor"; variant_constructor_case case]

and switch_dispatch_sexp = function
  | Lambda.Switch_direct -> Sexp.atom "Switch_direct"
  | Switch_variant facts ->
    Sexp.list [Sexp.atom "Switch_variant"; variant_matching_facts facts]

and lambda_switch ~with_locs (sw : Lambda.lambda_switch) =
  Sexp.list
    [
      Sexp.atom "lambda_switch";
      Sexp.list [Sexp.atom "sw_consts_full"; bool sw.sw_consts_full];
      Sexp.list
        [
          Sexp.atom "sw_consts";
          Sexp.list
            (List.map
               (fun (key, lam) ->
                 Sexp.list [switch_key_sexp key; lambda ~with_locs lam])
               sw.sw_consts);
        ];
      Sexp.list [Sexp.atom "sw_blocks_full"; bool sw.sw_blocks_full];
      Sexp.list
        [
          Sexp.atom "sw_blocks";
          Sexp.list
            (List.map
               (fun (key, lam) ->
                 Sexp.list [switch_key_sexp key; lambda ~with_locs lam])
               sw.sw_blocks);
        ];
      Sexp.list
        [Sexp.atom "sw_failaction"; opt (lambda ~with_locs) sw.sw_failaction];
      Sexp.list
        [Sexp.atom "sw_dispatch"; switch_dispatch_sexp sw.sw_dispatch];
    ]

(* Public API *)
let print_lambda ppf lam =
  let sexp = lambda ~with_locs:false lam in
  Format.fprintf ppf "%s" (Sexp.to_string sexp)

let print_lambda_with_locs ppf lam =
  let sexp = lambda ~with_locs:true lam in
  Format.fprintf ppf "%s" (Sexp.to_string sexp)
