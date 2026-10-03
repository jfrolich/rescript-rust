(* Fork-only: a deterministic textual rendering of a digested external, used
   by the sexp parity printers so the Rust compiler can be compared against
   this reference. *)

open External_arg_spec
open External_ffi_types

let list f xs = "[" ^ String.concat ";" (List.map f xs) ^ "]"
let quote s = Printf.sprintf "%S" s
let bool b = if b then "true" else "false"

let delim = function
  | DNone -> "DNone"
  | DStarJ -> "DStarJ"
  | DNoQuotes -> "DNoQuotes"
  | DBackQuotes -> "DBackQuotes"

let pairs xs = list (fun (a, b) -> "(" ^ quote a ^ "," ^ quote b ^ ")") xs

let attr = function
  | Poly_var_string {descr} -> "Poly_var_string" ^ pairs descr
  | Poly_var {descr = None} -> "Poly_var"
  | Poly_var {descr = Some d} -> "Poly_var" ^ pairs d
  | Int xs -> "Int" ^ list (fun (a, i) -> "(" ^ quote a ^ "," ^ string_of_int i ^ ")") xs
  | Arg_cst (Arg_int_lit i) -> "Arg_int_lit(" ^ string_of_int i ^ ")"
  | Arg_cst (Arg_string_lit (s, d)) ->
    "Arg_string_lit(" ^ quote s ^ "," ^ delim d ^ ")"
  | Extern_unit -> "Extern_unit"
  | Nothing -> "Nothing"
  | Ignore -> "Ignore"
  | Unwrap -> "Unwrap"

let label_noname = function
  | Arg_label -> "Arg_label"
  | Arg_empty -> "Arg_empty"
  | Arg_optional -> "Arg_optional"

let label = function
  | Obj_empty -> "Obj_empty"
  | Obj_label {name} -> "Obj_label(" ^ quote name ^ ")"
  | Obj_optional {name; for_sure_no_nested_option} ->
    "Obj_optional(" ^ quote name ^ "," ^ bool for_sure_no_nested_option ^ ")"

let param (p : param) = attr p.arg_type ^ ":" ^ label_noname p.arg_label
let obj_param (p : obj_param) = attr p.obj_arg_type ^ ":" ^ label p.obj_arg_label

let module_name m =
  "{" ^ quote m.bundle ^ ","
  ^ (match m.module_bind_name with
    | Phint_name s -> "Phint_name(" ^ quote s ^ ")"
    | Phint_nothing -> "Phint_nothing")
  ^ ","
  ^ (match m.import_attributes with
    | None -> "None"
    | Some a -> pairs a)
  ^ "}"

let kind = function
  | Decl_val {name} -> "Decl_val(" ^ quote name ^ ")"
  | Decl_send {name} -> "Decl_send(" ^ quote name ^ ")"
  | Decl_new {name} -> "Decl_new(" ^ quote name ^ ")"
  | Decl_get {name} -> "Decl_get(" ^ quote name ^ ")"
  | Decl_set {name} -> "Decl_set(" ^ quote name ^ ")"
  | Decl_get_index -> "Decl_get_index"
  | Decl_set_index -> "Decl_set_index"

let decl d =
  "{" ^ kind d.kind ^ ","
  ^ (match d.module_ with
    | None -> "None"
    | Some Module_itself -> "Module_itself"
    | Some (Module_named m) -> "Module_named" ^ module_name m)
  ^ "," ^ list quote d.scopes ^ "," ^ bool d.variadic ^ ","
  ^ string_of_int d.effective_arity ^ "}"

let return_wrapper = function
  | Return_unset -> "Return_unset"
  | Return_identity -> "Return_identity"
  | Return_null_to_opt -> "Return_null_to_opt"
  | Return_null_undefined_to_opt -> "Return_null_undefined_to_opt"

let spec = function
  | Ffi_bs (params, ret, d) ->
    "Ffi_bs(" ^ list param params ^ "," ^ return_wrapper ret ^ "," ^ decl d ^ ")"
  | Ffi_obj_create params -> "Ffi_obj_create" ^ list obj_param params

let inline_const = function
  | Const_str {s; delim = None} -> "Const_str(" ^ quote s ^ ")"
  | Const_str {s; delim = Some d} -> "Const_str(" ^ quote s ^ "," ^ delim d ^ ")"
  | Const_bool b -> "Const_bool(" ^ bool b ^ ")"
  | Const_int i -> "Const_int(" ^ Int32.to_string i ^ ")"
  | Const_bigint {negative; digits} ->
    "Const_bigint(" ^ bool negative ^ "," ^ quote digits ^ ")"
  | Const_float f -> "Const_float(" ^ quote f ^ ")"

(* The strings a primitive representation prints as. *)
let primitive_repr : Parsetree.primitive_repr -> string list = function
  | Prim_name s -> [s]
  | Prim_ffi {name; spec = s} -> [name; spec s]
  | Prim_inline_const c -> [inline_const c]

let import_source : Lambda.import_source -> string = function
  | Import_module {module_; path} ->
    "Import_module(" ^ Ident.name module_ ^ "," ^ list quote path ^ ")"
  | Import_external {module_; path} ->
    "Import_external(" ^ module_name module_ ^ "," ^ list quote path ^ ")"
