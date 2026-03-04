(* Sexp printer for Typedtree - used for parity testing between OCaml and Rust compilers *)

open Asttypes
open Typedtree

(* Sexp module - simple string-based pretty printing *)
module Sexp = struct
  type t = Atom of string | List of t list

  let atom s = Atom s
  let list l = List l

  (* Simple pretty printer without Res_doc dependency *)
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
let string txt = Sexp.atom ("\"" ^ txt ^ "\"")

let opt_string = function
  | None -> Sexp.atom "None"
  | Some s -> Sexp.list [Sexp.atom "Some"; string s]

let opt f = function
  | None -> Sexp.atom "None"
  | Some x -> Sexp.list [Sexp.atom "Some"; f x]

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

(* Path printer *)
let rec path p =
  match p with
  | Path.Pident id -> Sexp.list [Sexp.atom "Pident"; string (Ident.name id)]
  | Path.Pdot (p, s, _) -> Sexp.list [Sexp.atom "Pdot"; path p; string s]
  | Path.Papply (p1, p2) -> Sexp.list [Sexp.atom "Papply"; path p1; path p2]

(* Longident printer *)
let rec longident l =
  match l with
  | Longident.Lident s -> Sexp.list [Sexp.atom "Lident"; string s]
  | Longident.Ldot (l, s) -> Sexp.list [Sexp.atom "Ldot"; longident l; string s]
  | Longident.Lapply (l1, l2) -> Sexp.list [Sexp.atom "Lapply"; longident l1; longident l2]

let longident_loc li = longident li.txt

(* Ident printer - just the name, skip stamp for determinism *)
let ident id = string (Ident.name id)

(* Constant printer *)
let constant c =
  match c with
  | Const_int i -> Sexp.list [Sexp.atom "Const_int"; Sexp.atom (string_of_int i)]
  | Const_char c -> Sexp.list [Sexp.atom "Const_char"; Sexp.atom (Printf.sprintf "%d" c)]
  | Const_string (s, delim) ->
    Sexp.list [Sexp.atom "Const_string"; string s; opt string delim]
  | Const_float s -> Sexp.list [Sexp.atom "Const_float"; string s]
  | Const_int32 i -> Sexp.list [Sexp.atom "Const_int32"; Sexp.atom (Int32.to_string i)]
  | Const_int64 i -> Sexp.list [Sexp.atom "Const_int64"; Sexp.atom (Int64.to_string i)]
  | Const_bigint (positive, s) ->
    let sign_str = if positive then "+" else "-" in
    Sexp.list [Sexp.atom "Const_bigint"; Sexp.atom sign_str; string s]

(* Flags *)
let rec_flag = function
  | Nonrecursive -> Sexp.atom "Nonrecursive"
  | Recursive -> Sexp.atom "Recursive"

let direction_flag = function
  | Upto -> Sexp.atom "Upto"
  | Downto -> Sexp.atom "Downto"

let private_flag = function
  | Public -> Sexp.atom "Public"
  | Private -> Sexp.atom "Private"

let mutable_flag = function
  | Immutable -> Sexp.atom "Immutable"
  | Mutable -> Sexp.atom "Mutable"

let override_flag = function
  | Override -> Sexp.atom "Override"
  | Fresh -> Sexp.atom "Fresh"

let closed_flag = function
  | Closed -> Sexp.atom "Closed"
  | Open -> Sexp.atom "Open"

let sexp_arg_label lbl =
  match lbl with
  | Nolabel -> Sexp.atom "Nolabel"
  | Labelled {txt} -> Sexp.list [Sexp.atom "Labelled"; string txt]
  | Optional {txt} -> Sexp.list [Sexp.atom "Optional"; string txt]

let variance = function
  | Covariant -> Sexp.atom "Covariant"
  | Contravariant -> Sexp.atom "Contravariant"
  | Invariant -> Sexp.atom "Invariant"

let partial = function
  | Partial -> Sexp.atom "Partial"
  | Total -> Sexp.atom "Total"

(* Type expression dedup - each unique type is serialized once, referenced by #N *)
(* Uses physical identity (type_expr.id after repr) as the dedup key. *)
let dedup_tbl : (int, int) Hashtbl.t = Hashtbl.create 256
let dedup_arr : Sexp.t array ref = ref (Array.make 1024 (Sexp.atom "_"))
let dedup_next_idx : int ref = ref 0

let reset_dedup () =
  Hashtbl.clear dedup_tbl;
  dedup_arr := Array.make 1024 (Sexp.atom "_");
  dedup_next_idx := 0

let build_types_preamble () =
  let n = !dedup_next_idx in
  let items = ref [] in
  for i = n - 1 downto 0 do
    items := Sexp.list [Sexp.atom (string_of_int i); (!dedup_arr).(i)] :: !items
  done;
  Sexp.list (Sexp.atom "types" :: !items)

let ensure_dedup_capacity idx =
  let arr = !dedup_arr in
  if idx >= Array.length arr then begin
    let new_len = max (Array.length arr * 2) (idx + 1) in
    let new_arr = Array.make new_len (Sexp.atom "_") in
    Array.blit arr 0 new_arr 0 (Array.length arr);
    dedup_arr := new_arr
  end

let rec type_expr te =
  let te = Btype.repr te in  (* Follow Tlink chains *)
  let key = te.Types.id in
  match Hashtbl.find_opt dedup_tbl key with
  | Some idx -> Sexp.atom (Printf.sprintf "#%d" idx)
  | None ->
    let idx = !dedup_next_idx in
    incr dedup_next_idx;
    Hashtbl.add dedup_tbl key idx;
    ensure_dedup_capacity idx;
    let sexp = type_expr_body te in
    (!dedup_arr).(idx) <- sexp;
    Sexp.atom (Printf.sprintf "#%d" idx)

and type_expr_body te =
  (* All type_expr calls use let-bindings to ensure deterministic left-to-right
     evaluation order. OCaml's ocamlopt uses unspecified order for list literal
     elements, so inlining type_expr in [...] would give inconsistent ordering. *)
  match te.Types.desc with
  | Tvar name -> Sexp.list [Sexp.atom "Tvar"; opt_string name]
  | Tarrow (arg, ret, _, arity) ->
    let arg_sexp = type_expr arg.Types.typ in
    let ret_sexp = type_expr ret in
    Sexp.list [
      Sexp.atom "Tarrow";
      sexp_arg_label arg.Types.lbl;
      arg_sexp;
      ret_sexp;
      (match arity with Some a -> Sexp.list [Sexp.atom "Some"; Sexp.atom (string_of_int a)] | None -> Sexp.atom "None");
    ]
  | Ttuple l ->
    let items = List.map type_expr l in
    Sexp.list (Sexp.atom "Ttuple" :: items)
  | Tconstr (p, args, _) ->
    let arg_sexps = List.map type_expr args in
    Sexp.list [Sexp.atom "Tconstr"; path p; Sexp.list arg_sexps]
  | Tobject (ty, _) ->
    (* Sort object fields by name to normalize ordering for parity *)
    Sexp.list [Sexp.atom "Tobject"; object_fields_sorted ty]
  | Tfield (name, kind, ty1, ty2) ->
    let kind_str = match Btype.field_kind_repr kind with
      | Fpresent -> "Fpresent"
      | Fabsent -> "Fabsent"
      | Fvar _ -> "Fvar"
    in
    let ty1_sexp = type_expr ty1 in
    let ty2_sexp = type_expr ty2 in
    Sexp.list [Sexp.atom "Tfield"; string name; Sexp.atom kind_str; ty1_sexp; ty2_sexp]
  | Tnil -> Sexp.atom "Tnil"
  | Tlink _ -> Sexp.atom "Tlink"  (* Should not happen after Btype.repr *)
  | Tsubst ty ->
    let ty_sexp = type_expr ty in
    Sexp.list [Sexp.atom "Tsubst"; ty_sexp]
  | Tvariant row -> row_desc_sexp row
  | Tunivar name -> Sexp.list [Sexp.atom "Tunivar"; opt_string name]
  | Tpoly (ty, tyl) ->
    let ty_sexp = type_expr ty in
    let tyl_sexps = List.map type_expr tyl in
    Sexp.list [Sexp.atom "Tpoly"; ty_sexp; Sexp.list tyl_sexps]
  | Tpackage (p, lids, tyl) ->
    let tyl_sexps = List.map type_expr tyl in
    Sexp.list [
      Sexp.atom "Tpackage";
      path p;
      Sexp.list (List.map (fun l -> longident l) lids);
      Sexp.list tyl_sexps;
    ]

and object_fields_sorted ty =
  (* Collect all Tfield entries from the chain, sort by name, rebuild *)
  let rec collect_fields ty acc =
    let ty = Btype.repr ty in
    match ty.Types.desc with
    | Tfield (name, kind, field_ty, rest) ->
      let kind_str = match Btype.field_kind_repr kind with
        | Fpresent -> "Fpresent"
        | Fabsent -> "Fabsent"
        | Fvar _ -> "Fvar"
      in
      collect_fields rest ((name, kind_str, field_ty) :: acc)
    | _ -> (List.rev acc, ty)
  in
  let (fields, tail) = collect_fields ty [] in
  let sorted_fields = List.sort (fun (n1, _, _) (n2, _, _) -> String.compare n1 n2) fields in
  let tail_sexp = type_expr tail in
  List.fold_right (fun (name, kind_str, field_ty) rest_sexp ->
    let field_ty_sexp = type_expr field_ty in
    Sexp.list [Sexp.atom "Tfield"; string name; Sexp.atom kind_str; field_ty_sexp; rest_sexp]
  ) sorted_fields tail_sexp

and row_desc_sexp row =
  let row = Btype.row_repr row in
  (* Sort row_fields by label to normalize ordering for parity *)
  let sorted_fields = List.sort (fun (l1, _) (l2, _) -> String.compare l1 l2) row.Types.row_fields in
  let fields_sexp = Sexp.list (List.map (fun (l, rf) ->
    let rf_sexp = row_field_sexp rf in
    Sexp.list [string l; rf_sexp]
  ) sorted_fields) in
  Sexp.list [
    Sexp.atom "Tvariant";
    fields_sexp;
    Sexp.atom (if row.Types.row_closed then "closed" else "open");
    Sexp.atom (if row.Types.row_fixed then "fixed" else "not_fixed");
  ]

and row_field_sexp rf =
  match Btype.row_field_repr rf with
  | Rpresent None -> Sexp.atom "Rpresent_none"
  | Rpresent (Some ty) ->
    let ty_sexp = type_expr ty in
    Sexp.list [Sexp.atom "Rpresent"; ty_sexp]
  | Reither (c, tyl, _, _) ->
    let tyl_sexp = Sexp.list (List.map type_expr tyl) in
    Sexp.list [
      Sexp.atom "Reither";
      Sexp.atom (if c then "const" else "non_const");
      tyl_sexp;
    ]
  | Rabsent -> Sexp.atom "Rabsent"

(* Pattern *)
let rec pattern ~with_locs p =
  let loc = if with_locs then [location ~with_locs p.pat_loc] else [] in
  let extras = List.map (fun (extra, loc, attrs) ->
    pat_extra ~with_locs extra loc attrs
  ) p.pat_extra in
  let desc = pattern_desc ~with_locs p.pat_desc in
  let ty = type_expr p.pat_type in
  Sexp.list ([Sexp.atom "pattern"] @ loc @ extras @ [desc; Sexp.list [Sexp.atom "type"; ty]])

and pat_extra ~with_locs extra loc attrs =
  let loc_sexp = if with_locs then [location ~with_locs loc] else [] in
  let attrs_sexp = attributes ~with_locs attrs in
  match extra with
  | Tpat_constraint ct ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list ([Sexp.atom "Tpat_constraint"; ct_sexp] @ loc_sexp @ [attrs_sexp])
  | Tpat_type (p, _) ->
    Sexp.list ([Sexp.atom "Tpat_type"; path p] @ loc_sexp @ [attrs_sexp])
  | Tpat_open (p, _, _) ->
    Sexp.list ([Sexp.atom "Tpat_open"; path p] @ loc_sexp @ [attrs_sexp])
  | Tpat_unpack ->
    Sexp.list ([Sexp.atom "Tpat_unpack"] @ loc_sexp @ [attrs_sexp])

and pattern_desc ~with_locs desc =
  match desc with
  | Tpat_any -> Sexp.atom "Tpat_any"
  | Tpat_var (id, _) -> Sexp.list [Sexp.atom "Tpat_var"; ident id]
  | Tpat_alias (p, id, _) ->
    let p_sexp = pattern ~with_locs p in
    Sexp.list [Sexp.atom "Tpat_alias"; p_sexp; ident id]
  | Tpat_constant c -> Sexp.list [Sexp.atom "Tpat_constant"; constant c]
  | Tpat_tuple l ->
    let items = List.map (pattern ~with_locs) l in
    Sexp.list (Sexp.atom "Tpat_tuple" :: items)
  | Tpat_construct (li, _, args) ->
    let args_sexp = Sexp.list (List.map (pattern ~with_locs) args) in
    Sexp.list [
      Sexp.atom "Tpat_construct";
      longident_loc li;
      args_sexp;
    ]
  | Tpat_variant (label, arg, _) ->
    let arg_sexp = opt (pattern ~with_locs) arg in
    Sexp.list [Sexp.atom "Tpat_variant"; string label; arg_sexp]
  | Tpat_record (fields, flag) ->
    let fields_sexp = Sexp.list (List.map (fun (li, _, p, opt_flag) ->
      let p_sexp = pattern ~with_locs p in
      Sexp.list [longident_loc li; p_sexp; Sexp.atom (if opt_flag then "optional" else "required")]
    ) fields) in
    Sexp.list [
      Sexp.atom "Tpat_record";
      fields_sexp;
      closed_flag flag;
    ]
  | Tpat_array l ->
    let items = List.map (pattern ~with_locs) l in
    Sexp.list (Sexp.atom "Tpat_array" :: items)
  | Tpat_or (p1, p2, _) ->
    let p1_sexp = pattern ~with_locs p1 in
    let p2_sexp = pattern ~with_locs p2 in
    Sexp.list [Sexp.atom "Tpat_or"; p1_sexp; p2_sexp]

(* Expression *)
and expression ~with_locs e =
  let loc = if with_locs then [location ~with_locs e.exp_loc] else [] in
  let extras = List.map (fun (extra, loc, attrs) ->
    exp_extra ~with_locs extra loc attrs
  ) e.exp_extra in
  let desc = expression_desc ~with_locs e.exp_desc in
  let ty = type_expr e.exp_type in
  let attrs = attributes ~with_locs e.exp_attributes in
  Sexp.list ([Sexp.atom "expression"] @ loc @ extras @ [desc; Sexp.list [Sexp.atom "type"; ty]; attrs])

and exp_extra ~with_locs extra loc attrs =
  let loc_sexp = if with_locs then [location ~with_locs loc] else [] in
  let attrs_sexp = attributes ~with_locs attrs in
  match extra with
  | Texp_constraint ct ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list ([Sexp.atom "Texp_constraint"; ct_sexp] @ loc_sexp @ [attrs_sexp])
  | Texp_coerce ct ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list ([Sexp.atom "Texp_coerce"; ct_sexp] @ loc_sexp @ [attrs_sexp])
  | Texp_open (flag, p, _, _) ->
    Sexp.list ([Sexp.atom "Texp_open"; override_flag flag; path p] @ loc_sexp @ [attrs_sexp])
  | Texp_newtype s ->
    Sexp.list ([Sexp.atom "Texp_newtype"; string s] @ loc_sexp @ [attrs_sexp])

and expression_desc ~with_locs desc =
  match desc with
  | Texp_ident (p, li, _) ->
    Sexp.list [Sexp.atom "Texp_ident"; path p; longident_loc li]
  | Texp_constant c -> Sexp.list [Sexp.atom "Texp_constant"; constant c]
  | Texp_let (flag, vbs, e) ->
    let vbs_sexp = Sexp.list (List.map (value_binding ~with_locs) vbs) in
    let e_sexp = expression ~with_locs e in
    Sexp.list [
      Sexp.atom "Texp_let";
      rec_flag flag;
      vbs_sexp;
      e_sexp;
    ]
  | Texp_function { arg_label; arity; param; case = c; partial = p; async } ->
    let c_sexp = case ~with_locs c in
    Sexp.list [
      Sexp.atom "Texp_function";
      sexp_arg_label arg_label;
      opt (fun a -> Sexp.atom (string_of_int a)) arity;
      ident param;
      c_sexp;
      partial p;
      Sexp.atom (if async then "async" else "sync");
    ]
  | Texp_apply { funct; args; partial = p; transformed_jsx } ->
    let funct_sexp = expression ~with_locs funct in
    let args_sexp = Sexp.list (List.map (fun (lbl, arg) ->
      let arg_sexp = opt (expression ~with_locs) arg in
      Sexp.list [sexp_arg_label lbl; arg_sexp]
    ) args) in
    Sexp.list [
      Sexp.atom "Texp_apply";
      funct_sexp;
      args_sexp;
      Sexp.atom (if p then "partial" else "total");
      Sexp.atom (if transformed_jsx then "jsx" else "not_jsx");
    ]
  | Texp_match (e, cases, exn_cases, p) ->
    let e_sexp = expression ~with_locs e in
    let cases_sexp = Sexp.list (List.map (case ~with_locs) cases) in
    let exn_cases_sexp = Sexp.list (List.map (case ~with_locs) exn_cases) in
    Sexp.list [
      Sexp.atom "Texp_match";
      e_sexp;
      cases_sexp;
      exn_cases_sexp;
      partial p;
    ]
  | Texp_try (e, cases) ->
    let e_sexp = expression ~with_locs e in
    let cases_sexp = Sexp.list (List.map (case ~with_locs) cases) in
    Sexp.list [
      Sexp.atom "Texp_try";
      e_sexp;
      cases_sexp;
    ]
  | Texp_tuple l ->
    let items = List.map (expression ~with_locs) l in
    Sexp.list (Sexp.atom "Texp_tuple" :: items)
  | Texp_construct (li, _, args) ->
    let args_sexp = Sexp.list (List.map (expression ~with_locs) args) in
    Sexp.list [
      Sexp.atom "Texp_construct";
      longident_loc li;
      args_sexp;
    ]
  | Texp_variant (label, arg) ->
    let arg_sexp = opt (expression ~with_locs) arg in
    Sexp.list [Sexp.atom "Texp_variant"; string label; arg_sexp]
  | Texp_record { fields; representation = _; extended_expression } ->
    let fields_sexp = Sexp.list (Array.to_list (Array.map (fun (ld, def, opt_flag) ->
      let def_sexp = match def with
        | Kept ty ->
          let ty_sexp = type_expr ty in
          Sexp.list [Sexp.atom "Kept"; ty_sexp]
        | Overridden (li, e) ->
          let e_sexp = expression ~with_locs e in
          Sexp.list [Sexp.atom "Overridden"; longident_loc li; e_sexp]
      in
      Sexp.list [string ld.Types.lbl_name; def_sexp; Sexp.atom (if opt_flag then "optional" else "required")]
    ) fields)) in
    let ext_sexp = opt (expression ~with_locs) extended_expression in
    Sexp.list [
      Sexp.atom "Texp_record";
      fields_sexp;
      ext_sexp;
    ]
  | Texp_field (e, li, _) ->
    let e_sexp = expression ~with_locs e in
    Sexp.list [Sexp.atom "Texp_field"; e_sexp; longident_loc li]
  | Texp_setfield (e1, li, _, e2) ->
    let e1_sexp = expression ~with_locs e1 in
    let e2_sexp = expression ~with_locs e2 in
    Sexp.list [Sexp.atom "Texp_setfield"; e1_sexp; longident_loc li; e2_sexp]
  | Texp_array l ->
    let items = List.map (expression ~with_locs) l in
    Sexp.list (Sexp.atom "Texp_array" :: items)
  | Texp_ifthenelse (e1, e2, e3) ->
    let e1_sexp = expression ~with_locs e1 in
    let e2_sexp = expression ~with_locs e2 in
    let e3_sexp = opt (expression ~with_locs) e3 in
    Sexp.list [Sexp.atom "Texp_ifthenelse"; e1_sexp; e2_sexp; e3_sexp]
  | Texp_sequence (e1, e2) ->
    let e1_sexp = expression ~with_locs e1 in
    let e2_sexp = expression ~with_locs e2 in
    Sexp.list [Sexp.atom "Texp_sequence"; e1_sexp; e2_sexp]
  | Texp_while (e1, e2) ->
    let e1_sexp = expression ~with_locs e1 in
    let e2_sexp = expression ~with_locs e2 in
    Sexp.list [Sexp.atom "Texp_while"; e1_sexp; e2_sexp]
  | Texp_for (id, _, e1, e2, flag, e3) ->
    let e1_sexp = expression ~with_locs e1 in
    let e2_sexp = expression ~with_locs e2 in
    let e3_sexp = expression ~with_locs e3 in
    Sexp.list [Sexp.atom "Texp_for"; ident id; e1_sexp; e2_sexp; direction_flag flag; e3_sexp]
  | Texp_send (e, Tmeth_name name, arg) ->
    let e_sexp = expression ~with_locs e in
    let arg_sexp = opt (expression ~with_locs) arg in
    Sexp.list [Sexp.atom "Texp_send"; e_sexp; string name; arg_sexp]
  | Texp_letmodule (id, _, me, e) ->
    let me_sexp = module_expr ~with_locs me in
    let e_sexp = expression ~with_locs e in
    Sexp.list [Sexp.atom "Texp_letmodule"; ident id; me_sexp; e_sexp]
  | Texp_letexception (ec, e) ->
    let ec_sexp = extension_constructor ~with_locs ec in
    let e_sexp = expression ~with_locs e in
    Sexp.list [Sexp.atom "Texp_letexception"; ec_sexp; e_sexp]
  | Texp_assert e ->
    let e_sexp = expression ~with_locs e in
    Sexp.list [Sexp.atom "Texp_assert"; e_sexp]
  | Texp_pack me ->
    let me_sexp = module_expr ~with_locs me in
    Sexp.list [Sexp.atom "Texp_pack"; me_sexp]
  | Texp_extension_constructor (li, p) ->
    Sexp.list [Sexp.atom "Texp_extension_constructor"; longident_loc li; path p]

and case ~with_locs c =
  let lhs_sexp = pattern ~with_locs c.c_lhs in
  let guard_sexp = opt (expression ~with_locs) c.c_guard in
  let rhs_sexp = expression ~with_locs c.c_rhs in
  Sexp.list [
    Sexp.atom "case";
    lhs_sexp;
    guard_sexp;
    rhs_sexp;
  ]

and value_binding ~with_locs vb =
  let loc = if with_locs then [location ~with_locs vb.vb_loc] else [] in
  let pat_sexp = pattern ~with_locs vb.vb_pat in
  let expr_sexp = expression ~with_locs vb.vb_expr in
  let attrs_sexp = attributes ~with_locs vb.vb_attributes in
  Sexp.list ([
    Sexp.atom "value_binding";
  ] @ loc @ [
    pat_sexp;
    expr_sexp;
    attrs_sexp;
  ])

(* Core type *)
and core_type ~with_locs ct =
  let loc = if with_locs then [location ~with_locs ct.ctyp_loc] else [] in
  let desc = core_type_desc ~with_locs ct.ctyp_desc in
  let ty = type_expr ct.ctyp_type in
  let attrs = attributes ~with_locs ct.ctyp_attributes in
  Sexp.list ([Sexp.atom "core_type"] @ loc @ [desc; Sexp.list [Sexp.atom "type"; ty]; attrs])

and core_type_desc ~with_locs desc =
  match desc with
  | Ttyp_any -> Sexp.atom "Ttyp_any"
  | Ttyp_var s -> Sexp.list [Sexp.atom "Ttyp_var"; string s]
  | Ttyp_arrow (arg, ret, arity) ->
    let arg_attrs_sexp = attributes ~with_locs arg.attrs in
    let arg_ct_sexp = core_type ~with_locs arg.typ in
    let ret_sexp = core_type ~with_locs ret in
    Sexp.list [
      Sexp.atom "Ttyp_arrow";
      sexp_arg_label arg.lbl;
      arg_attrs_sexp;
      arg_ct_sexp;
      ret_sexp;
      opt (fun a -> Sexp.atom (string_of_int a)) arity;
    ]
  | Ttyp_tuple l ->
    let items = List.map (core_type ~with_locs) l in
    Sexp.list (Sexp.atom "Ttyp_tuple" :: items)
  | Ttyp_constr (p, _, args) ->
    let args_sexp = Sexp.list (List.map (core_type ~with_locs) args) in
    Sexp.list [Sexp.atom "Ttyp_constr"; path p; args_sexp]
  | Ttyp_object (fields, flag) ->
    let fields_sexp = Sexp.list (List.map (object_field ~with_locs) fields) in
    Sexp.list [
      Sexp.atom "Ttyp_object";
      fields_sexp;
      closed_flag flag;
    ]
  | Ttyp_alias (ct, s) ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list [Sexp.atom "Ttyp_alias"; ct_sexp; string s]
  | Ttyp_variant (fields, flag, labels) ->
    let fields_sexp = Sexp.list (List.map (row_field_decl ~with_locs) fields) in
    Sexp.list [
      Sexp.atom "Ttyp_variant";
      fields_sexp;
      closed_flag flag;
      opt (fun l -> Sexp.list (List.map string l)) labels;
    ]
  | Ttyp_poly (vars, ct) ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list [Sexp.atom "Ttyp_poly"; Sexp.list (List.map string vars); ct_sexp]
  | Ttyp_package pkg ->
    let fields_sexp = Sexp.list (List.map (fun (li, ct) ->
      let ct_sexp = core_type ~with_locs ct in
      Sexp.list [longident_loc li; ct_sexp]
    ) pkg.pack_fields) in
    Sexp.list [
      Sexp.atom "Ttyp_package";
      path pkg.pack_path;
      fields_sexp;
    ]

and object_field ~with_locs field =
  match field with
  | OTtag (name, attrs, ct) ->
    let attrs_sexp = attributes ~with_locs attrs in
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list [Sexp.atom "OTtag"; string name.txt; attrs_sexp; ct_sexp]
  | OTinherit ct ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list [Sexp.atom "OTinherit"; ct_sexp]

and row_field_decl ~with_locs field =
  match field with
  | Ttag (name, attrs, const, args) ->
    let attrs_sexp = attributes ~with_locs attrs in
    let args_sexp = Sexp.list (List.map (core_type ~with_locs) args) in
    Sexp.list [
      Sexp.atom "Ttag";
      string name.txt;
      attrs_sexp;
      Sexp.atom (if const then "const" else "non_const");
      args_sexp;
    ]
  | Tinherit ct ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list [Sexp.atom "Tinherit"; ct_sexp]

(* Attributes *)
and attribute ~with_locs (name, payload) =
  Sexp.list [Sexp.atom "attribute"; string name.txt; payload_sexp ~with_locs payload]

and attributes ~with_locs attrs =
  Sexp.list (Sexp.atom "attributes" :: List.map (attribute ~with_locs) attrs)

and payload_sexp ~with_locs:_ p =
  match p with
  | Parsetree.PStr _ -> Sexp.list [Sexp.atom "PStr"; Sexp.atom "<structure>"]
  | Parsetree.PSig _ -> Sexp.list [Sexp.atom "PSig"; Sexp.atom "<signature>"]
  | Parsetree.PTyp _ -> Sexp.list [Sexp.atom "PTyp"; Sexp.atom "<core_type>"]
  | Parsetree.PPat _ -> Sexp.list [Sexp.atom "PPat"; Sexp.atom "<pattern>"]

(* Type declarations *)
and type_declaration ~with_locs td =
  let loc = if with_locs then [location ~with_locs td.typ_loc] else [] in
  let params_sexp = Sexp.list [Sexp.atom "params"; Sexp.list (List.map (fun (ct, v) ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list [ct_sexp; variance v]
  ) td.typ_params)] in
  let cstrs_sexp = Sexp.list [Sexp.atom "cstrs"; Sexp.list (List.map (fun (ct1, ct2, _loc) ->
    let ct1_sexp = core_type ~with_locs ct1 in
    let ct2_sexp = core_type ~with_locs ct2 in
    Sexp.list [ct1_sexp; ct2_sexp]
  ) td.typ_cstrs)] in
  let kind_sexp = Sexp.list [Sexp.atom "kind"; type_kind ~with_locs td.typ_kind] in
  let manifest_sexp = Sexp.list [Sexp.atom "manifest"; opt (core_type ~with_locs) td.typ_manifest] in
  let attrs_sexp = attributes ~with_locs td.typ_attributes in
  Sexp.list ([
    Sexp.atom "type_declaration";
    ident td.typ_id;
    string td.typ_name.txt;
  ] @ loc @ [
    params_sexp;
    cstrs_sexp;
    kind_sexp;
    Sexp.list [Sexp.atom "private"; private_flag td.typ_private];
    manifest_sexp;
    attrs_sexp;
  ])

and type_kind ~with_locs kind =
  match kind with
  | Ttype_abstract -> Sexp.atom "Ttype_abstract"
  | Ttype_variant cds ->
    let items = List.map (constructor_declaration ~with_locs) cds in
    Sexp.list (Sexp.atom "Ttype_variant" :: items)
  | Ttype_record lds ->
    let items = List.map (label_declaration ~with_locs) lds in
    Sexp.list (Sexp.atom "Ttype_record" :: items)
  | Ttype_open -> Sexp.atom "Ttype_open"

and constructor_declaration ~with_locs cd =
  let loc = if with_locs then [location ~with_locs cd.cd_loc] else [] in
  let args_sexp = constructor_arguments ~with_locs cd.cd_args in
  let res_sexp = opt (core_type ~with_locs) cd.cd_res in
  let attrs_sexp = attributes ~with_locs cd.cd_attributes in
  Sexp.list ([
    Sexp.atom "constructor_declaration";
    ident cd.cd_id;
    string cd.cd_name.txt;
  ] @ loc @ [
    args_sexp;
    res_sexp;
    attrs_sexp;
  ])

and constructor_arguments ~with_locs args =
  match args with
  | Cstr_tuple cts ->
    let items = List.map (core_type ~with_locs) cts in
    Sexp.list (Sexp.atom "Cstr_tuple" :: items)
  | Cstr_record lds ->
    let items = List.map (label_declaration ~with_locs) lds in
    Sexp.list (Sexp.atom "Cstr_record" :: items)

and label_declaration ~with_locs ld =
  let loc = if with_locs then [location ~with_locs ld.ld_loc] else [] in
  let ct_sexp = core_type ~with_locs ld.ld_type in
  let attrs_sexp = attributes ~with_locs ld.ld_attributes in
  Sexp.list ([
    Sexp.atom "label_declaration";
    ident ld.ld_id;
    string ld.ld_name.txt;
  ] @ loc @ [
    mutable_flag ld.ld_mutable;
    Sexp.atom (if ld.ld_optional then "optional" else "required");
    ct_sexp;
    attrs_sexp;
  ])

(* Type extension *)
and type_extension ~with_locs te =
  let params_sexp = Sexp.list [Sexp.atom "params"; Sexp.list (List.map (fun (ct, v) ->
    let ct_sexp = core_type ~with_locs ct in
    Sexp.list [ct_sexp; variance v]
  ) te.tyext_params)] in
  let constructors_sexp = Sexp.list [Sexp.atom "constructors"; Sexp.list (List.map (extension_constructor ~with_locs) te.tyext_constructors)] in
  let attrs_sexp = attributes ~with_locs te.tyext_attributes in
  Sexp.list [
    Sexp.atom "type_extension";
    path te.tyext_path;
    longident_loc te.tyext_txt;
    params_sexp;
    constructors_sexp;
    private_flag te.tyext_private;
    attrs_sexp;
  ]

and extension_constructor ~with_locs ec =
  let loc = if with_locs then [location ~with_locs ec.ext_loc] else [] in
  let kind_sexp = extension_constructor_kind ~with_locs ec.ext_kind in
  let attrs_sexp = attributes ~with_locs ec.ext_attributes in
  Sexp.list ([
    Sexp.atom "extension_constructor";
    ident ec.ext_id;
    string ec.ext_name.txt;
  ] @ loc @ [
    kind_sexp;
    attrs_sexp;
  ])

and extension_constructor_kind ~with_locs kind =
  match kind with
  | Text_decl (args, ret) ->
    let args_sexp = constructor_arguments ~with_locs args in
    let ret_sexp = opt (core_type ~with_locs) ret in
    Sexp.list [Sexp.atom "Text_decl"; args_sexp; ret_sexp]
  | Text_rebind (p, _) ->
    Sexp.list [Sexp.atom "Text_rebind"; path p]

(* Value description *)
and value_description ~with_locs vd =
  let loc = if with_locs then [location ~with_locs vd.val_loc] else [] in
  let ct_sexp = core_type ~with_locs vd.val_desc in
  let attrs_sexp = attributes ~with_locs vd.val_attributes in
  Sexp.list ([
    Sexp.atom "value_description";
    ident vd.val_id;
    string vd.val_name.txt;
  ] @ loc @ [
    ct_sexp;
    Sexp.list (Sexp.atom "prim" :: List.map string vd.val_prim);
    attrs_sexp;
  ])

(* Module types *)
and module_type ~with_locs mt =
  let loc = if with_locs then [location ~with_locs mt.mty_loc] else [] in
  let desc = module_type_desc ~with_locs mt.mty_desc in
  let attrs = attributes ~with_locs mt.mty_attributes in
  Sexp.list ([Sexp.atom "module_type"] @ loc @ [desc; attrs])

and module_type_desc ~with_locs desc =
  match desc with
  | Tmty_ident (p, _) -> Sexp.list [Sexp.atom "Tmty_ident"; path p]
  | Tmty_signature sg ->
    let sg_sexp = signature ~with_locs sg in
    Sexp.list [Sexp.atom "Tmty_signature"; sg_sexp]
  | Tmty_functor (id, _, mt_arg, mt_res) ->
    let mt_arg_sexp = opt (module_type ~with_locs) mt_arg in
    let mt_res_sexp = module_type ~with_locs mt_res in
    Sexp.list [Sexp.atom "Tmty_functor"; ident id; mt_arg_sexp; mt_res_sexp]
  | Tmty_with (mt, constraints) ->
    let mt_sexp = module_type ~with_locs mt in
    let constraints_sexp = Sexp.list (List.map (fun (p, _, wc) ->
      let wc_sexp = with_constraint ~with_locs wc in
      Sexp.list [path p; wc_sexp]
    ) constraints) in
    Sexp.list [
      Sexp.atom "Tmty_with";
      mt_sexp;
      constraints_sexp;
    ]
  | Tmty_typeof me ->
    let me_sexp = module_expr ~with_locs me in
    Sexp.list [Sexp.atom "Tmty_typeof"; me_sexp]
  | Tmty_alias (p, _) -> Sexp.list [Sexp.atom "Tmty_alias"; path p]

and with_constraint ~with_locs wc =
  match wc with
  | Twith_type td ->
    let td_sexp = type_declaration ~with_locs td in
    Sexp.list [Sexp.atom "Twith_type"; td_sexp]
  | Twith_module (p, _) -> Sexp.list [Sexp.atom "Twith_module"; path p]
  | Twith_typesubst td ->
    let td_sexp = type_declaration ~with_locs td in
    Sexp.list [Sexp.atom "Twith_typesubst"; td_sexp]
  | Twith_modsubst (p, _) -> Sexp.list [Sexp.atom "Twith_modsubst"; path p]

(* Signature *)
and signature ~with_locs sg =
  let items = List.map (signature_item ~with_locs) sg.sig_items in
  Sexp.list (Sexp.atom "signature" :: items)

and signature_item ~with_locs si =
  let loc = if with_locs then [location ~with_locs si.sig_loc] else [] in
  let desc = signature_item_desc ~with_locs si.sig_desc in
  Sexp.list ([Sexp.atom "signature_item"] @ loc @ [desc])

and signature_item_desc ~with_locs desc =
  match desc with
  | Tsig_value vd ->
    let vd_sexp = value_description ~with_locs vd in
    Sexp.list [Sexp.atom "Tsig_value"; vd_sexp]
  | Tsig_type (flag, tds) ->
    let tds_sexp = Sexp.list (List.map (type_declaration ~with_locs) tds) in
    Sexp.list [Sexp.atom "Tsig_type"; rec_flag flag; tds_sexp]
  | Tsig_typext te ->
    let te_sexp = type_extension ~with_locs te in
    Sexp.list [Sexp.atom "Tsig_typext"; te_sexp]
  | Tsig_exception ec ->
    let ec_sexp = extension_constructor ~with_locs ec in
    Sexp.list [Sexp.atom "Tsig_exception"; ec_sexp]
  | Tsig_module md ->
    let md_sexp = module_declaration ~with_locs md in
    Sexp.list [Sexp.atom "Tsig_module"; md_sexp]
  | Tsig_recmodule mds ->
    let mds_sexp = Sexp.list (List.map (module_declaration ~with_locs) mds) in
    Sexp.list [Sexp.atom "Tsig_recmodule"; mds_sexp]
  | Tsig_modtype mtd ->
    let mtd_sexp = module_type_declaration ~with_locs mtd in
    Sexp.list [Sexp.atom "Tsig_modtype"; mtd_sexp]
  | Tsig_open od ->
    let od_sexp = open_description ~with_locs od in
    Sexp.list [Sexp.atom "Tsig_open"; od_sexp]
  | Tsig_include incl ->
    let incl_sexp = include_description ~with_locs incl in
    Sexp.list [Sexp.atom "Tsig_include"; incl_sexp]
  | Tsig_attribute attr -> Sexp.list [Sexp.atom "Tsig_attribute"; attribute ~with_locs attr]

and module_declaration ~with_locs md =
  let loc = if with_locs then [location ~with_locs md.md_loc] else [] in
  let mt_sexp = module_type ~with_locs md.md_type in
  let attrs_sexp = attributes ~with_locs md.md_attributes in
  Sexp.list ([
    Sexp.atom "module_declaration";
    ident md.md_id;
    string md.md_name.txt;
  ] @ loc @ [
    mt_sexp;
    attrs_sexp;
  ])

and module_type_declaration ~with_locs mtd =
  let loc = if with_locs then [location ~with_locs mtd.mtd_loc] else [] in
  let mt_sexp = opt (module_type ~with_locs) mtd.mtd_type in
  let attrs_sexp = attributes ~with_locs mtd.mtd_attributes in
  Sexp.list ([
    Sexp.atom "module_type_declaration";
    ident mtd.mtd_id;
    string mtd.mtd_name.txt;
  ] @ loc @ [
    mt_sexp;
    attrs_sexp;
  ])

and open_description ~with_locs od =
  let loc = if with_locs then [location ~with_locs od.open_loc] else [] in
  let attrs_sexp = attributes ~with_locs od.open_attributes in
  Sexp.list ([
    Sexp.atom "open_description";
    path od.open_path;
    longident_loc od.open_txt;
  ] @ loc @ [
    override_flag od.open_override;
    attrs_sexp;
  ])

and include_description ~with_locs incl =
  let loc = if with_locs then [location ~with_locs incl.incl_loc] else [] in
  let mt_sexp = module_type ~with_locs incl.incl_mod in
  let attrs_sexp = attributes ~with_locs incl.incl_attributes in
  Sexp.list ([
    Sexp.atom "include_description";
  ] @ loc @ [
    mt_sexp;
    attrs_sexp;
  ])

(* Module expression *)
and module_expr ~with_locs me =
  let loc = if with_locs then [location ~with_locs me.mod_loc] else [] in
  let desc = module_expr_desc ~with_locs me.mod_desc in
  let attrs = attributes ~with_locs me.mod_attributes in
  Sexp.list ([Sexp.atom "module_expr"] @ loc @ [desc; attrs])

and module_expr_desc ~with_locs desc =
  match desc with
  | Tmod_ident (p, _) -> Sexp.list [Sexp.atom "Tmod_ident"; path p]
  | Tmod_structure str ->
    let str_sexp = structure ~with_locs str in
    Sexp.list [Sexp.atom "Tmod_structure"; str_sexp]
  | Tmod_functor (id, _, mt_arg, me) ->
    let mt_arg_sexp = opt (module_type ~with_locs) mt_arg in
    let me_sexp = module_expr ~with_locs me in
    Sexp.list [Sexp.atom "Tmod_functor"; ident id; mt_arg_sexp; me_sexp]
  | Tmod_apply (me1, me2, _) ->
    let me1_sexp = module_expr ~with_locs me1 in
    let me2_sexp = module_expr ~with_locs me2 in
    Sexp.list [Sexp.atom "Tmod_apply"; me1_sexp; me2_sexp]
  | Tmod_constraint (me, _, constraint_, _) ->
    let me_sexp = module_expr ~with_locs me in
    let constraint_sexp = match constraint_ with
      | Tmodtype_implicit -> Sexp.atom "implicit"
      | Tmodtype_explicit mt ->
        let mt_sexp = module_type ~with_locs mt in
        Sexp.list [Sexp.atom "explicit"; mt_sexp]
    in
    Sexp.list [Sexp.atom "Tmod_constraint"; me_sexp; constraint_sexp]
  | Tmod_unpack (e, _) ->
    let e_sexp = expression ~with_locs e in
    Sexp.list [Sexp.atom "Tmod_unpack"; e_sexp]

(* Structure *)
and structure ~with_locs str =
  let items = List.map (structure_item ~with_locs) str.str_items in
  Sexp.list (Sexp.atom "structure" :: items)

and structure_item ~with_locs si =
  let loc = if with_locs then [location ~with_locs si.str_loc] else [] in
  let desc = structure_item_desc ~with_locs si.str_desc in
  Sexp.list ([Sexp.atom "structure_item"] @ loc @ [desc])

and structure_item_desc ~with_locs desc =
  match desc with
  | Tstr_eval (e, attrs) ->
    let e_sexp = expression ~with_locs e in
    let attrs_sexp = attributes ~with_locs attrs in
    Sexp.list [Sexp.atom "Tstr_eval"; e_sexp; attrs_sexp]
  | Tstr_value (flag, vbs) ->
    let vbs_sexp = Sexp.list (List.map (value_binding ~with_locs) vbs) in
    Sexp.list [Sexp.atom "Tstr_value"; rec_flag flag; vbs_sexp]
  | Tstr_primitive vd ->
    let vd_sexp = value_description ~with_locs vd in
    Sexp.list [Sexp.atom "Tstr_primitive"; vd_sexp]
  | Tstr_type (flag, tds) ->
    let tds_sexp = Sexp.list (List.map (type_declaration ~with_locs) tds) in
    Sexp.list [Sexp.atom "Tstr_type"; rec_flag flag; tds_sexp]
  | Tstr_typext te ->
    let te_sexp = type_extension ~with_locs te in
    Sexp.list [Sexp.atom "Tstr_typext"; te_sexp]
  | Tstr_exception ec ->
    let ec_sexp = extension_constructor ~with_locs ec in
    Sexp.list [Sexp.atom "Tstr_exception"; ec_sexp]
  | Tstr_module mb ->
    let mb_sexp = module_binding ~with_locs mb in
    Sexp.list [Sexp.atom "Tstr_module"; mb_sexp]
  | Tstr_recmodule mbs ->
    let mbs_sexp = Sexp.list (List.map (module_binding ~with_locs) mbs) in
    Sexp.list [Sexp.atom "Tstr_recmodule"; mbs_sexp]
  | Tstr_modtype mtd ->
    let mtd_sexp = module_type_declaration ~with_locs mtd in
    Sexp.list [Sexp.atom "Tstr_modtype"; mtd_sexp]
  | Tstr_open od ->
    let od_sexp = open_description ~with_locs od in
    Sexp.list [Sexp.atom "Tstr_open"; od_sexp]
  | Tstr_include incl ->
    let incl_sexp = include_declaration ~with_locs incl in
    Sexp.list [Sexp.atom "Tstr_include"; incl_sexp]
  | Tstr_attribute attr -> Sexp.list [Sexp.atom "Tstr_attribute"; attribute ~with_locs attr]

and module_binding ~with_locs mb =
  let loc = if with_locs then [location ~with_locs mb.mb_loc] else [] in
  let me_sexp = module_expr ~with_locs mb.mb_expr in
  let attrs_sexp = attributes ~with_locs mb.mb_attributes in
  Sexp.list ([
    Sexp.atom "module_binding";
    ident mb.mb_id;
    string mb.mb_name.txt;
  ] @ loc @ [
    me_sexp;
    attrs_sexp;
  ])

and include_declaration ~with_locs incl =
  let loc = if with_locs then [location ~with_locs incl.incl_loc] else [] in
  let me_sexp = module_expr ~with_locs incl.incl_mod in
  let attrs_sexp = attributes ~with_locs incl.incl_attributes in
  Sexp.list ([
    Sexp.atom "include_declaration";
  ] @ loc @ [
    me_sexp;
    attrs_sexp;
  ])

(* Public API *)
(* Content-based type normalization: merge duplicate type entries *)
let normalize_types_and_body body =
  let n = !dedup_next_idx in
  let arr = !dedup_arr in
  if n = 0 then (build_types_preamble (), body)
  else begin
    (* Phase 1: find content-equivalent entries *)
    let old_to_canonical = Array.init n (fun i -> i) in
    let converge () =
      (* Rewrite refs in type entries using current mapping *)
      let rewrite_ref s =
        let len = String.length s in
        if len > 1 && s.[0] = '#' then
          let idx_str = String.sub s 1 (len - 1) in
          (try
            let idx = int_of_string idx_str in
            if idx >= 0 && idx < n then
              "#" ^ string_of_int old_to_canonical.(idx)
            else s
          with Failure _ -> s)
        else s
      in
      let rec rewrite_sexp = function
        | Sexp.Atom s -> Sexp.Atom (rewrite_ref s)
        | Sexp.List items -> Sexp.List (List.map rewrite_sexp items)
      in
      let rewritten = Array.init n (fun i -> rewrite_sexp arr.(i)) in
      (* No normalization stripping — comparing exact output *)
      let changed = ref false in
      let content_tbl : (string, int) Hashtbl.t = Hashtbl.create n in
      Hashtbl.clear content_tbl;
      for idx = 0 to n - 1 do
        if old_to_canonical.(idx) = idx then begin
          let content = Sexp.to_string rewritten.(idx) in
          match Hashtbl.find_opt content_tbl content with
          | Some canonical ->
            (* Merge: all entries pointing to idx now point to canonical *)
            for j = 0 to n - 1 do
              if old_to_canonical.(j) = idx then begin
                old_to_canonical.(j) <- canonical;
                changed := true
              end
            done
          | None ->
            Hashtbl.add content_tbl content idx
        end
      done;
      (* Update arr with rewritten versions *)
      Array.blit rewritten 0 arr 0 n;
      !changed
    in
    (* Iterate until stable *)
    for _ = 0 to 19 do
      if converge () then () (* continue *)
    done;
    (* No Phase 2b path alias merge — comparing exact output *)
    (* Phase 2c: compact indices *)
    let canonical_to_new = Hashtbl.create n in
    let next_new = ref 0 in
    for idx = 0 to n - 1 do
      let canonical = old_to_canonical.(idx) in
      if not (Hashtbl.mem canonical_to_new canonical) then begin
        Hashtbl.add canonical_to_new canonical !next_new;
        incr next_new
      end
    done;
    let old_to_new = Array.init n (fun idx ->
      match Hashtbl.find_opt canonical_to_new old_to_canonical.(idx) with
      | Some new_idx -> new_idx
      | None -> idx)
    in
    (* Rewrite all refs *)
    let rewrite_ref s =
      let len = String.length s in
      if len > 1 && s.[0] = '#' then
        let idx_str = String.sub s 1 (len - 1) in
        (try
          let idx = int_of_string idx_str in
          if idx >= 0 && idx < n then
            "#" ^ string_of_int old_to_new.(idx)
          else s
        with Failure _ -> s)
      else s
    in
    let rec rewrite_sexp = function
      | Sexp.Atom s -> Sexp.Atom (rewrite_ref s)
      | Sexp.List items -> Sexp.List (List.map rewrite_sexp items)
    in
    (* Build new types preamble *)
    let new_n = !next_new in
    let new_types = Array.make new_n (Sexp.atom "_") in
    for idx = 0 to n - 1 do
      let canonical = old_to_canonical.(idx) in
      if canonical = idx then begin
        match Hashtbl.find_opt canonical_to_new canonical with
        | Some new_idx -> new_types.(new_idx) <- rewrite_sexp arr.(idx)
        | None -> ()
      end
    done;
    let items = ref [] in
    for i = new_n - 1 downto 0 do
      items := Sexp.list [Sexp.atom (string_of_int i); new_types.(i)] :: !items
    done;
    let preamble = Sexp.list (Sexp.atom "types" :: !items) in
    let body = rewrite_sexp body in
    (preamble, body)
  end

let print_typed_structure ppf str =
  reset_dedup ();
  let body = structure ~with_locs:false str in
  let (preamble, body) = normalize_types_and_body body in
  Format.fprintf ppf "%s\n%s" (Sexp.to_string preamble) (Sexp.to_string body)

let print_typed_structure_with_locs ppf str =
  reset_dedup ();
  let body = structure ~with_locs:true str in
  let (preamble, body) = normalize_types_and_body body in
  Format.fprintf ppf "%s\n%s" (Sexp.to_string preamble) (Sexp.to_string body)

let print_typed_signature ppf sg =
  reset_dedup ();
  let body = signature ~with_locs:false sg in
  let (preamble, body) = normalize_types_and_body body in
  Format.fprintf ppf "%s\n%s" (Sexp.to_string preamble) (Sexp.to_string body)

let print_typed_signature_with_locs ppf sg =
  reset_dedup ();
  let body = signature ~with_locs:true sg in
  let (preamble, body) = normalize_types_and_body body in
  Format.fprintf ppf "%s\n%s" (Sexp.to_string preamble) (Sexp.to_string body)
