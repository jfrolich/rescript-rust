(* Sexp printer for Typedtree - used for parity testing between OCaml and Rust compilers *)

open Asttypes
open Typedtree

(* Sexp module - simple string-based pretty printing *)
module Sexp = struct
  type t = Atom of string | List of t list

  let atom s = Atom s
  let list l = List l

  (* Simple pretty printer without Res_doc dependency. It writes into one
     buffer: building the string by concatenation at every level is quadratic
     in the nesting depth (a large character-range pattern nests thousands of
     or-patterns). *)
  let rec add_indent buf indent t =
    match t with
    | Atom s -> Buffer.add_string buf s
    | List [] -> Buffer.add_string buf "()"
    | List [Atom s] ->
      Buffer.add_char buf '(';
      Buffer.add_string buf s;
      Buffer.add_char buf ')'
    | List [sexpr] ->
      Buffer.add_char buf '(';
      add_indent buf indent sexpr;
      Buffer.add_char buf ')'
    | List (first :: rest) ->
      Buffer.add_char buf '(';
      add_indent buf (indent + 1) first;
      List.iter
        (fun item ->
          Buffer.add_char buf '\n';
          Buffer.add_string buf (String.make ((indent * 2) + 2) ' ');
          add_indent buf (indent + 1) item)
        rest;
      Buffer.add_char buf ')'

  let to_string sexpr =
    let buf = Buffer.create 4096 in
    add_indent buf 0 sexpr;
    Buffer.contents buf
end

(* Helper functions *)
let string txt = Sexp.atom ("\"" ^ txt ^ "\"")

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
  | Path.Pident id -> Sexp.list [Sexp.atom "Pident"; string (Ident.unique_toplevel_name id)]
  | Path.Pdot (p, s, _) -> Sexp.list [Sexp.atom "Pdot"; path p; string s]
  | Path.Papply (p1, p2) -> Sexp.list [Sexp.atom "Papply"; path p1; path p2]

(* Longident printer *)
let rec longident l =
  match l with
  | Longident.Lident s -> Sexp.list [Sexp.atom "Lident"; string s]
  | Longident.Ldot (l, s) -> Sexp.list [Sexp.atom "Ldot"; longident l; string s]

let longident_loc li = longident li.txt

(* Ident printer - name/stamp for full parity *)
let ident id = string (Ident.unique_toplevel_name id)

(* Constant printer *)
let constant c =
  match c with
  | Const_int i -> Sexp.list [Sexp.atom "Const_int"; Sexp.atom (string_of_int i)]
  | Const_char c -> Sexp.list [Sexp.atom "Const_char"; Sexp.atom (Printf.sprintf "%d" c)]
  | Const_string s -> Sexp.list [Sexp.atom "Const_string"; string s]
  | Const_float s -> Sexp.list [Sexp.atom "Const_float"; string s]
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

(* Type expression serializer.

   Types are serialized inline at each typedtree occurrence:
   - non-cyclic sharing is serialized structurally
   - Tvar/Tunivar identity is preserved via normalized local ids
   - real recursion is preserved with inline mu/ref binders

   This keeps parity focused on the final semantic type shape rather than the
   allocator/copy strategy used to build it, without a file-global preamble. *)

type active_mu_binding = {
  id: int;
  mutable used: bool;
}

type type_sexp_state = {
  tvars: (int, int) Hashtbl.t;
  tunivars: (int, int) Hashtbl.t;
  active_bindings: (int, active_mu_binding) Hashtbl.t;
  mutable next_tvar_id: int;
  mutable next_tunivar_id: int;
  mutable next_mu_id: int;
}

let new_type_sexp_state () = {
  tvars = Hashtbl.create 16;
  tunivars = Hashtbl.create 16;
  active_bindings = Hashtbl.create 16;
  next_tvar_id = 0;
  next_tunivar_id = 0;
  next_mu_id = 0;
}

let next_tvar_id state te =
  match Hashtbl.find_opt state.tvars te.Types.id with
  | Some id -> id
  | None ->
    let id = state.next_tvar_id in
    state.next_tvar_id <- id + 1;
    Hashtbl.add state.tvars te.Types.id id;
    id

let next_tunivar_id state te =
  match Hashtbl.find_opt state.tunivars te.Types.id with
  | Some id -> id
  | None ->
    let id = state.next_tunivar_id in
    state.next_tunivar_id <- id + 1;
    Hashtbl.add state.tunivars te.Types.id id;
    id

let rec type_expr_inline state te =
  let te = Btype.repr te in
  match te.Types.desc with
  | Tvar _ ->
    let id = next_tvar_id state te in
    Sexp.list [Sexp.atom "Tvar"; Sexp.atom (string_of_int id)]
  | Tunivar _ ->
    let id = next_tunivar_id state te in
    Sexp.list [Sexp.atom "Tunivar"; Sexp.atom (string_of_int id)]
  | _ -> (
    match Hashtbl.find_opt state.active_bindings te.Types.id with
    | Some binding ->
      binding.used <- true;
      Sexp.list [Sexp.atom "ref"; Sexp.atom (string_of_int binding.id)]
    | None ->
      let binding = {id = state.next_mu_id; used = false} in
      state.next_mu_id <- state.next_mu_id + 1;
      Hashtbl.add state.active_bindings te.Types.id binding;
      let sexp = type_expr_body_inline state te in
      Hashtbl.remove state.active_bindings te.Types.id;
      if binding.used then
        Sexp.list [Sexp.atom "mu"; Sexp.atom (string_of_int binding.id); sexp]
      else
        sexp)

and type_expr_body_inline state te =
  (* All recursive calls use let-bindings to ensure deterministic left-to-right
     evaluation order. OCaml's ocamlopt uses unspecified order for list literal
     elements, so inlining type_expr_inline in [...] would give inconsistent
     ordering. *)
  match te.Types.desc with
  | Tvar _ | Tunivar _ -> assert false
  | Tarrow (args, ret) ->
    let args_sexp =
      List.map
        (fun arg ->
          Sexp.list [sexp_arg_label arg.Types.lbl; type_expr_inline state arg.Types.typ])
        args
    in
    let ret_sexp = type_expr_inline state ret in
    Sexp.list (Sexp.atom "Tarrow" :: args_sexp @ [ret_sexp])
  | Ttuple l ->
    let items = List.map (type_expr_inline state) l in
    Sexp.list (Sexp.atom "Ttuple" :: items)
  | Tconstr (p, args, _) ->
    let arg_sexps = List.map (type_expr_inline state) args in
    Sexp.list [Sexp.atom "Tconstr"; path p; Sexp.list arg_sexps]
  | Tobject ty ->
    let ty_sexp = type_expr_inline state ty in
    Sexp.list [Sexp.atom "Tobject"; ty_sexp]
  | Tfield {name; mutability; typ = ty1; rest = ty2} ->
    let mutability_str =
      match Btype.mutability_repr mutability with
      | Immutable -> "Immutable"
      | Mutable -> "Mutable"
    in
    let ty1_sexp = type_expr_inline state ty1 in
    let ty2_sexp = type_expr_inline state ty2 in
    Sexp.list
      [Sexp.atom "Tfield"; string name; Sexp.atom mutability_str; ty1_sexp; ty2_sexp]
  | Tnil -> Sexp.atom "Tnil"
  | Tlink _ -> Sexp.atom "Tlink"  (* Should not happen after Btype.repr *)
  | Tsubst ty ->
    let ty_sexp = type_expr_inline state ty in
    Sexp.list [Sexp.atom "Tsubst"; ty_sexp]
  | Tvariant row -> row_desc_sexp state row
  | Tpoly (ty, tyl) ->
    let ty_sexp = type_expr_inline state ty in
    let tyl_sexps = List.map (type_expr_inline state) tyl in
    Sexp.list [Sexp.atom "Tpoly"; ty_sexp; Sexp.list tyl_sexps]
  | Tpackage (p, lids, tyl) ->
    let tyl_sexps = List.map (type_expr_inline state) tyl in
    Sexp.list [
      Sexp.atom "Tpackage";
      path p;
      Sexp.list (List.map (fun l -> longident l) lids);
      Sexp.list tyl_sexps;
    ]

and type_expr te =
  let state = new_type_sexp_state () in
  type_expr_inline state te

and row_desc_sexp state row =
  let row = Btype.row_repr row in
  let fields_sexp = Sexp.list (List.map (fun (l, rf) ->
    let rf_sexp = row_field_sexp state rf in
    Sexp.list [string l; rf_sexp]
  ) row.Types.row_fields) in
  Sexp.list [
    Sexp.atom "Tvariant";
    fields_sexp;
    Sexp.atom (if row.Types.row_closed then "closed" else "open");
    Sexp.atom (if row.Types.row_fixed then "fixed" else "not_fixed");
  ]

and row_field_sexp state rf =
  match Btype.row_field_repr rf with
  | Rpresent None -> Sexp.atom "Rpresent_none"
  | Rpresent (Some ty) ->
    let ty_sexp = type_expr_inline state ty in
    Sexp.list [Sexp.atom "Rpresent"; ty_sexp]
  | Reither (c, tyl, _, _) ->
    let tyl_sexp = Sexp.list (List.map (type_expr_inline state) tyl) in
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
  | Tpat_interval (c1, c2) ->
    Sexp.list [Sexp.atom "Tpat_interval"; constant c1; constant c2]
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
  | Tpat_record (fields, flag, _rest) ->
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
  | Tpat_dict entries ->
    let entry {tdp_key; tdp_pattern; tdp_optional} =
      Sexp.list
        [
          string tdp_key.txt;
          pattern ~with_locs tdp_pattern;
          Sexp.atom (string_of_bool tdp_optional);
        ]
    in
    Sexp.list (Sexp.atom "Tpat_dict" :: List.map entry entries)
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
  | Texp_coerce {source_type; target; target_type} ->
    let source_sexp = Sexp.list [Sexp.atom "source"; type_expr source_type] in
    let ct_sexp = core_type ~with_locs target in
    let target_sexp = Sexp.list [Sexp.atom "target"; type_expr target_type] in
    Sexp.list
      ([Sexp.atom "Texp_coerce"; source_sexp; ct_sexp; target_sexp]
      @ loc_sexp @ [attrs_sexp])
  | Texp_open (flag, p, _, _) ->
    Sexp.list ([Sexp.atom "Texp_open"; override_flag flag; path p] @ loc_sexp @ [attrs_sexp])

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
  | Texp_function { params; body; async } ->
    let params_sexp =
      List.map
        (fun (fp : function_param) ->
          Sexp.list [
            sexp_arg_label fp.fp_lbl;
            ident fp.fp_param;
            pattern ~with_locs fp.fp_pat;
            partial fp.fp_partial;
          ])
        params
    in
    let body_sexp = expression ~with_locs body in
    Sexp.list [
      Sexp.atom "Texp_function";
      Sexp.list params_sexp;
      body_sexp;
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
  | Texp_try (e, cases, finally) ->
    let e_sexp = expression ~with_locs e in
    let cases_sexp = Sexp.list (List.map (case ~with_locs) cases) in
    let finally_sexp = opt (expression ~with_locs) finally in
    Sexp.list [
      Sexp.atom "Texp_try";
      e_sexp;
      cases_sexp;
      finally_sexp;
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
    let fields_sexp = Sexp.list (Array.to_list (Array.map (fun (ld, li, e) ->
      let e_sexp = expression ~with_locs e in
      Sexp.list [string ld.Types.lbl_name; longident_loc li; e_sexp]
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
  | Texp_dict entries ->
    let entry = function
      | Tdict_entry (key, e) ->
        Sexp.list
          [Sexp.atom "Tdict_entry"; string key.txt; expression ~with_locs e]
      | Tdict_spread e ->
        Sexp.list [Sexp.atom "Tdict_spread"; expression ~with_locs e]
    in
    Sexp.list (Sexp.atom "Texp_dict" :: List.map entry entries)
  | Texp_spread (kind, parts) ->
    let kind =
      match kind with
      | Spread_array -> "Spread_array"
      | Spread_list -> "Spread_list"
    in
    let parts = List.map (expression ~with_locs) parts in
    Sexp.list (Sexp.atom "Texp_spread" :: Sexp.atom kind :: parts)
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
  | Texp_object_get (e, {txt = name; _}) ->
    let e_sexp = expression ~with_locs e in
    Sexp.list [Sexp.atom "Texp_object_get"; e_sexp; string name]
  | Texp_object_set (e1, {txt = name; _}, e2) ->
    let e1_sexp = expression ~with_locs e1 in
    let e2_sexp = expression ~with_locs e2 in
    Sexp.list [Sexp.atom "Texp_object_set"; e1_sexp; string name; e2_sexp]
  | Texp_object_literal fields ->
    Sexp.list
      (Sexp.atom "Texp_object_literal"
      :: List.map
           (fun ((s : string Asttypes.loc), e) ->
             Sexp.list [string s.txt; expression ~with_locs e])
           fields)
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
  | Texp_break -> Sexp.list [Sexp.atom "Texp_break"]
  | Texp_continue -> Sexp.list [Sexp.atom "Texp_continue"]
  | Texp_for_of _ -> Sexp.list [Sexp.atom "Texp_for_of"]
  | Texp_for_await_of _ -> Sexp.list [Sexp.atom "Texp_for_await_of"]
  | Texp_tagged_template {tag; raw_sources; values} ->
    let tag_sexp = expression ~with_locs tag in
    let values_sexp = List.map (expression ~with_locs) values in
    Sexp.list
      [
        Sexp.atom "Texp_tagged_template";
        tag_sexp;
        Sexp.list (List.map string raw_sources);
        Sexp.list values_sexp;
      ]
  | Texp_template {segments; values} ->
    let values_sexp = List.map (expression ~with_locs) values in
    Sexp.list
      [
        Sexp.atom "Texp_template";
        Sexp.list
          (List.map
             (fun segment ->
               Sexp.list
                 [
                   string (String_literal.template_source segment);
                   string (String_literal.template_semantic segment);
                 ])
             segments);
        Sexp.list values_sexp;
      ]

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
  | Ttyp_arrow (args, ret) ->
    let args_sexp =
      List.map
        (fun (arg : Typedtree.arg) ->
          Sexp.list [
            sexp_arg_label arg.lbl;
            attributes ~with_locs arg.attrs;
            core_type ~with_locs arg.typ;
          ])
        args
    in
    let ret_sexp = core_type ~with_locs ret in
    Sexp.list (Sexp.atom "Ttyp_arrow" :: args_sexp @ [ret_sexp])
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
    Sexp.list
      (Sexp.atom "prim"
      :: List.map string
           (match vd.val_prim with
           | None -> []
           | Some prim -> Ffi_debug.primitive_repr prim));
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
  let attrs_sexp = attributes ~with_locs od.open_attributes in
  Sexp.list ([
    Sexp.atom "open_description";
    path od.open_path;
    longident_loc od.open_txt;
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
let print_typed_structure ppf str =
  let body = structure ~with_locs:false str in
  Format.fprintf ppf "%s" (Sexp.to_string body)

let print_typed_structure_with_locs ppf str =
  let body = structure ~with_locs:true str in
  Format.fprintf ppf "%s" (Sexp.to_string body)

let print_typed_signature ppf sg =
  let body = signature ~with_locs:false sg in
  Format.fprintf ppf "%s" (Sexp.to_string body)

let print_typed_signature_with_locs ppf sg =
  let body = signature ~with_locs:true sg in
  Format.fprintf ppf "%s" (Sexp.to_string body)
