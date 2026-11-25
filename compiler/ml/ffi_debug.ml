(* Fork-only: a deterministic textual rendering of an import source, used by
   the sexp debugging printers. *)

open External_ffi_types

let list f xs = "[" ^ String.concat ";" (List.map f xs) ^ "]"
let quote s = Printf.sprintf "%S" s

let pairs xs = list (fun (a, b) -> "(" ^ quote a ^ "," ^ quote b ^ ")") xs

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

let import_source : Lambda.import_source -> string = function
  | Import_module {module_; path} ->
    "Import_module(" ^ Ident.name module_ ^ "," ^ list quote path ^ ")"
  | Import_external {module_; path} ->
    "Import_external(" ^ module_name module_ ^ "," ^ list quote path ^ ")"
