(* Typed artifacts served by a running `rescript watch`.

   In-process builds write no .cmi/.cmt/.cmti files. A watcher keeps them in
   memory and serves them on a local port (rewatch/src/tooling_server.rs):
   `lib/rescript-watch.addr` in the watched project holds `<host:port>
   <token>`. A client sends `AUTH <token>`, then `GET <path>` for the
   artifact a file-backed build would have written at <path>; the reply is
   `OK <length>` followed by the bytes, or `MISSING`. *)

let address_file_name = "rescript-watch.addr"

type connection = {ic: in_channel; oc: out_channel}

(* Watchers by address file; [None] once a connection failed. *)
let connections : (string, connection option) Hashtbl.t = Hashtbl.create 1

(* The address file governing a directory, by directory. *)
let address_files : (string, string option) Hashtbl.t = Hashtbl.create 16

let rec find_address_file dir =
  match Hashtbl.find_opt address_files dir with
  | Some found -> found
  | None ->
    let candidate = Filename.concat (Filename.concat dir "lib") address_file_name in
    let found =
      if Sys.file_exists candidate then Some candidate
      else
        let parent = Filename.dirname dir in
        if parent = dir then None else find_address_file parent
    in
    Hashtbl.replace address_files dir found;
    found

let read_reply ic =
  let header = input_line ic in
  match String.split_on_char ' ' (String.trim header) with
  | ["OK"; length] -> Some (really_input_string ic (int_of_string length))
  | _ -> None

let connect address_file =
  match Hashtbl.find_opt connections address_file with
  | Some connection -> connection
  | None ->
    let connection =
      try
        let content =
          let ic = open_in address_file in
          Fun.protect ~finally:(fun () -> close_in ic) (fun () -> input_line ic)
        in
        match String.split_on_char ' ' (String.trim content) with
        | [address; token] -> (
          match String.rindex_opt address ':' with
          | None -> None
          | Some colon ->
            let host = String.sub address 0 colon in
            let port =
              int_of_string
                (String.sub address (colon + 1)
                   (String.length address - colon - 1))
            in
            let ic, oc =
              Unix.open_connection
                (Unix.ADDR_INET (Unix.inet_addr_of_string host, port))
            in
            output_string oc ("AUTH " ^ token ^ "\n");
            flush oc;
            match read_reply ic with
            | Some _ -> Some {ic; oc}
            | None ->
              Unix.shutdown_connection ic;
              None)
        | _ -> None
      with _ -> None
    in
    Hashtbl.replace connections address_file connection;
    connection

let artifacts : (string, string option) Hashtbl.t = Hashtbl.create 64

(* Roots of the projects being edited. A dependency's artifact may live
   outside the watched project (e.g. hoisted into a parent node_modules), so
   its own directories need not lead to the watcher. *)
let project_roots : string list ref = ref []

let add_project_root root =
  if not (List.mem root !project_roots) then
    project_roots := !project_roots @ [root]

let watcher_for path =
  match find_address_file (Filename.dirname path) with
  | Some _ as found -> found
  | None -> List.find_map find_address_file !project_roots

(* The bytes of the artifact at [path], if a watcher serves it. *)
let get path =
  let path =
    if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path
    else path
  in
  match Hashtbl.find_opt artifacts path with
  | Some bytes -> bytes
  | None ->
    let bytes =
      match watcher_for path with
      | None -> None
      | Some address_file -> (
        match connect address_file with
        | None -> None
        | Some {ic; oc} -> (
          try
            output_string oc ("GET " ^ path ^ "\n");
            flush oc;
            read_reply ic
          with _ ->
            Hashtbl.replace connections address_file None;
            None))
    in
    Hashtbl.replace artifacts path bytes;
    bytes

(* [Cmt_format.read] over bytes instead of a file: a .cmt, or a .cmi
   optionally followed by the .cmt part. *)
let read_artifact bytes =
  let magic_length = String.length Config.cmi_magic_number in
  if String.length bytes < magic_length then None
  else
    let magic = String.sub bytes 0 magic_length in
    let next_value pos =
      let value = Marshal.from_string bytes pos in
      (value, pos + Marshal.total_size (Bytes.unsafe_of_string bytes) pos)
    in
    if magic = Config.cmt_magic_number then
      Some (None, Some (fst (next_value magic_length) : Cmt_format.cmt_infos))
    else if magic = Config.cmi_magic_number then
      let (name, sign), pos = next_value magic_length in
      let crcs, pos = next_value pos in
      let flags, pos = next_value pos in
      let cmi =
        {
          Cmi_format.cmi_name = name;
          cmi_sign = sign;
          cmi_crcs = crcs;
          cmi_flags = flags;
        }
      in
      let cmt =
        if
          String.length bytes >= pos + magic_length
          && String.sub bytes pos magic_length = Config.cmt_magic_number
        then Some (fst (next_value (pos + magic_length)) : Cmt_format.cmt_infos)
        else None
      in
      Some (Some cmi, cmt)
    else None

let exists path = get path <> None || Sys.file_exists path

(* The artifact paths served by the watcher governing [dir], canonical. *)
let list ~dir =
  match
    match find_address_file dir with
    | Some _ as found -> found
    | None -> List.find_map find_address_file !project_roots
  with
  | None -> []
  | Some address_file -> (
    match connect address_file with
    | None -> []
    | Some {ic; oc} -> (
      try
        output_string oc "LIST\n";
        flush oc;
        match read_reply ic with
        | None -> []
        | Some listing ->
          String.split_on_char '\n' listing |> List.filter (fun p -> p <> "")
      with _ ->
        Hashtbl.replace connections address_file None;
        []))

let canonical path = try Unix.realpath path with _ -> path

let read_cmt path =
  match get path with
  | None -> None
  | Some bytes -> (
    match read_artifact bytes with
    | Some (_, Some cmt) -> Some cmt
    | _ -> None)

let read_cmi path =
  match get path with
  | None -> None
  | Some bytes -> (
    match read_artifact bytes with
    | Some (Some cmi, _) -> Some cmi
    | _ -> None)

(* [Cmt_format.read_cmt], preferring the artifact a watcher serves. *)
let read_cmt_or_file path =
  match read_cmt path with
  | Some cmt -> cmt
  | None -> Cmt_format.read_cmt path
