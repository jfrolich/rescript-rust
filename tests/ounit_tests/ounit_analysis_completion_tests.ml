let ( >:: ), ( >::: ) = OUnit.(( >:: ), ( >::: ))

(* The parsed expression of [let x = <source>]. *)
let parsed_expression source =
  let parsed =
    Res_driver.parse_implementation_from_source ~display_filename:"Todo.res"
      ~source
  in
  OUnit.assert_bool "expected valid ReScript source" (not parsed.invalid);
  match parsed.parsetree with
  | [{Parsetree.pstr_desc = Pstr_value (_, [{pvb_expr}])}] -> pvb_expr
  | _ -> OUnit.assert_failure "Expected one let binding"

(* What completion finds with the cursor right after the extension name,
   which ends at column [name_end] of the only line. *)
let completable source ~name_end =
  match
    Analysis.Completion_front_end.completion_with_parser ~debug:false ~source
      ~kind_file:Analysis.Files.Res ~pos_cursor:(0, name_end)
  with
  | Some (completable, _scope) ->
    Analysis.Shared_types.Completable.to_string completable
  | None -> "None"

let suites =
  __FILE__
  >::: [
         ( "completion at %todo is the extension node todo" >:: fun _ ->
           List.iter
             (fun (source, name_end, node) ->
               let expression = parsed_expression source in
               (* The parser gives a todo node, or keeps the extension for a
                  payload that is not a message. *)
               OUnit.assert_equal ~printer:Fun.id node
                 (Analysis.Utils.identify_pexp expression.pexp_desc);
               OUnit.assert_equal ~printer:Fun.id ~msg:source
                 "CextensionNode(todo)"
                 (completable source ~name_end))
             [
               ("let a = %todo", 13, "Pexp_todo");
               ("let a = %todo(\"message\")", 13, "Pexp_todo");
               ("let a = %todo(`template`)", 13, "Pexp_todo");
               ("let a = @attr %todo(\"x\")", 19, "Pexp_todo");
               ("let a = %todo(1)", 13, "Pexp_extension");
               ("let a = %todo(@attr \"x\")", 13, "Pexp_extension");
             ] );
         ( "completion at another extension is its name" >:: fun _ ->
           OUnit.assert_equal ~printer:Fun.id "CextensionNode(todx)"
             (completable "let a = %todx" ~name_end:13);
           OUnit.assert_equal ~printer:Fun.id "CextensionNode(raw)"
             (completable "let a = %raw(\"1\")" ~name_end:12) );
       ]
