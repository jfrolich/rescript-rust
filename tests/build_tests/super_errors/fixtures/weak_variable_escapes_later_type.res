// A weak variable keeps the level of the structure item that created it,
// which is below the binding time of a type declared by a later item:
// lowering `t` to that level must report the escape.
let r = ref(None)
type t = A
let () = r := Some(A)
