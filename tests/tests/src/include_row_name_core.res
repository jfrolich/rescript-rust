module Shadow = {
  type box
  type t<'a> = [#shadow(string) | #none]
  let toString: t<'a> => string = x =>
    switch x {
    | #shadow(x) => x
    | #none => "none"
    }
}
let boxShadows = x => x->List.map(Shadow.toString)->List.length
