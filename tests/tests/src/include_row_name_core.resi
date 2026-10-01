module Shadow: {
  type box
  type t<'a> = [#shadow(string) | #none]
  let toString: t<'a> => string
}
let boxShadows: list<[Shadow.t<Shadow.box>]> => int
