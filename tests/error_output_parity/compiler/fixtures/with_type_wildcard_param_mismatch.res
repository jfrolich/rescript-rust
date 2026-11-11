module type S = {
  type t<'a, 'b>
  let x: t<int, string>
}
module M: S with type t<_, 'b> = list<'b> = {
  type t<'a, 'b> = array<'b>
  let x = ["s"]
}
