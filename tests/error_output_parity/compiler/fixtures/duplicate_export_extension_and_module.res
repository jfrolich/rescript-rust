type t<'a> = ..
type t<'a> += M: t<int>
module M = {
  let x = 1
}
