module M: {
  type t = private int
  let v: t
} = {
  type t = int
  let v = 1
}
let f = () => "s" === (M.v :> int)
