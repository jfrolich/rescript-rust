@@warning("A")
@internal.local
module P1 = {
  exception A
}
open! P1
let f = () => throw(A)
