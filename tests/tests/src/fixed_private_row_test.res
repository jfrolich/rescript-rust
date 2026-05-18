type t = private [< #A | #B]

module type S = {
  type u = private [< #C | #D]
}
