module R = {
  type t = ..
  type t += C({v: int, w: int})
}
let c = R.C({w: 1})
