module R = {
  exception E({v: int})
}
open R
let e = E(1)
