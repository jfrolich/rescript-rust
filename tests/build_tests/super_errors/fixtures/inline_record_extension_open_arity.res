module R = {
  exception E({v: int, w: string})
}
open R
let e = E({v: 1, w: ""}, 2)
