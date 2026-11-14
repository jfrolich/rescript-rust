// The interface instantiates the weak variable of `r` to the abstract `t`
// declared before it; the implementation must be accepted.
type t
let r = ref(None)
let v = r.contents
