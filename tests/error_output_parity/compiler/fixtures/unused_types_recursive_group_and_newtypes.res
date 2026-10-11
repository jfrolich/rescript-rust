module M: {
  let f: int => int
} = {
  type rec a = A(b) | Nil
  and b = B(a)
  type rec c = C(c) | D
  type e = E
  type used = U
  let f = x => {
    let _ = U
    let g = (type t, y: t) => y
    let h = (type s, y) => y
    let _ = (g, h)
    switch E {
    | E => x
    }
  }
}
