module M: {
  let g: int => int
} = {
  type a = A | B | C
  type b = a = A | B | C
  let classify = (x: b) =>
    switch x {
    | A => 1
    | B | C => 2
    }
  let g = n => classify(n > 0 ? A : A)
}
