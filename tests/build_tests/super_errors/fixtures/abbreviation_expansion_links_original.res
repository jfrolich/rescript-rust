type id<'a> = 'a
let mk = (): id<(int, int)> => (1, 2)
let f = (a, b) => {
  let _ = [a, mk()]
  let _ = [b, mk()]
  let _ = [a, b]
  let z: string = b
  z
}
