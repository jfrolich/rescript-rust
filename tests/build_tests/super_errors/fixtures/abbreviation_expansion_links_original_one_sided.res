type id<'a> = 'a
let mk = (): id<(int, int)> => (1, 2)
let pl = (): (int, int) => (1, 2)
let f = (a, b) => {
  let _ = [a, pl()]
  let _ = [b, mk()]
  let _ = [b, a]
  let z: string = a
  z
}
