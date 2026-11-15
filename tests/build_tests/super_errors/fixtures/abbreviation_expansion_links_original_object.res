type id<'a> = 'a
let mk = (): id<{"x": int}> => {"x": 1}
let f = (a, b) => {
  let _ = [a, mk()]
  let _ = [b, mk()]
  let _ = [a, b]
  let z: string = b
  z
}
