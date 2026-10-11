type rec eq<'a, 'b> = Refl: eq<[< #a | #b], 'a>

let f: type a. eq<a, int> => int = x =>
  switch x {
  | Refl => 0
  }

let x: string = 1
