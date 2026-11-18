type rec eq<_, _> = Refl: eq<'a, 'a>
let f = (type a, w: eq<a, int>, y: a) => switch w { | Refl => { let g = (z: a) => z; g(y) } }
