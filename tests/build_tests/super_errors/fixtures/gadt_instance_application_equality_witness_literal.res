type rec eq<_, _> = Refl: eq<'a, 'a>
let f = (type a, w: eq<a, string>, y: a) => switch w { | Refl => ((z: a) => z)(y) }
