type rec eq<_, _> = Refl: eq<'a, 'a>
type t
let f = (w: eq<t, int>, v: t): int => switch w { | Refl => v }
