// Applications inside a case whose result does not leave the equation:
// both compilers accept them (the refused ones are the super_errors
// fixtures gadt_instance_application_*).

module AppliedLiteralAnnotated = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a): a => switch x { | Int => ((z: a) => z)(y) }
}

module LetFunctionAnnotated = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a): a => switch x { | Int => { let g = (z: a) => z; g(y) } }
}

module LetFunctionArray = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (z: a) => [z]; g(y) } }
}

module IdentOnly = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) => switch x { | Int => y }
}

module IfElseAnnotated = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a): a => switch x { | Int => { let g = (z: a) => z; if true { g(y) } else { 0 } } }
}

module EqualityWitnessAnnotated = {
  type rec eq<_, _> = Refl: eq<'a, 'a>
  let f = (type a, w: eq<a, int>, y: a): a => switch w { | Refl => { let g = (z: a) => z; g(y) } }
}

module FunctionReturned = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, _y: a) => switch x { | Int => (z: a) => z }
}

module FunctionReturnedAppliedOutside = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) => { let h = switch x { | Int => (z: a) => z }; h(y) }
}

module NestedTwoEquations = {
  type rec t<_> = Int: t<int>
  type rec s<_> = Str: s<string>
  let f = (type a b, x: t<a>, w: s<b>, y: a, v: b) =>
    switch x {
    | Int => switch w { | Str => { let g = (z: a, u: b) => (z, u); g(y, v) } }
    }
}

module ObjectField = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (z: a) => {"v": z}; g(y)["v"] } }
}

module RecordField = {
  type rec t<_> = Int: t<int>
  type box<'x> = {v: 'x}
  let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (z: a) => {v: z}; g(y).v } }
}

module TupleAnnotatedResult = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (z: a) => ((z: a), 1); g(y) } }
}

module AfterPlainFunctionAnnotated = {
  type rec t<_> = Int: t<int>
  let h = (o: option<int>) => switch o { | Some(n) => n | None => 0 }
  let f = (type a, x: t<a>, y: a): a => switch x { | Int => { let g = (z: a) => z; g(y) } }
}

module PolyvariantPayload = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (z: a) => #V(z); g(y) } }
}
