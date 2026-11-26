// Object and variant comparisons inside a case that both compilers accept:
// the instance does not leave its equation, or no row of the outer level is
// unified with it (the refused ones are the super_errors fixtures
// gadt_instance_row_*).

module VariantRight = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, v: [> #A(int)]) =>
    switch x {
    | Int => v === #A(y)
    }
}

module ObjectClosed = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, o: {"f": int}) =>
    switch x {
    | Int => {"f": y} === o
    }
}

module VariantTagOnOneSide = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, v: [> #B]) =>
    switch x {
    | Int => #A(y) === v
    }
}

module ObjectIntUse = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, o: {.."f": int}) =>
    switch x {
    | Int => {"f": y + 1} === o
    }
}

module ObjectFieldAnnotated = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, o: {.."f": int}) =>
    switch x {
    | Int => {"f": (y: int)} === o
    }
}

module VariantClosed = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, v: [#A(int)]) =>
    switch x {
    | Int => #A(y) === v
    }
}

module VariantResultAnnotated = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a): [> #A(int)] =>
    switch x {
    | Int => #A(y)
    }
}

module VariantIntUse = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, v: [> #A(int)]) =>
    switch x {
    | Int => #A(y + 1) === v
    }
}

module VariantPayloadAnnotated = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, v: [> #A(int)]) =>
    switch x {
    | Int => #A((y: int)) === v
    }
}

module VariantUpperBoundFunction = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, v: [< #A(int) | #B]) =>
    switch x {
    | Int => {
        let k = (w: [< #A(a) | #B]) => w === v
        k
      }
    }
}

module ObjectOperandAnnotated = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, o: {.."f": int}) =>
    switch x {
    | Int => ({"f": y}: {.."f": int}) === o
    }
}

module VariantOperandAnnotated = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, v: [> #A(int)]) =>
    switch x {
    | Int => (#A(y): [> #A(int)]) === v
    }
}
