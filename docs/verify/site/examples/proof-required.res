let rec sum = xs =>
  switch xs {
  | list{} => 0
  | list{x, ...rest} => x + sum(rest)
  }

let rec append = (xs, ys) =>
  switch xs {
  | list{} => ys
  | list{x, ...rest} => list{x, ...append(rest, ys)}
  }

@law(proved)
let sumAppend = (xs: list<int>, ys: list<int>) => sum(append(xs, ys)) == sum(xs) + sum(ys)

// The standard library is another file: this law can be run, not proved.
@law(proved)
let reverseKeepsSum = (xs: list<int>) => sum(List.reverse(xs)) == sum(xs)
