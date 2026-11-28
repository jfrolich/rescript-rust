let rec append = (xs, ys) =>
  switch xs {
  | list{} => ys
  | list{x, ...rest} => list{x, ...append(rest, ys)}
  }

let rec length = xs =>
  switch xs {
  | list{} => 0
  | list{_, ...rest} => 1 + length(rest)
  }

let rec reverse = xs =>
  switch xs {
  | list{} => list{}
  | list{x, ...rest} => append(reverse(rest), list{x})
  }

@law
let appendNil = (xs: list<int>) => append(xs, list{}) == xs

@law
let appendAssoc = (xs: list<int>, ys: list<int>, zs: list<int>) =>
  append(append(xs, ys), zs) == append(xs, append(ys, zs))

@law
let lengthAppend = (xs: list<string>, ys: list<string>) =>
  length(append(xs, ys)) == length(xs) + length(ys)

@law
let reverseAppend = (xs: list<int>, ys: list<int>) =>
  reverse(append(xs, ys)) == append(reverse(ys), reverse(xs))

@law(proved)
let reverseTwice = (xs: list<int>) => reverse(reverse(xs)) == xs

// The standard library is another file: this law is run, not proved.
@law
let reverseKeepsLength = (xs: list<int>) => List.length(List.reverse(xs)) == List.length(xs)

// And a run is not enough for a law that asks for a proof.
@law(proved)
let libraryReverseTwice = (xs: list<int>) => List.reverse(List.reverse(xs)) == xs
