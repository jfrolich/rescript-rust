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

@law
let appendNil = (xs: list<int>) => append(xs, list{}) == xs

@law
let lengthAppend = (xs: list<string>, ys: list<string>) =>
  length(append(xs, ys)) == length(xs) + length(ys)
