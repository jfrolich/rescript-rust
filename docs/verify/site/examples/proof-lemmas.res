let rec append = (xs, ys) =>
  switch xs {
  | list{} => ys
  | list{x, ...rest} => list{x, ...append(rest, ys)}
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
let reverseAppend = (xs: list<int>, ys: list<int>) =>
  reverse(append(xs, ys)) == append(reverse(ys), reverse(xs))

@law
let reverseTwice = (xs: list<int>) => reverse(reverse(xs)) == xs
