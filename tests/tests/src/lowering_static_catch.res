@val external ext: int => int = "ext"
@val external big: (int, int, int) => int = "big"

// The handler of the shared action is a function that holds a static catch
// of its own. No exit leaves a function, so the handler follows the body of
// the outer match without an `exit` variable.
let handlerIsClosureWithCatch = (x, y, z) =>
  switch (x, y) {
  | (1, _) | (_, 2) =>
    () =>
      switch (z, y) {
      | (3, _) | (_, 4) => big(big(1, 2, 3), big(4, 5, 6), big(7, 8, 9))
      | _ => ext(2)
      }
  | _ => () => ext(3)
  }

// The guarded match is compiled inside the body of the outer match's static
// catch. Its default action is reached from the guard's handler as well, so
// both of its catches take an `exit` variable.
let catchUnderCatch = (x, y, z, w, g) =>
  switch (x, y) {
  | (1, _) | (_, 2) => big(big(1, 2, 3), big(4, 5, 6), big(7, 8, 9))
  | _ =>
    switch (z, w) {
    | (3, _) | (_, 4) if g => big(big(11, 12, 13), big(14, 15, 16), big(17, 18, 19))
    | _ => big(big(21, 22, 23), big(24, 25, 26), big(27, 28, 29))
    }
  }
