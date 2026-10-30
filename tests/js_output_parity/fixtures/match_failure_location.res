// Every non-exhaustive match raises Match_failure with this file's basename,
// line and column, whichever Matching entry point compiles it.
type t = A | B(int) | C

let single = x =>
  switch x {
  | A => 0
  | B(n) => n
  }

let tuple = (x, y) =>
  switch (x, y) {
  | (A, _) => 0
  | (_, C) => 1
  | (B(n), B(m)) => n + m
  }

let letPattern = x => {
  let B(n) = x
  n
}

let nested = x =>
  switch x {
  | Some(A) => 0
  | None => 1
  }
