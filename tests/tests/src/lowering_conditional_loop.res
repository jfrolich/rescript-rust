type t = A | B(int) | C(int, int) | D
@val external log: int => unit = "log"
let h = (c, xs: array<t>) => if c {
  for i in 0 to Array.length(xs) - 1 {
    switch Array.getUnsafe(xs, i) {
    | A => break
    | B(n) => log(n)
    | C(n, m) => log(n + m)
    | D => log(4)
    }
  }
  1
} else { 2 }

let nonReturn = (c, xs: array<t>) => {
  let result = if c {
  for i in 0 to Array.length(xs) - 1 {
    switch Array.getUnsafe(xs, i) {
    | A => break
    | B(n) => log(n)
    | C(n, m) => log(n + m)
    | D => log(4)
    }
  }
  1
} else { 2 }
  log(result)
  result + 1
}

let nested = (c, xs: array<t>) => if c {
  for outer in 0 to 2 {
    if outer > 0 {
  for i in 0 to Array.length(xs) - 1 {
    switch Array.getUnsafe(xs, i) {
    | A => break
    | B(n) => log(n)
    | C(n, m) => log(n + m)
    | D => log(4)
    }
  }
  1
} else { 2 }->ignore
  }
  1
} else { 2 }

let stringReturn = (c, xs: array<string>) => if c {
  for i in 0 to Array.length(xs) - 1 {
    switch Array.getUnsafe(xs, i) {
    | "stop" => break
    | "one" => log(1)
    | "two" => log(2)
    | _ => log(3)
    }
  }
  1
} else { 2 }
