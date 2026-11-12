let rec g = x => {
  let rec even = n => if n == 0 { true } else if n == 1 { false } else { even(n - 2) }
  if even(x) { g(x - 1) } else { x }
}

let rec captured = x => {
  let rec even = n => if n == 0 { x > 0 } else if n == 1 { false } else { even(n - 2) }
  if even(x) { captured(x - 1) } else { x }
}

let rec nested = x => {
  let rec even = n => {
    let rec step = m => if m <= 0 { true } else { step(m - 2) }
    if n == 0 { true } else if step(n) { even(n - 1) } else { false }
  }
  if even(x) { nested(x - 1) } else { x }
}
