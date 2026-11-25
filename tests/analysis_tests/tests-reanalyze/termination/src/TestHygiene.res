// Hygiene errors of groups with several functions. The analysis compiles a
// group's functions in the order of its function table, a hash table, and
// the two parts of a sequence last first: the errors below are reported in
// that order, not in source order.

let progress = () => ()

@progress(progress)
let rec f = () => f()

// Functions used as values: in both parts of a sequence, an if and a tuple.
@progress(progress)
let rec g = () => {
  let a = g
  let b = h
  ignore(a)
  ignore(b)
  (g, h)->ignore
  if true {
    ignore(g)
  } else {
    ignore(h)
  }
}
and h = () => {
  ignore(g)
  g()
}
and i = () => {
  ignore(h)
  h()
}
and j = () => {
  ignore(i)
  ignore(k)
  i()
}
and k = () => {
  ignore(j)
  j()
}

// Parametric and inner recursive functions.
@progress(progress)
let rec parseList = (~f, n) => {
  let rec loop = m =>
    if m == 0 {
      []
    } else {
      [f(m), ...loop(m - 1)]
    }
  loop(n)
}
and parseInt = n => {
  progress()
  n
}
and parseListInt = n => parseList(~f=parseInt, n)
and other = n => parseList(~f=other2, n)
and other2 = n => {
  ignore(other(n))
  n
}
and bad2 = n => parseList(~f=x => x, n)

@progress(progress)
let rec opt = n =>
  if n == 0 {
    None
  } else {
    progress()
    Some(n)
  }
and useOpt = n =>
  switch opt(n) {
  | Some(m) => useOpt(m)
  | None => useOpt(n)
  }
and tr = n =>
  try {
    tr(n)
  } catch {
  | _ => tr(n)
  }
and forLoop = n => {
  for i in forLoop(n) to forLoop(n + 1) {
    ignore(forLoop(i))
  }
  0
}

// Calls that pass no recursive function for a parametric function's label.
@progress(progress)
let rec pp1 = (~f, n) => f(n)
and r0 = n => pp1(~f=r1, n)
and r1 = n => {
  let _ = pp1(~f=x => x, n)
  let _ = pp1(~f=x => x + 1, n)
  r1(n)
}
and r2 = n => {
  let _ = pp1(~f=x => x, n)
  r3(n)
}
and r3 = n => {
  let _ = pp1(~f=x => x, n)
  r4(n)
}
and r4 = n => {
  let _ = pp1(~f=x => x, n)
  r5(n)
}
and r5 = n => {
  let _ = pp1(~f=x => x, n)
  r6(n)
}
and r6 = n => {
  let _ = pp1(~f=x => x, n)
  r7(n)
}
and r7 = n => {
  let _ = pp1(~f=x => x, n)
  r8(n)
}
and r8 = n => {
  let _ = pp1(~f=x => x, n)
  r9(n)
}
and r9 = n => {
  let _ = pp1(~f=x => x, n)
  alpha2(n)
}
and alpha2 = n => {
  let _ = pp1(~f=x => x, n)
  beta2(n)
}
and beta2 = n => {
  let _ = pp1(~f=x => x, n)
  (pp1(~f=x => x, n), pp1(~f=x => x * 2, n))->ignore
  gamma2(n)
}
and gamma2 = n => {
  let _ = pp1(~f=x => x, n)
  pp1(~f=x => x, n) + r1(n) + pp1(~f=x => x, n)
}
and delta2 = n => {
  let rec lp = m =>
    if m == 0 {
      pp1(~f=x => x, m)
    } else {
      lp(m - 1)
    }
  pp1(~f=x => x, n) + lp(n)
}
