// A range loop whose first value has effects and whose bound needs
// statements: the first value is declared before the bound's statements and
// the loop is printed without one (`for (; i <= bound; ++i)`). The
// declaration must stay whether the body reads the variable or not.

let first: unit => int = %raw(`() => 1`)
let last: unit => int = %raw(`() => 3`)
let fail: unit => int = %raw(`() => { throw new Error("bound") }`)

let effects = ref(0)
let eff = () => effects := effects.contents + 1
let seen = []

let unreadTo = () => {
  for _i in first() to (try last() catch {
  | _ => 0
  }) {
    eff()
  }
}

let unreadDownto = () => {
  for _i in last() downto (try first() catch {
  | _ => 0
  }) {
    eff()
  }
}

let ignoredTo = () => {
  for i in first() to (try last() catch {
  | _ => 0
  }) {
    ignore(i)
    eff()
  }
}

let ignoredDownto = () => {
  for i in last() downto (try first() catch {
  | _ => 0
  }) {
    ignore(i)
    eff()
  }
}

let logged = () => {
  for i in first() to (try last() catch {
  | _ => 0
  }) {
    Console.log(i)
  }
}

let readTo = () => {
  for i in first() to (try last() catch {
  | _ => 0
  }) {
    seen->Array.push(i)
  }
}

let captured = () => {
  let fns = []
  for i in first() to (try last() catch {
  | _ => 0
  }) {
    fns->Array.push(() => i)
  }
  fns->Array.map(f => f())
}

type pick = A | B | C

let switchBound = (v: pick) => {
  for _i in first() to switch v {
  | A => last()
  | B => last() + first()
  | C => first()
  } {
    eff()
  }
}

let whileBound = () => {
  for _i in first() to {
    let n = ref(0)
    while n.contents < last() {
      n := n.contents + 1
    }
    n.contents
  } {
    eff()
  }
}

let variableFirst = () => {
  let start = first()
  for _i in start to (try last() catch {
  | _ => 0
  }) {
    eff()
  }
}

let tryFirst = () => {
  for _i in (try fail() catch {
  | _ => first()
  }) to (try last() catch {
  | _ => 0
  }) {
    eff()
  }
}

let nested = () => {
  for _o in first() to (try last() catch {
  | _ => 0
  }) {
    for i in first() to (try last() catch {
    | _ => 0
    }) {
      ignore(i)
      eff()
    }
  }
}

let followed = () => {
  for _i in first() to (try last() catch {
  | _ => 0
  }) {
    eff()
  }
  eff()
}

let cell = ref(1)

let cellFirst = () => {
  for _i in cell.contents to (try last() catch {
  | _ => 0
  }) {
    eff()
  }
}

// The same loops at the top level of the unit.
for _i in first() to (try last() catch {
| _ => 0
}) {
  eff()
}

for i in last() downto (try first() catch {
| _ => 0
}) {
  ignore(i)
  eff()
}

let topFns = []
for i in first() to (try last() catch {
| _ => 0
}) {
  topFns->Array.push(() => i)
}

for _i in cell.contents to (try last() catch {
| _ => 0
}) {
  eff()
}

let topEffects = effects.contents

open Mocha
open Test_utils

let count = run => {
  effects := 0
  run()
  effects.contents
}

describe(__MODULE__, () => {
  test("top level", () => {
    eq(__LOC__, 9, topEffects)
    // The variable is declared once before the loop, so every closure
    // reads its last value.
    eq(__LOC__, [4, 4, 4], topFns->Array.map(f => f()))
  })
  test("unread variable", () => {
    eq(__LOC__, 3, count(unreadTo))
    eq(__LOC__, 3, count(unreadDownto))
    eq(__LOC__, 3, count(followed) - 1)
  })
  test("ignored variable", () => {
    eq(__LOC__, 3, count(ignoredTo))
    eq(__LOC__, 3, count(ignoredDownto))
    eq(__LOC__, 9, count(nested))
  })
  test("read and captured variable", () => {
    readTo()
    eq(__LOC__, [1, 2, 3], seen)
    eq(__LOC__, [4, 4, 4], captured())
  })
  test("bounds and first values", () => {
    eq(__LOC__, 3, count(() => switchBound(A)))
    eq(__LOC__, 4, count(() => switchBound(B)))
    eq(__LOC__, 1, count(() => switchBound(C)))
    eq(__LOC__, 3, count(whileBound))
    eq(__LOC__, 3, count(variableFirst))
    eq(__LOC__, 3, count(tryFirst))
    eq(__LOC__, 3, count(cellFirst))
  })
})
