// A local exception that rebinds another is the exception it rebinds, with
// its arguments (compiler/ml/typecore.ml `Pexp_letexception`,
// compiler/ml/typedecl.ml `transl_exception`).

exception E0
exception E1(int)
exception E2(int, string)
exception R({a: int, b: string})

module M = {
  exception E(int)
}
module A = M

let noArgument = x => {
  exception L = E0
  switch x {
  | L => 1
  | _ => 0
  }
}

let oneArgument = x => {
  exception L = E1
  switch x {
  | L(n) => n
  | _ => 0
  }
}

let twoArguments = x => {
  exception L = E2
  switch x {
  | L(n, s) => n + String.length(s)
  | _ => 0
  }
}

let inlineRecord = x => {
  exception L = R
  switch x {
  | L({a, b}) => a + String.length(b)
  | _ => 0
  }
}

let buildInlineRecord = () => {
  exception L = R
  L({a: 1, b: "x"})
}

let build = () => {
  exception L = E1
  L(1)
}

let buildAndMatch = x => {
  exception L = E1
  switch x {
  | L(n) => L(n + 1)
  | e => e
  }
}

let unused = () => {
  exception L = E1
  1
}

let throughPath = x => {
  exception L = M.E
  switch x {
  | L(n) => n
  | _ => 0
  }
}

let throughAlias = () => {
  exception L = A.E
  L(2)
}

let localOfLocal = x => {
  exception K(int)
  exception L = K
  switch K(x) {
  | L(n) => n
  | _ => 0
  }
}

let predefined = x => {
  exception L = Failure
  switch x {
  | L(s) => s
  | _ => ""
  }
}

let calledTwice = x => {
  exception L = E1
  try throw(L(x)) catch {
  | E1(n) => n
  }
}

let first = calledTwice(1)
let second = calledTwice(2)

// Controls: a local declaration with arguments, and a rebind item.
let localDeclaration = x => {
  exception L(int, string)
  switch x {
  | L(n, _) => n
  | _ => 0
  }
}

exception F = E1

let itemRebind = x =>
  switch x {
  | F(n) => n
  | _ => 0
  }
