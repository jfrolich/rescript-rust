// Arguments and literal elements are evaluated left to right when a later
// one compiles to statements; JS method calls keep their object as `this`.
let log = []
let note = (x: string) => log->Array.push(x)

type o = {"m": int => int, "k": int}
let mk = (): o => {
  note("mk")
  %raw(`{m: function (x) { return this.k + x }, k: 5}`)
}

// Method call whose object compiles to statements
let viaBlockObj = {
  let o = {
    note("obj")
    let v = mk()
    v
  }
  o["m"](1)
}

let objWithPrelude = (n) => {
  let r = ref(0)
  let res = ({
    r := n
    let v = mk()
    v
  })["m"]({
    r := r.contents + 1
    r.contents
  })
  (res, r.contents)
}

// Property read of an object with statements, then used as an argument
let readField = (n) => {
  let r = ref(n)
  let k = ({
    r := r.contents + 1
    mk()
  })["k"]
  (k, r.contents)
}

// Mutated callee field
type t = {mutable f: int => int}
let callee = (o: t) => o.f({
  o.f = x => x + 100
  let y = Int.fromString("1")->Option.getOrThrow
  y * 2
})

// Method with prelude in an argument: this must stay obj
let methodThis = (o: o) => {
  let c = ref(0)
  o["m"]({
    c := c.contents + 1
    let z = Int.fromString("3")->Option.getOrThrow
    z + c.contents
  })
}

// assignable var in loop and closures
let loopy = () => {
  let acc = ref(0)
  let out = []
  for i in acc.contents to {
    acc := 3
    let e = acc.contents
    e
  } {
    out->Array.push(i)->ignore
  }
  out
}

let closures = () => {
  let x = ref(1)
  let bump = () => x := x.contents * 10
  let pair = (x.contents, {
    bump()
    let y = x.contents
    y + 1
  })
  pair
}

let isArr = (xs: array<int>) => {
  let r = ref(0)
  let p = (Array.isArray(xs), r.contents, {
    r := 2
    let q = Int.fromString("4")->Option.getOrThrow
    q
  })
  p
}

let dict = (n) => {
  let r = ref(n)
  dict{"a": r.contents, "b": {
    r := 9
    let w = Int.fromString("5")->Option.getOrThrow
    w + r.contents
  }}
}

Console.log((viaBlockObj, objWithPrelude(2), readField(3), callee({f: x => x}), methodThis(mk()), loopy(), closures(), isArr([1]), dict(1), log))
