let base = 7
let f = x => x + base
type t = A | B(int) | C(string)
let classify = v =>
  switch v {
  | A => "a"
  | B(n) if n > 3 => "big"
  | B(_) => "small"
  | C(s) => s ++ "!"
  }
let rec loop = (n, acc) => n == 0 ? acc : loop(n - 1, acc + n)
let strs = s =>
  switch s {
  | "x" => 1
  | "y" => 2
  | _ => 3
  }
let effects = () => {
  Console.log("hi")
  let arr = [1, 2, 3]
  arr->Array.forEach(x => Console.log(x))
  if Array.length(arr) > 2 {
    Console.log("long")
  } else {
    Console.log("short")
  }
}
type r = {a: int, b: string}
let upd = (r: r) => {...r, a: r.a + 1}
let obj = {"x": 1, "y": "two"}
let failing = () => throw(Not_found)
let dbg = () => %debugger
let mutating = () => {
  let x = ref(0)
  for i in 0 to 10 { x := x.contents + i }
  while x.contents > 0 { x := x.contents - 3 }
  x.contents
}
let tryit = () => try failing() catch { | Not_found => 0 }
module M = {
  let inner = (a, b) => a * b
}
let useM = M.inner(2, 3)
let trailingDebugger = () => %debugger
let cb_a1 = arr => arr->Array.map(x => x + 1)
let cb_a2 = (f: (int => int) => int) => f(x => x + 1)
let cb_a3 = arr => Array.forEach(arr, x => Console.log(x))
let cb_a4 = () => {
  let cb = x => Console.log(x)
  cb
}
