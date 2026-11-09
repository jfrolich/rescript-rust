// debugger(arg) evaluates its unit argument for effect before the statement,
// whatever its control flow, and its own value is unit.
let f = (x, y) => x + y

// Argument with an effect, statement position and tail position.
let effect = () => {
  debugger(Console.log("before"))
  3
}
let tail = () => debugger(Console.log("tail"))
let value = () => {
  let v = debugger(ignore(f(1, 2)))
  v
}
// Control-flow arguments.
let cond = c => {
  debugger(if c { Console.log("yes") })
  1
}
let sw = (x: option<int>) => {
  debugger(switch x { | Some(n) => Console.log(n) | None => () })
  2
}
let loop = n => {
  let i = ref(0)
  debugger(while i.contents < n { i := i.contents + 1 })
  i.contents
}
let tryArg = () => {
  debugger(try Console.log("t") catch { | Not_found => () })
  4
}
// Non-returning argument.
let throwing = () => debugger(throw(Not_found))
let unitLiteral = () => debugger()
// Through a let-bound unit and as an expression argument.
let nested = () => Console.log(debugger(Console.log("inner")))
// Inlined into the caller's frame through a wrapper.
let wrap = () => debugger()
let caller = () => {
  wrap()
  5
}
