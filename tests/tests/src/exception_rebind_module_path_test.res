// An exception rebound from a module path is read at that path: a field of
// the module, in this file or another one.

module Target = {
  exception Failed(string)
}

exception Failed = Target.Failed

module Outer = {
  module Inner = {
    exception Deep(int)
  }
}

exception Deep = Outer.Inner.Deep

module Make = (
  X: {
    let name: string
  },
) => {
  exception Made(string)
  let make = () => Made(X.name)
}

module Applied = Make({
  let name = "applied"
})

exception Made = Applied.Made

exception Local = Local_exception_test.D

let message = exn =>
  switch exn {
  | Failed(message) => message
  | Deep(n) => Int.toString(n)
  | Made(name) => name
  | Local(n) => Int.toString(n)
  | _ => "other"
  }

let messages = [
  message(Target.Failed("failed")),
  message(Outer.Inner.Deep(1)),
  message(Applied.make()),
  message(Local_exception_test.D(3)),
]
