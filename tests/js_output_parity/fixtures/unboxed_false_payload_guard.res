@unboxed
type dragStart = | @as(false) NoDrag | Drag({set: int => unit})

type event = {dragStart: dragStart}

let moveEvent = (event: event, value: int) => {
  let start = event.dragStart
  switch start {
  | Drag(target) => target.set(value)
  | _ => ()
  }
  value
}

let move = (start: dragStart, value: int) => {
  switch start {
  | NoDrag => ()
  | Drag({set}) => set(value)
  }
}

let moveBound = (start: dragStart, value: int) => {
  switch start {
  | NoDrag => ()
  | Drag(target) => target.set(value)
  }
}
