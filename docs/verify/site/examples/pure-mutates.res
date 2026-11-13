type buffer = {mutable items: array<string>, mutable size: int}

@mutates
let add = (buffer, item) => {
  buffer.items = buffer.items->Array.concat([item])
  buffer.size = buffer.size + 1
}

@pure
let fromArray = items => {
  let buffer = {items: [], size: 0}
  items->Array.forEach(item => buffer->add(item))
  buffer
}
