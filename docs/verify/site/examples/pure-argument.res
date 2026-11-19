type item = {name: string, price: int, qty: int}

@pure
let addItem = (items, item) => {
  items->Array.push(item)
  items
}
