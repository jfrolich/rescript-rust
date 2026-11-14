type item = {name: string, price: int, qty: int}
type shape = Circle(float) | Rect(float, float)

@pure
let total = items => items->Array.reduce(0, (sum, item) => sum + item.price * item.qty)

@pure
let area = shape =>
  switch shape {
  | Circle(r) => Math.Constants.pi *. r *. r
  | Rect(w, h) => w *. h
  }
