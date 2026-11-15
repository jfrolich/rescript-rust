module R = {
  type t = Apple | Banana | Pear | Bear
  type r = {apple: int, banana: int}
  exception Melon(int)
  let apple = 1
  type fruit = int
  module Sub = {
    let x = 1
  }
  module type Sig = {
    let x: int
  }
}
module A = R
