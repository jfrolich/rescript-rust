module F = (
  X: {
    module R: {
      type t = Apple | Banana | Pear | Bear
      type r = {apple: int, banana: int}
      exception Melon(int)
      let apple: int
      type fruit = int
      module Sub: {
        let x: int
      }
      module type Sig = {
        let x: int
      }
    }
    module A = R
  },
) => {
  let v = X.A.Subb.x
}
