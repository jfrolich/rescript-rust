module Sub = {
  type t = {name: string}
  let make = () => {name: "a"}
  module Deep = {
    type u = Leaf(t)
    let leaf = () => Leaf(make())
  }
}
