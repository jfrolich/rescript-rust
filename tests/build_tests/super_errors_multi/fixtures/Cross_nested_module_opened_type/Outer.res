module Inner = {
  type t = {name: string}
  let make = () => {name: "a"}
  module Deep = {
    type pair = (t, int)
    let pair = (x: t): pair => (x, 1)
  }
}
