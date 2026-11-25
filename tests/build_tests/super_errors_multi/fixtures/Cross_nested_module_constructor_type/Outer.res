module Inner = {
  type t = {name: string}
  type shape =
    | Circle(float)
    | Square
  module Deep = {
    type color =
      | Red
      | Green
  }
}
