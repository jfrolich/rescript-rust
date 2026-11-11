module Outer: {
  module type T = {
    module G: (Y: {let a: int; let b: int}) => {}
  }
}
