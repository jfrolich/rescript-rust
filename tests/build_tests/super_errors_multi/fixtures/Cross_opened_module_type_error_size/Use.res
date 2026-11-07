module M: {
  module type T = {
    open Dep
    module N1: Sub.S
    module N2: Sub.S
    module type N3 = Sub.S
    let x: (~a: int) => int
  }
} = {
  module type T = {
    open Dep
    module N1: Sub.S
    module N2: Sub.S
    module type N3 = Sub.S
    let x: string
  }
}
