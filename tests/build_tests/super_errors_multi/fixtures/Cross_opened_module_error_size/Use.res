module M: {
  module type T = {
    open Dep
    type s2 = Sub.s
    type s3 = Sub.s
    let x: int
  }
} = {
  module type T = {
    open Dep
    type s2 = Sub.s
    type s3 = Sub.s
    let x: string
  }
}
