module M: {
  module type T = {
    module N: module type of Dep.Sub
    let x: int
  }
} = {
  module type T = {
    module N: module type of Dep.Sub
    let x: string
  }
}
