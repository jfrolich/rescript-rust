module M: {
  module type T = {
    let w: Dep.a
    let y: Dep.b
    let z: Dep.c
    let x: int
  }
} = {
  module type T = {
    let w: Dep.a
    let y: Dep.b
    let z: Dep.c
    let x: string
  }
}
