module M: {
  module type T = {
    @instanceOf({"Foo"}) type foo
    let x: int
  }
} = {
  module type T = {
    @instanceOf({"Foo"}) type foo
    let x: string
  }
}
