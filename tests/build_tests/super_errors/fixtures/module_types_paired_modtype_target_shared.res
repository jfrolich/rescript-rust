// In N, every `T` is the one `Mty_ident T` of `Subst.add_modtype`: 392 words, printed.
module M: {
  module type T = {
    let x: int
  }
  module N: {
    module A0: T
    module A1: T
    module A2: T
    module A3: T
    let v: string
  }
} = {
  module type T = {
    let x: int
  }
  module N = {
    module A0 = {
      let x = 0
    }
    module A1 = {
      let x = 1
    }
    module A2 = {
      let x = 2
    }
    module A3 = {
      let x = 3
    }
    let v = 1
  }
}
