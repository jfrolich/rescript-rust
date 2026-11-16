// Signatures of a functor parameter, a functor result, a recursive module
// and a module type declare constructors that never warn.
module M: {} = {
  module F = (
    X: {
      exception E
    },
  ) => {}
}

module M2: {} = {
  module F = (X: {}): {
    exception E
  } => {
    exception E
  }
}

module M3: {} = {
  module rec A: {
    exception E
  } = {
    exception E
  }
}

module M4: {} = {
  module type S = {
    exception E
  }
}
