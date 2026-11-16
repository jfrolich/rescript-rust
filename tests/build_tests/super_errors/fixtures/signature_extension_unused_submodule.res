// An extension constructor declared in a signature gets no unused warning;
// only the implementation's declaration does.
module M: {} = {
  module N: {
    exception E(int)
  } = {
    exception E(int)
  }
}

type t = ..

module M2: {} = {
  module N: {
    type t += E
  } = {
    type t += E
  }
}

module M3: {} = {
  module N: {
    module P: {
      exception E
    }
  } = {
    module P = {
      exception E
    }
  }
}

module M4: {} = {
  module N: {
    type t += private E
  } = {
    type t += E
  }
}
