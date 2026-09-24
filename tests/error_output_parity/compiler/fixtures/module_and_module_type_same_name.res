module S1 = (X: {}) => { let x = 1 }
module type S1 = { let foo: int }
module M: S1 = { let foo = 1 }
module F: S1 => {} = (X: {}) => {}
