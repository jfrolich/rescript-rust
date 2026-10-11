module type MT = { module type TT = { let u: int }
 module Z: TT }
module M: MT = { module type TT = { let u: int }
 module Z = {} }
