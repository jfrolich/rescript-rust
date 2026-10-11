// Env.scrape_alias expands a module's Mty_ident through the module type
// definition.
module type F = (I: {}) => {let x: int}
module Make: F = (I: {}) => {
  let x = 1
}
let v = Make.x
