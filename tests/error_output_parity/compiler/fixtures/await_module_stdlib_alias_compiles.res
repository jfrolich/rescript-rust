// `await M` of a module alias checks its `module type of` package against
// the alias target resolved as a module.
let f4 = async () => {
  module A = await Array
  A.forEach
}
