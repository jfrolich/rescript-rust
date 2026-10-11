// A module unpacked from `module type of` a functor scrapes to the functor
// type, so a field access reports Access_functor_as_structure.
module Make = (I: {}) => {
  let x = 1
}
let f0 = async () => {
  module O = await Make
  O.forEach
}
