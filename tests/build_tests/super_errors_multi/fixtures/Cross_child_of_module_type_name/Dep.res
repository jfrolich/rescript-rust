module type S = {
  type t
  let make: unit => t
}
module type Same = S
module N: Same = {
  type t = {name: string}
  let make = () => {name: "a"}
}
