// create_package_mty rejects duplicate constraints before the package module
// type is looked up.
module type S = {
  type t
  type p = module(S with type t = int and type t = string)
}
