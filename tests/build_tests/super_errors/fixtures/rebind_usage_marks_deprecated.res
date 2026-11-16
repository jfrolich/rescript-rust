// A rebind through a deprecated module reports the deprecation.
@deprecated("use Other")
module N = {
  exception E
}

exception A = N.E
