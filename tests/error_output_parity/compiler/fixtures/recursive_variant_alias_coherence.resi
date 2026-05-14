module Target: {
  type rec t =
    | Node(array<t>)
}

type rec t = Target.t =
  | Node(array<t>)
