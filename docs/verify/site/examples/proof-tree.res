type rec tree = Leaf | Node(tree, int, tree)

let rec size = tree =>
  switch tree {
  | Leaf => 0
  | Node(left, _, right) => size(left) + 1 + size(right)
  }

let rec mirror = tree =>
  switch tree {
  | Leaf => Leaf
  | Node(left, value, right) => Node(mirror(right), value, mirror(left))
  }

@law
let mirrorTwice = (t: tree) => mirror(mirror(t)) == t

@law
let mirrorKeepsSize = (t: tree) => size(mirror(t)) == size(t)

type rec nat = Zero | Succ(nat)

let rec add = (a, b) =>
  switch a {
  | Zero => b
  | Succ(rest) => Succ(add(rest, b))
  }

@law
let addCommutes = (a: nat, b: nat) => add(a, b) == add(b, a)
