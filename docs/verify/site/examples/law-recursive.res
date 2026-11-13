type rec tree<'a> = Leaf | Node(tree<'a>, 'a, tree<'a>)

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

let rec toList = tree =>
  switch tree {
  | Leaf => list{}
  | Node(left, value, right) => List.concat(toList(left), list{value, ...toList(right)})
  }

@law
let mirrorKeepsSize = (t: tree<int>) => size(mirror(t)) == size(t)

@law
let mirrorTwice = (t: tree<string>) => mirror(mirror(t)) == t

@law
let mirrorReverses = (t: tree<int>) => toList(mirror(t)) == List.reverse(toList(t))
