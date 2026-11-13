// The representations a law's values go through: each law takes a value
// apart the way compiled code does, so a value made in the wrong form fails.

type colour = Red | Green | @as("b") Blue
type point = {x: int, @as("why") y: float, label?: string}
type shape = Circle(float) | Rect({w: float, h: float}) | Poly(array<point>, colour)
type rec tree<'a> = Leaf | Node(tree<'a>, 'a, tree<'a>)
@tag("kind") type event = Click({x: int}) | Key(string) | Idle
@unboxed type id = Num(float) | Str(string) | @as(null) Missing

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
let colours = (c: colour) =>
  switch c {
  | Red | Green | Blue => true
  }

@law
let points = (p: point) =>
  p.x == p.x &&
  switch p.label {
  | Some(label) => String.length(label) >= 0
  | None => true
  }

@law
let shapes = (s: shape) =>
  switch s {
  | Circle(r) => r == r
  | Rect({w, h}) => w *. h == h *. w
  | Poly(points, Red | Green | Blue) => Array.length(points) >= 0
  }

@law
let mirrorKeepsSize = (t: tree<int>) => size(mirror(t)) == size(t)

@law
let mirrorTwice = (t: tree<bool>) => mirror(mirror(t)) == t

@law
let events = (e: event) =>
  switch e {
  | Click({x}) => x == x
  | Key(key) => String.length(key) >= 0
  | Idle => true
  }

@law
let ids = (i: id) =>
  switch i {
  | Num(n) => n == n
  | Str(s) => String.length(s) >= 0
  | Missing => true
  }

@law
let options = (o: option<option<bool>>) =>
  switch o {
  | None | Some(None) | Some(Some(true)) | Some(Some(false)) => true
  }

@law
let containers = (xs: list<(int, string)>, d: dict<int>, r: result<int, string>, v: [#a | #b(int)]) =>
  List.length(xs) >= 0 &&
  Dict.keysToArray(d)->Array.length == Dict.valuesToArray(d)->Array.length &&
  switch (r, v) {
  | (Ok(_) | Error(_), #a | #b(_)) => true
  }

module Nested = {
  @law
  let reverseTwice = (xs: array<int>) => xs->Array.toReversed->Array.toReversed == xs
}
