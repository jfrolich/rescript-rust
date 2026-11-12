module Pair = {
  type t = {first: option<int>, second: option<int>}
}

module Single = {
  type t = {first: option<int>}
}

// The record patterns find their labels only through the open, which is
// therefore used.
let sum = pair => {
  open Pair
  let {first, second} = pair
  first->Option.getOr(0) + second->Option.getOr(0)
}

let firstOf = pair => {
  open Pair
  switch pair {
  | {first, second: _} => first
  }
}

// The second open shadows the label; the first one is unused.
let shadowed = pair => {
  open Pair
  open Single
  let {first} = pair
  first
}
