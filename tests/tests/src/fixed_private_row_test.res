type t = private [< #A | #B]

module type S = {
  type u = private [< #C | #D]
}

module M = {
  type v = private [< #E | #F]
}

module A = M

module Host = {
  module Inner = M
}

module Alias = Host.Inner

module type AType = {
  type v = private [< #E | #F]
}

module Checked: AType = A
module CheckedAlias: AType = Alias
