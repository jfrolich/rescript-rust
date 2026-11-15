module Top = {
  module Outer: {
    module R: {
      type ext = ..
      type ext += C(string)
    }
  } = {
    module R = {
      type ext = ..
      type ext += C(int)
    }
  }
}
