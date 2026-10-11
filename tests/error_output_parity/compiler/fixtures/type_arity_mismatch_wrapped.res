// error-output-parity: Typetexp.Type_arity_mismatch message wraps in its Format box
module VeryLongModuleNameForWrapping = {
  type t<'a, 'b> = ('a, 'b)
}
type x = VeryLongModuleNameForWrapping.t<int>
