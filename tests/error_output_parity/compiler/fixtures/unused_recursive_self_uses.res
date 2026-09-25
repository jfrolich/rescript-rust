// error-output-parity: uses inside a recursive definition do not count as uses
module M: {} = {
  type rec a = A(b) and b = B(a)
  let rec f = () => g() and g = () => f()
  let rec used = () => helper() and helper = () => 1
  let _ = used
}
