// error-output-parity: module type of structure inside recursive module approximation
module rec A: module type of {let x = 1} = A
