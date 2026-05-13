// error-output-parity: strict module-alias inclusion accepts flattened runtime alias targets.
module M = (Belt.List: module type of Belt.List)
