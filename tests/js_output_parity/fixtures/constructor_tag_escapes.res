type key = | @as("\\") Backslash | @as("\"") Quote | @as("a'b") Apos | @as("\n") Nl
let keys = [(Backslash, "Backslash"), (Quote, "Quote"), (Apos, "A"), (Nl, "nl")]
let f = k => switch k { | Backslash => 1 | Quote => 2 | Apos => 3 | Nl => 4 }
let g = k => k == Backslash
let h = (k: key) => (k :> string) == "\\"
@unboxed type u = | @as("\\") B | S(string)
let i = x => switch x { | B => 1 | S(_) => 2 }
let j = [B, S("\\")]
