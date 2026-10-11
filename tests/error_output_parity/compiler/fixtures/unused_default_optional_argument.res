// A defaulted optional parameter is bound by a generated `let`, so an
// unused one gets warning 26.
let f = (~text=32, ~label="hel") => ()
let g = (~a=1, ~b=a + 1, ~c=3, ()) => b
