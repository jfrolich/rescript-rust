type word = {start: float, text: string}
type aligned = {...word, alignedStart: float}
let w: word = {start: 1., text: "a"}
let a: aligned = {...w, alignedStart: 1.}
