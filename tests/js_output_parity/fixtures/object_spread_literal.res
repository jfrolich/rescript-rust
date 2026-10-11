type word = {start: float, text: string, alignedStart?: float}
let word = (start, text): word => {start, text}
let ws: array<word> = [{...word(1000., "a"), alignedStart: 1.}]
let ws2 = (w: word) => {...w, alignedStart: 1.}
