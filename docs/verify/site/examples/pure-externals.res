@pure @val external parseFloat: string => float = "parseFloat"
@pure @send external padStart: (string, int, string) => string = "padStart"

@pure
let hash: string => int = %raw(`s => [...s].reduce((h, c) => (h * 31 + c.charCodeAt(0)) | 0, 0)`)

@pure
let key = s => `${s->padStart(4, "0")}:${hash(s)->Int.toString}:${parseFloat(s)->Float.toString}`
