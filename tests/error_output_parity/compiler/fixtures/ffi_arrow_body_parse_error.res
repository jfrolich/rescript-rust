let add: (int, int) => int = %ffi(`(x,y)=>x+.y`)
let bad: string = add
