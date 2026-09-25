@val
external log: @unwrap [< #A(int) | #B(string)] => unit = "console.log"
let () = log(#A(1))
let x: string = 1
