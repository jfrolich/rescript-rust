// error-output-parity: Typetexp.Cannot_quantify Tvar escape branch
external magic: 'a => 'b = "%identity"

let f: type a. {.. "x": 'b. (a as 'b)} = magic(0)
