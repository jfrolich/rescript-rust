let double = x => x * 2

let trace = x => {
  Console.log(x)
  x
}

@pure
let f = x => trace(double(x))
