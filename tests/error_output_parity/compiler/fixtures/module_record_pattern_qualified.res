module M = {
  let x = 1
}

module N = {
  let y = 2
}

let {N.y: value} = module(M)
