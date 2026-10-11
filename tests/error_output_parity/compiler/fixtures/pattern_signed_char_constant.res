let x = url =>
  switch url {
  | list{-'c'} => 1
  | _ => 2
  }
let y: string = x(list{})
