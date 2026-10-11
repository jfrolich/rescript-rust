// A switch-case body is an ordinary expression block.
let f = async x =>
  switch x {
  | Some(_) =>
    module MathModule = await Math
  }
