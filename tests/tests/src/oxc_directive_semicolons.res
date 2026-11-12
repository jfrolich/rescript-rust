let cached = @directive("'use cache';") value => value + 1
let action = @directive("'use server';") async value => value + 2
let nested = value => {
  let local = @directive("'use cache';;") input => input + 3
  local(value)
}
