type fn<'a> = ('a, ~named: 'a, ~optional: 'a=?) => 'a
let select: fn<'a> = (value, ~named, ~optional=?) => {
  let _ = named
  let _ = optional
  value
}
let integer = select(7, ~named=8)
let text = select("first", ~optional="third", ~named="second")
let curried = (x, ~named) => (~optional=?) => {
  let _ = named
  let _ = optional
  x
}
let nested = curried(integer, ~named=text)(~optional=true)
type base<'a> = {
  fixed: (~named: int, ~optional: int=?) => int,
  generic: ('a, ~named: 'a, ~optional: 'a=?) => 'a,
}
type spread = {...base<string>}
let project = (value: spread) => value.generic("a", ~named="b")
