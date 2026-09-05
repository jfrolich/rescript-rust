let inferred = (fn, value) => fn(value, ~named=value)
let choose = (value, ~named, ~optional=?) => {
  ignore(named)
  ignore(optional)
  value
}
let integer = inferred((value, ~named) => value + named, 3)
let text = choose("first", ~optional="third", ~named="second")
let partial = choose(~named=4, ...)
let completed = partial(5)
type alias<'a> = ('a, ~named: 'a, ~optional: 'a=?) => 'a
let viaAlias = (fn: alias<int>) => fn(8, ~named=9)
let result = viaAlias(choose)
