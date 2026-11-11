// Runtime annotations and `@tag` read their payload's semantic string, so a
// backquoted string without interpolation and a string in braces name a
// class, a `typeof` kind or a tag like a string constant does.

@instanceOf(`Foo`) type foo
@instanceOf({"Bar"}) type bar
@instanceOf(`Intl\u{2E}Locale`) type locale
@typeOf(`symbol`) type sym
@typeOf({`bigint`}) type big

@unboxed type payload = Foo(foo) | Bar(bar) | Locale(locale) | Sym(sym) | Big(big) | S(string)

let classify = x =>
  switch x {
  | Foo(_) => 1
  | Bar(_) => 2
  | Locale(_) => 3
  | Sym(_) => 4
  | Big(_) => 5
  | S(_) => 6
  }

@tag(`kind`) type tagged = A({x: int}) | B({y: string})
@tag({"type"}) type braced = C({x: int}) | D({y: string})

let tagged = x =>
  switch x {
  | A({x}) => x
  | B(_) => 0
  }

let braced = x =>
  switch x {
  | C({x}) => x
  | D(_) => 0
  }
