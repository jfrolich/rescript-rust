@unboxed
type t<+'a> = Primitive_js_extern.null<'a> =
  | Value('a)
  | @as(null) Null

@pure
external asNullable: t<'a> => Stdlib_Nullable.t<'a> = "%identity"

@pure
external null: t<'a> = "#null"

@pure
external make: 'a => t<'a> = "%identity"

@pure
external toOption: t<'a> => option<'a> = "#null_to_opt"

let fromOption: option<'a> => t<'a> = option =>
  switch option {
  | Some(x) => make(x)
  | None => null
  }

let equal = (a, b, eq) => Stdlib_Option.equal(a->toOption, b->toOption, eq)

let compare = (a, b, cmp) => Stdlib_Option.compare(a->toOption, b->toOption, cmp)

let getOr = (value, default) =>
  switch value->toOption {
  | Some(x) => x
  | None => default
  }

let getOrThrow: t<'a> => 'a = value =>
  switch value->toOption {
  | Some(x) => x
  | None => throw(Invalid_argument("Null.getOrThrow: value is null"))
  }

@pure
external getUnsafe: t<'a> => 'a = "%identity"

let forEach = (value, f) =>
  switch value->toOption {
  | Some(x) => f(x)
  | None => ()
  }

let map = (value, f) =>
  switch value->toOption {
  | Some(x) => make(f(x))
  | None => null
  }

let mapOr = (value, default, f) =>
  switch value->toOption {
  | Some(x) => f(x)
  | None => default
  }

let flatMap = (value, f) =>
  switch value->toOption {
  | Some(x) => f(x)
  | None => null
  }

@pure
external ignore: t<'a> => unit = "%ignore"
