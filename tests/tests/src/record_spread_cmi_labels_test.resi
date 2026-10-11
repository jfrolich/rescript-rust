type props = {
  ...JsxDOM.domProps,
  prefetch?: bool,
}

let prefetchOf: props => option<bool>

type base = {
  @as("x-y") a: int,
  /** The b field */
  @as("z") b?: string,
}

type extended = {...base, c: int}

let make: unit => extended
