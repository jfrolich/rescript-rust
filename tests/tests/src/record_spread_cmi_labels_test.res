type props = {
  ...JsxDOM.domProps,
  prefetch?: bool,
}

let prefetchOf = (p: props) => p.prefetch

type base = {
  @as("x-y") a: int,
  /** The b field */
  @as("z") b?: string,
}

type extended = {...base, c: int}

let make = (): extended => {a: 1, c: 2}
