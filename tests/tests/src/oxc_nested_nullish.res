// Keep nullish rewrite candidates nested inside a larger logical chain.
let left = (value: Nullable.t<int>, extra: bool) =>
  if value == Nullable.null || value == Nullable.undefined || extra {1} else {2}

let right = (value: Nullable.t<int>, extra: bool) =>
  if extra || (value == Nullable.undefined || value == Nullable.null) {1} else {2}
