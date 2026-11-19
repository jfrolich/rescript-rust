@pure
let evens = xs => {
  let out = []
  xs->Array.forEach(x =>
    if mod(x, 2) == 0 {
      out->Array.push(x)
    }
  )
  out
}

@pure
let sum = xs => {
  let total = ref(0)
  for i in 0 to Array.length(xs) - 1 {
    total := total.contents + xs->Array.getUnsafe(i)
  }
  total.contents
}
