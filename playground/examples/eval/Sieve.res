// Ordinary code: nothing here is a macro.
let primesBelow = (limit: int): array<int> => {
  let composite = Array.make(~length=limit, false)
  let primes = []
  for n in 2 to limit - 1 {
    if !(composite->Array.getUnsafe(n)) {
      primes->Array.push(n)
      let multiple = ref(n * n)
      while multiple.contents < limit {
        composite->Array.setUnsafe(multiple.contents, true)
        multiple := multiple.contents + n
      }
    }
  }
  primes
}

let rec fib = n => n < 2 ? n : fib(n - 1) + fib(n - 2)
