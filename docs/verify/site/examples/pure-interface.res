module Counter: {
  @pure
  let next: int => int
} = {
  let calls = ref(0)
  let next = n => {
    calls := calls.contents + 1
    n + 1
  }
}
