let counter = ref(0)

@pure
let next = () => counter.contents + 1

@pure
let stamp = text => `${text} at ${Date.now()->Float.toString}`
