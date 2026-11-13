@pure
let counter = () => {
  let n = ref(0)
  () => {
    n := n.contents + 1
    n.contents
  }
}
