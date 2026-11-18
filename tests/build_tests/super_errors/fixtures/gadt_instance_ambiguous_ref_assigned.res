type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) => {
  let r = ref(None)
  switch x {
  | Int => r := Some(if true { y } else { 0 })
  }
  r.contents
}
