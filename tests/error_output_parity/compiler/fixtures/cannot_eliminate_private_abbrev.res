module Make = (S: {type elt}) => {
  let f = (x: S.elt) => x
}
module I = Make({
  type elt = private int
})
