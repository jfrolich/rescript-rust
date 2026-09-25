// Ppat_record: with no concrete record expected type (`opath = None`) a label
// with nothing in scope is unbound (typecore.ml process_label).
type point = {x: float, y: float}

let f = point => {
  let {y, int} = point
  y +. int
}
