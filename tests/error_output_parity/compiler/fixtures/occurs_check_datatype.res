// Occurs check through a user datatype.
type rec t<'a, 'k> = Empty | Node(t<'a, 'k>, 'k, 'a)
let rec add = x_ => switch x_ { | Empty => Empty | Node(l, v, _) => Node(l, v, add(l)) }
