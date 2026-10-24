// Matching on a tagged variant whose constructors include an empty inline
// record keeps every branch: the missing constructors of a match are built
// from the type's real descriptors, inline records included.
@tag("type")
type easing =
  | @as("linear") Linear({})
  | @as("hold") Hold({})
  | @as("function") Ease({name: string})
  | @as("cubicBezier") Bezier({x1: float, y1: float})

let same = (a, b) =>
  switch (a, b) {
  | (Linear(_), Linear(_)) | (Hold(_), Hold(_)) => true
  | (Ease(a), Ease(b)) => a.name == b.name
  | (Bezier(a), Bezier(b)) => a.x1 == b.x1 && a.y1 == b.y1
  | _ => false
  }

let isLinear = e =>
  switch e {
  | Linear(_) => true
  | _ => false
  }
