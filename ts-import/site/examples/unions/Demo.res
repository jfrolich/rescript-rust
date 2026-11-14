let {area, scale, place} = %ts("./shapes.ts")

// A union of objects with a common literal field is a variant tagged by
// that field. At run time `Circle({radius: 2.})` is `{kind: "circle", radius: 2}`.
let circle = Circle({radius: 2.})
let circleArea = area(circle)

// So a value that comes back from TypeScript can be matched on.
let describe = shape =>
  switch scale(shape, 2.) {
  | Circle({radius}) => `a circle of radius ${Float.toString(radius)}`
  | Rect({width, height}) => `${Float.toString(width)} by ${Float.toString(height)}`
  | Point(_) => "a point"
  }

// String literals are polymorphic variants; `number | "auto"` is an
// unboxed variant, a plain number or the string "auto" at run time.
// A member with only the tag is a case with an empty record:
// `Point({})` is `{kind: "point"}`.
let placed = place(circle, #center, Auto)
let sized = place(Point({}), #left, Number(120.))
