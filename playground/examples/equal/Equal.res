open Macro

// Two arguments of the same type. The comparison is written out per type:
// no run-time reflection, no walking of unknown values.
@generic
let equal = (a: code<'a>, b: code<'a>): code<bool> =>
  switch Type.info(typeOf(a)) {
  | Int | Float | String | Bool | Unit | BigInt | Char => %code(${a} === ${b})
  | Option(_) =>
    %code(
      switch (${a}, ${b}) {
      | (Some(left), Some(right)) => equal(left, right)
      | (None, None) => true
      | _ => false
      }
    )
  | Array(_) =>
    %code({
      let (left, right) = (${a}, ${b})
      Array.length(left) == Array.length(right) &&
        left->Array.everyWithIndex((item, index) => equal(item, right->Array.getUnsafe(index)))
    })
  | Record({fields}) =>
    fields->Array.reduce(%code(true), (all, f) =>
      %code(${all} && equal(${a->Code.field(f.name)}, ${b->Code.field(f.name)}))
    )
  | _ => error(`Equal.equal cannot compare values of type ${Type.name(typeOf(a))}`)
  }
