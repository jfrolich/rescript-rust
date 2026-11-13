type t = float

module Constants = {
  @pure @val external nan: float = "NaN"
  @pure @val external epsilon: float = "Number.EPSILON"
  @pure @val external positiveInfinity: float = "Number.POSITIVE_INFINITY"
  @pure @val external negativeInfinity: float = "Number.NEGATIVE_INFINITY"
  @pure @val external minValue: float = "Number.MIN_VALUE"
  @pure @val external maxValue: float = "Number.MAX_VALUE"
}

@pure
external equal: (float, float) => bool = "%equal"

@pure
external compare: (float, float) => Stdlib_Ordering.t = "%compare"

@pure @val @scope("Number") external isNaN: float => bool = "isNaN"
@pure @val external isFinite: float => bool = "isFinite"
@pure @val external parseFloat: 'a => float = "parseFloat"
// parseInt's return type is a float because it can be NaN
@pure @val external parseInt: ('a, ~radix: int=?) => float = "parseInt"

@pure @send external toExponential: (float, ~digits: int=?) => string = "toExponential"

@pure @send external toFixed: (float, ~digits: int=?) => string = "toFixed"

@pure @send external toPrecision: (float, ~digits: int=?) => string = "toPrecision"

@pure @send external toString: (float, ~radix: int=?) => string = "toString"
@pure @send external toLocaleString: float => string = "toLocaleString"

let fromString: string => option<float> = %raw(`str => {
  if (!str || !str.trim()) return;
  let num = +str; // Number coercion, see https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number#number_coercion
  return isNaN(num) ? undefined : num;
}`)

@pure
external toInt: float => int = "%intoffloat"

@pure
external fromInt: int => float = "%identity"

@pure
external mod: (float, float) => float = "%modfloat"

let clamp = (~min=?, ~max=?, value): float => {
  let value = switch max {
  | Some(max) if max < value => max
  | _ => value
  }
  switch min {
  | Some(min) if min > value => min
  | _ => value
  }
}

@pure
external ignore: float => unit = "%ignore"
