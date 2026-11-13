type t = int

module Constants = {
  @inline let minValue = -2147483648
  @inline let maxValue = 2147483647
}

@pure
external equal: (int, int) => bool = "%equal"

@pure
external compare: (int, int) => Stdlib_Ordering.t = "%compare"

@pure @send external toExponential: (int, ~digits: int=?) => string = "toExponential"

@pure @send external toFixed: (int, ~digits: int=?) => string = "toFixed"

@pure @send external toPrecision: (int, ~digits: int=?) => string = "toPrecision"

@pure @send external toString: (int, ~radix: int=?) => string = "toString"
@pure @send external toLocaleString: int => string = "toLocaleString"

@pure
external toFloat: int => float = "%identity"

@pure
external fromFloat: float => int = "%intoffloat"

let fromString: string => option<int> = str => {
  let? Some(num) = str->Stdlib_Float.fromString
  num === num->fromFloat->toFloat && Stdlib_Float.isFinite(num) ? Some(num->fromFloat) : None
}

@pure
external mod: (int, int) => int = "%modint"

type rangeOptions = {step?: int, inclusive?: bool}

let abs = x =>
  if x >= 0 {
    x
  } else {
    -x
  }

@pure @val external ceil: float => float = "Math.ceil"

let range = (start, end, ~options: rangeOptions={}) => {
  let isInverted = start > end

  let step = switch options.step {
  | None => isInverted ? -1 : 1
  | Some(0) if start !== end =>
    Stdlib_JsError.throw(Stdlib_JsError.RangeError.make("Incorrect range arguments"))
  | Some(n) => n
  }

  let length = if isInverted === (step >= 0) {
    0 // infinite because step goes in opposite direction of end
  } else if step == 0 {
    options.inclusive === Some(true) ? 1 : 0
  } else {
    let range = isInverted ? start - end : end - start
    let range = options.inclusive === Some(true) ? range + 1 : range
    ceil(Stdlib_Float.fromInt(range) /. Stdlib_Float.fromInt(abs(step)))->Stdlib_Float.toInt
  }

  Stdlib_Array.fromInitializer(~length, i => start + i * step)
}

let clamp = (~min=?, ~max=?, value): int => {
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
external bitwiseAnd: (int, int) => int = "%andint"

@pure
external bitwiseOr: (int, int) => int = "%orint"

@pure
external bitwiseXor: (int, int) => int = "%xorint"

@pure
external bitwiseNot: int => int = "%bitnot_int"

@pure
external shiftLeft: (int, int) => int = "%lslint"

@pure
external shiftRight: (int, int) => int = "%asrint"

@pure
external shiftRightUnsigned: (int, int) => int = "%lsrint"

@pure
external ignore: int => unit = "%ignore"
