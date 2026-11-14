type t = bigint

@pure @val external asIntN: (~width: int, bigint) => bigint = "BigInt.asIntN"
@pure @val external asUintN: (~width: int, bigint) => bigint = "BigInt.asUintN"

@val @pure
external fromStringOrThrow: string => bigint = "BigInt"

let fromString = (value: string) => {
  try Some(fromStringOrThrow(value)) catch {
  | _ => None
  }
}

@pure @val external fromInt: int => bigint = "BigInt"

@val @pure
external fromFloatOrThrow: float => bigint = "BigInt"

let fromFloat = (value: float) => {
  try Some(fromFloatOrThrow(value)) catch {
  | _ => None
  }
}

@send @pure
external toString: (bigint, ~radix: int=?) => string = "toString"

@send @pure
external toLocaleString: bigint => string = "toLocaleString"

@pure @val external toFloat: bigint => float = "Number"

let toInt = t => t->toFloat->Stdlib_Int.fromFloat

@pure
external add: (bigint, bigint) => bigint = "%addbigint"

@pure
external sub: (bigint, bigint) => bigint = "%subbigint"

@pure
external mul: (bigint, bigint) => bigint = "%mulbigint"

@pure
external div: (bigint, bigint) => bigint = "%divbigint"

@pure
external mod: (bigint, bigint) => bigint = "%modbigint"

@pure
external bitwiseAnd: (bigint, bigint) => bigint = "%andbigint"

@pure
external bitwiseOr: (bigint, bigint) => bigint = "%orbigint"

@pure
external bitwiseXor: (bigint, bigint) => bigint = "%xorbigint"

@pure
external bitwiseNot: bigint => bigint = "%bitnot_bigint"

@pure
external shiftLeft: (bigint, bigint) => bigint = "%lslbigint"

@pure
external shiftRight: (bigint, bigint) => bigint = "%asrbigint"

@pure
external ignore: bigint => unit = "%ignore"
