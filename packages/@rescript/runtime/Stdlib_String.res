type t = string

@pure @val external make: 'a => string = "String"

@pure @val external fromCharCode: int => string = "String.fromCharCode"
@pure @variadic @val external fromCharCodeMany: array<int> => string = "String.fromCharCode"

@pure @val external fromCodePoint: int => string = "String.fromCodePoint"
@pure @variadic @val external fromCodePointMany: array<int> => string = "String.fromCodePoint"

@pure
external equal: (string, string) => bool = "%equal"

@pure
external compare: (string, string) => Stdlib_Ordering.t = "%compare"

@pure @get external length: string => int = "length"
@pure @get_index external get: (string, int) => option<string> = ""
@pure @get_index external getUnsafe: (string, int) => string = ""
@pure @send external charAt: (string, int) => string = "charAt"

@pure @send external charCodeAtUnsafe: (string, int) => int = "charCodeAt"

@pure @val @scope("Number") external isNaN: float => bool = "isNaN"
@pure @send external charCodeAt: (string, int) => float = "charCodeAt"

let charCodeAt = (s, i) => {
  let c = charCodeAt(s, i)
  isNaN(c) ? None : Some(c->Stdlib_Int.fromFloat)
}

@pure @send external codePointAt: (string, int) => option<int> = "codePointAt"

@pure @send external concat: (string, string) => string = "concat"
@pure @variadic @send external concatMany: (string, array<string>) => string = "concat"

@pure @send external endsWith: (string, string) => bool = "endsWith"
@pure @send external endsWithFrom: (string, string, int) => bool = "endsWith"

@pure @send external includes: (string, string) => bool = "includes"
@pure @send external includesFrom: (string, string, int) => bool = "includes"

@pure @send external indexOf: (string, string) => int = "indexOf"

let indexOfOpt = (s, search) =>
  switch indexOf(s, search) {
  | -1 => None
  | index => Some(index)
  }

@pure @send external indexOfFrom: (string, string, int) => int = "indexOf"

@pure @send external lastIndexOf: (string, string) => int = "lastIndexOf"

let lastIndexOfOpt = (s, search) =>
  switch lastIndexOf(s, search) {
  | -1 => None
  | index => Some(index)
  }

@pure @send external lastIndexOfFrom: (string, string, int) => int = "lastIndexOf"

@return(nullable) @send @pure
external match: (string, Stdlib_RegExp.t) => option<Stdlib_RegExp.Result.t> = "match"

type normalizeForm = [#NFC | #NFD | #NFKC | #NFKD]
@pure @send external normalize: string => string = "normalize"
@pure @send external normalizeByForm: (string, normalizeForm) => string = "normalize"

@pure @send external repeat: (string, int) => string = "repeat"

@pure @send external replace: (string, string, string) => string = "replace"
@pure @send external replaceRegExp: (string, Stdlib_RegExp.t, string) => string = "replace"
@pure @send external replaceAll: (string, string, string) => string = "replaceAll"
@pure @send external replaceAllRegExp: (string, Stdlib_RegExp.t, string) => string = "replaceAll"

@send @pure
external replaceRegExpBy0Unsafe: (
  string,
  Stdlib_RegExp.t,
  (~match: string, ~offset: int, ~input: string) => string,
) => string = "replace"

@send @pure
external replaceRegExpBy1Unsafe: (
  string,
  Stdlib_RegExp.t,
  (~match: string, ~group1: string, ~offset: int, ~input: string) => string,
) => string = "replace"

@send @pure
external replaceRegExpBy2Unsafe: (
  string,
  Stdlib_RegExp.t,
  (~match: string, ~group1: string, ~group2: string, ~offset: int, ~input: string) => string,
) => string = "replace"

@send @pure
external replaceRegExpBy3Unsafe: (
  string,
  Stdlib_RegExp.t,
  (
    ~match: string,
    ~group1: string,
    ~group2: string,
    ~group3: string,
    ~offset: int,
    ~input: string,
  ) => string,
) => string = "replace"

@pure @send external search: (string, Stdlib_RegExp.t) => int = "search"

let searchOpt = (s, re) =>
  switch search(s, re) {
  | -1 => None
  | index => Some(index)
  }

@pure @send external slice: (string, ~start: int, ~end: int=?) => string = "slice"

@pure @send external split: (string, string) => array<string> = "split"
@pure @send external splitAtMost: (string, string, ~limit: int) => array<string> = "split"
@pure @send external splitByRegExp: (string, Stdlib_RegExp.t) => array<option<string>> = "split"

@send @pure
external splitByRegExpAtMost: (string, Stdlib_RegExp.t, ~limit: int) => array<option<string>> =
  "split"

@pure @send external startsWith: (string, string) => bool = "startsWith"
@pure @send external startsWithFrom: (string, string, int) => bool = "startsWith"

@pure @send external substring: (string, ~start: int, ~end: int=?) => string = "substring"

@pure @send external toLowerCase: string => string = "toLowerCase"
@pure @send external toLocaleLowerCase: string => string = "toLocaleLowerCase"
@pure @send external toUpperCase: string => string = "toUpperCase"
@pure @send external toLocaleUpperCase: string => string = "toLocaleUpperCase"

@pure @send external trim: string => string = "trim"
@pure @send external trimStart: string => string = "trimStart"
@pure @send external trimEnd: string => string = "trimEnd"

@pure @send external padStart: (string, int, string) => string = "padStart"
@pure @send external padEnd: (string, int, string) => string = "padEnd"

@send @pure
external localeCompare: (
  string,
  string,
  ~locales: array<string>=?,
  ~options: Stdlib_Intl_Collator.options=?,
) => float = "localeCompare"

let isEmpty = s => length(s) == 0

let capitalize = s =>
  if isEmpty(s) {
    s
  } else {
    toUpperCase(getUnsafe(s, 0)) ++ slice(s, ~start=1)
  }

@pure
external ignore: string => unit = "%ignore"

@pure
external asIterable: string => Stdlib_Iterable.t<string> = "%identity"

@pure @get_index external getSymbolUnsafe: (string, Stdlib_Symbol.t) => 'a = ""
