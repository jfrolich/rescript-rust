type t<'a> = dict<'a>

@pure @get_index external getUnsafe: (dict<'a>, string) => 'a = ""
@pure @get_index external get: (dict<'a>, string) => option<'a> = ""
@mutates @set_index external set: (dict<'a>, string, 'a) => unit = ""
@mutates @val external delete: 'a => unit = "delete"

@mutates(unchecked)
let delete = (dict, string) => {
  delete(get(dict, string))
}

@pure @obj external make: unit => dict<'a> = ""

@pure @val external fromArray: array<(string, 'a)> => dict<'a> = "Object.fromEntries"

@val @pure
external fromIterable: Stdlib_Iterable.t<(string, 'a)> => dict<'a> = "Object.fromEntries"

@pure @val external toArray: dict<'a> => array<(string, 'a)> = "Object.entries"

@pure @val external keysToArray: dict<'a> => array<string> = "Object.keys"

@pure @val external valuesToArray: dict<'a> => array<'a> = "Object.values"

@mutates @val external assign: (dict<'a>, dict<'a>) => dict<'a> = "Object.assign"

@mutates @variadic @val
external assignMany: (dict<'a>, array<dict<'a>>) => dict<'a> = "Object.assign"

@pure @val external concat: (@as(json`{}`) _, dict<'a>, dict<'a>) => dict<'a> = "Object.assign"

@variadic @val @pure
external concatMany: (@as(json`{}`) _, dict<'a>, array<dict<'a>>) => dict<'a> = "Object.assign"

@pure @variadic @val
external concatAll: (@as(json`{}`) _, array<dict<'a>>) => dict<'a> = "Object.assign"

@pure @val external copy: (@as(json`{}`) _, dict<'a>) => dict<'a> = "Object.assign"

// Use %raw to support for..in which is a ~10% faster than .forEach
let forEach: (dict<'a>, 'a => unit) => unit = %raw(`(dict, f) => {
  for (var i in dict) {
    f(dict[i]);
  }
}`)

// Use %raw to support for..in which is a ~10% faster than .forEach
let forEachWithKey: (dict<'a>, ('a, string) => unit) => unit = %raw(`(dict, f) => {
  for (var i in dict) {
    f(dict[i], i);
  }
}`)

// Use %raw to support for..in which is a ~10% faster than .forEach
let mapValues: (dict<'a>, 'a => 'b) => dict<'b> = %raw(`(dict, f) => {
  var target = {}, i;
  for (i in dict) {
    target[i] = f(dict[i]);
  }
  return target;
}`)

// Use %raw to support for..in which is a ~10% faster than Object.keys
let size: dict<'a> => int = %raw(`(dict) => {
  var size = 0, i;
  for (i in dict) {
    size++;
  }
  return size;
}`)

// Use %raw to support for..in which is a 2x faster than Object.keys
let isEmpty: dict<'a> => bool = %raw(`(dict) => {
  for (var _ in dict) {
    return false
  }
  return true
}`)

@pure
external has: (dict<'a>, string) => bool = "%dict_has"

@pure
external ignore: dict<'a> => unit = "%ignore"
