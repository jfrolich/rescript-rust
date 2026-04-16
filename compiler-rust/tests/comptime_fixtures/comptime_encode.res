type user = {
  name: string,
  age: int,
}

// NOTE: This uses the old `comptime T: type` parameter syntax which
// is not yet fully implemented. See comptime_codec.res for the working
// polymorphic pattern using @comptime + @typeInfo(value).
@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | _ => @compileError("unsupported type")
  }
}

let myUser: user = {name: "Alice", age: 30}
let json = encode(myUser)
