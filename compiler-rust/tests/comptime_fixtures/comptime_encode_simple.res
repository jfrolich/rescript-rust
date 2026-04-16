type user = {name: string, age: int}

let u: user = {name: "Alice", age: 30}

// Simple comptime encoder — accesses each field
let encoded = switch @typeInfo(user) {
| Record({fields}) => {
    inline for field in fields {
      let _fieldName = field.name
      let _fieldVal = @field(u, field.name)
    }
    "done"
  }
| _ => @compileError("encode requires a record type")
}
