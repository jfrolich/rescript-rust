open Macro

// Mock.make() is a record of functions that fail when they are called:
// what a test starts from, before it replaces the functions it uses.
//
// The parameters of a generated function have names, to read well in the
// expansion, and are not used: the compiler would warn about each one.
// The macro puts @warning("-27") on the function, so whoever uses the
// macro gets no warning for code they did not write.
//
// An attribute belongs to an expression. A field of a record has no place
// for one, so it goes on the field's value.
@generic
let make = (_: code<unit>): code<'a> =>
  switch Type.info(expected()) {
  | Record({fields}) =>
    Code.record(
      fields->Array.map(f =>
        switch Type.info(f.typ) {
        | Function({params}) =>
          let named = params->Array.mapWithIndex((typ, i) => Code.param("arg" ++ Int.toString(i + 1), typ))
          let stub = Code.fn(named, %code(throw(Failure(${Code.string(f.name ++ " is not mocked")}))))
          Code.entryOf(f, %code(@warning("-27") ${stub}))
        | _ => error(`Mock.make: the field ${f.name} is not a function`)
        }
      ),
    )
  | _ => error("Mock.make fills a record of functions")
  }

// An attribute a quote cannot write, because the macro computes it:
// Code.withAttr(value, name, ~payload) is `@name(payload) value`.
@macro
let allow = (warning: int, value: code<'a>): code<'a> =>
  Code.withAttr(value, "warning", ~payload=Code.string("-" ++ Int.toString(warning)))
