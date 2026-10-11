// `#A()` in a type is a tag with an empty-tuple payload.
@val external f: (~x: @string [#A()]=?) => unit = "f"
