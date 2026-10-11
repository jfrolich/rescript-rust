// obj##name becomes a property access (Ast_util.js_property).
let o = {"x": 1}
let w: string = \"##"(o, "x")
