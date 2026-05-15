type token
type config
type componentClass
type data
type bareClient

@module("output-parity-sdk") external defaultToken: token = "default"
@module("output-parity-sdk") external createToken: string => token = "createToken"
@module("output-parity-sdk") @new external newToken: string => token = "Token"
@module("output-parity-sdk") @val external version: string = "version"

@module("package-one") external sameNameOne: unit => int = "sameName"
@module("package-two") external sameNameTwo: unit => int = "sameName"

@module(("output-parity-sdk", "Nested")) @val external nestedValue: int = "value"
@module(("output-parity-sdk", "Nested")) external nestedCall: int => int = "bump"
@module(("output-parity-sdk", "Nested")) external nestedOther: int => int = "other"

@val("createClass") @module("react") external createClass: config => componentClass = "createClass"
@val("render") @module("react-dom") external render: (componentClass, token) => unit = ""

@module("node:assert") external ok: (bool, ~message: string=?) => unit = "ok"
@module("node:assert") external equal: ('a, 'a, ~message: string=?) => unit = "strictEqual"
@module("node:assert") external deepEqual: ('a, 'a, ~message: string=?) => unit =
  "deepStrictEqual"

@module("path") @variadic external joinPath: array<string> => string = "join"
@module("./relative-tool.js") external localDefault: int => int = "default"
@module("./relative-tool.js") external localNamed: int => int = "named"

@module external assetUrl: string = "./asset.png"
@val @module external bareData: data = "emoji-mart/data/all.json"
@module @new external makeBareClient: (~token: string, ~secret: string) => bareClient =
  "@mux/mux-node"

let makeConfig = name => %raw(`{ displayName: name }`)

let renderValue = () => render(createClass(makeConfig("ImportBinding")), defaultToken)

let assertionCalls = () => {
  ok(true, ~message="ok")
  equal(1, 1)
  deepEqual({"left": 1}, {"left": 1}, ~message="deep")
}

let allValues = (
  defaultToken,
  createToken("created"),
  newToken("constructed"),
  version,
  sameNameOne(),
  sameNameTwo(),
  nestedCall(nestedValue),
  nestedOther(nestedValue),
  joinPath(["root", "child", "file.res"]),
  localDefault(3),
  localNamed(4),
  assetUrl,
  bareData,
  makeBareClient(~token="token", ~secret="secret"),
  renderValue(),
  assertionCalls(),
)
