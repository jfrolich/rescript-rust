// `Node` is a variant tagged by `type`. Two cases share the tag "Literal":
// the switch tests `node.type`, and in the "Literal" arm
// `typeof node.value === "number"`.
module Nodes = %ts("./nodes.ts")

let describe = (node: Nodes.node) =>
  switch node {
  | StringLiteral({value}) => `the string ${value}`
  | NumericLiteral({value}) => `the number ${Float.toString(value)}`
  | Super(_) => "super"
  }

// The tag is written for you: `Super({start: 3.})` is
// `{type: "Super", start: 3}`.
let printed = Nodes.print(Super({start: 3.}))
