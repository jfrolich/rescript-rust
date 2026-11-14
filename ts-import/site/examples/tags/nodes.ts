export interface StringLiteral {
  type: "Literal";
  value: string;
}

export interface NumericLiteral {
  type: "Literal";
  value: number;
}

export interface Super {
  type: "Super";
  start: number;
}

// Two members share the tag "Literal"; the kind of `value` tells them apart.
export type Node = StringLiteral | NumericLiteral | Super;

export function print(node: Node): string {
  return node.type === "Super" ? "super" : String(node.value);
}
