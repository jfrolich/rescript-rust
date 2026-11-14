export type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "rect"; width: number; height: number }
  | { kind: "point" };

export type Align = "left" | "center" | "right";

export type Size = number | "auto";

export function area(shape: Shape): number {
  switch (shape.kind) {
    case "circle": return Math.PI * shape.radius ** 2;
    case "rect": return shape.width * shape.height;
    case "point": return 0;
  }
}

export function scale(shape: Shape, factor: number): Shape {
  return shape;
}

export function place(shape: Shape, align: Align, width: Size): string {
  return `${shape.kind} ${align} ${width}`;
}
