@Lens.derive
type point = {x: int, y: int, label: string}

let origin = {x: 0, y: 0, label: "origin"}

let moved = origin->Lens.update(point_x, x => x + 10)->Lens.update(point_label, String.toUpperCase)

Console.log(moved)
