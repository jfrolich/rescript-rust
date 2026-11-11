export interface Done {
  result: string;
}

export interface Failed {
  error: string;
  code?: number;
}

// Two plain objects: only their fields tell them apart.
export function run(job: string): Done | Failed {
  return job === "" ? { error: "no job", code: 1 } : { result: job };
}

export interface Label {
  value: string;
}

export interface Amount {
  value: number;
  unit: string;
}

// A field both have, of a different kind in each.
export function show(cell: Label | Amount): string {
  return typeof cell.value === "string" ? cell.value : `${cell.value} ${cell.unit}`;
}
