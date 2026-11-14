export type Result<T, E = string> =
  | { ok: true; value: T }
  | { ok: false; error: E };

export interface Page<T> {
  items: T[];
  next?: string;
}

export function parseNumber(text: string): Result<number> {
  const value = Number(text);
  return Number.isNaN(value) ? { ok: false, error: "not a number" } : { ok: true, value };
}

export function first<T>(page: Page<T>): T | undefined {
  return page.items[0];
}

export function mapPage<T, U>(page: Page<T>, f: (item: T, index: number) => U): Page<U> {
  return { items: page.items.map(f), next: page.next };
}
