// Things TypeScript can say that ReScript cannot say exactly.

// Two signatures for one function.
export function parse(input: string): number;
export function parse(input: number): string;
export function parse(input: unknown): unknown {
  return input;
}

// A union with nothing to tell its members apart at run time: both have
// `id`, and `label` may be missing from either.
export type Target = { id: string; label?: string } | { id: string };
export function resolve(target: Target): string {
  return "";
}

// `any` switches checking off.
export function log(message: any, ...rest: any[]): void {}

// A constraint on a type parameter.
export function byId<T extends { id: string }>(items: T[], id: string): T | undefined {
  return items.find((item) => item.id === id);
}

// A function that also has properties.
export const debounce: { (callback: () => void): void; cancel(): void } = Object.assign(
  (callback: () => void) => {},
  { cancel() {} },
);
