export function add(a: number, b: number): number {
  return a + b;
}

// No annotation on the result: TypeScript infers `string`.
export const formatPrice = (amount: number, currency = "EUR") =>
  `${amount.toFixed(2)} ${currency}`;

export function average(...values: number[]) {
  return values.reduce(add, 0) / values.length;
}

export const taxRate = 0.21;
