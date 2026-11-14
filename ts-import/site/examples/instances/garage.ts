export class Vehicle {
  constructor(public wheels: number) {}
}

export class Car extends Vehicle {
  constructor(public plate: string) {
    super(4);
  }

  honk(): string {
    return "beep";
  }
}

// Classes, a string and a symbol: each has a test at run time.
export function park(what: Car | Vehicle | string): number {
  return 1;
}

export function listen(event: string | symbol, target: URL | Date): void {}
