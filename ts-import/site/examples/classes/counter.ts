export class Counter {
  static zero(): Counter {
    return new Counter(0);
  }

  private history: number[] = [];

  constructor(public count: number, readonly step = 1) {}

  increment(by?: number): Counter {
    this.history.push(this.count);
    this.count += by ?? this.step;
    return this;
  }

  get isZero(): boolean {
    return this.count === 0;
  }
}

export function sum(counters: Counter[]): number {
  return counters.reduce((total, counter) => total + counter.count, 0);
}
