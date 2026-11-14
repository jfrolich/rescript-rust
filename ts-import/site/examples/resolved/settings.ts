interface Settings {
  theme: "light" | "dark";
  fontSize: number;
  wrap: boolean;
  shortcuts: Record<string, string>;
}

const defaults: Settings = { theme: "light", fontSize: 14, wrap: true, shortcuts: {} };

// None of these types is written out anywhere. They are computed.
export type Patch = Partial<Omit<Settings, "shortcuts">>;
export type Setters = { [K in keyof Patch as `set${Capitalize<K>}`]-?: (value: Settings[K]) => void };

export function update(patch: Patch): Settings {
  return { ...defaults, ...patch };
}

export declare const setters: Setters;

// No annotation at all: the result type is inferred from the body.
export const snapshot = () => ({ settings: defaults, savedAt: new Date(), dirty: false });
