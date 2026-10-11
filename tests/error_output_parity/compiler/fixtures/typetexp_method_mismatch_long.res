// Typetexp Method_mismatch is laid out in a @[<hov> box.
type person = {"say": (string, string) => unit, "say": (string, [< #a | #b]) => unit}
