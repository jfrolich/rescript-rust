// Some(function) is an identity option wrapper, but its arrow body still groups.
@val external install: (unit => option<unit => unit>) => unit = "install"
@val external effect: int => unit = "effect"
let installCleanup = value => install(() => Some(() => effect(value)))
let nested = value => Some(() => Some(() => effect(value)))
