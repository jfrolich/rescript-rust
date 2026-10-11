// error-output-parity: dict expression spread rows participate in missing-comma recovery.
let other = dict{"b": 2}
let value = dict{"a": 1 ...other}
