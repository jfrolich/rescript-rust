// error-output-parity: dict expression rows after spread participate in missing-comma recovery.
let other = dict{"b": 2}
let value = dict{...other "a": 1}
