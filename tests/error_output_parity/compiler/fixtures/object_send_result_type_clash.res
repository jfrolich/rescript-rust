// Differential fuzzer regression.
let f = (x: {"a": string}) => { let y: int = x["a"]; y }
