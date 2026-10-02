external importValue: int => promise<int> = "%import"
let _ = importValue(_)
let _ = x => importValue(x)
