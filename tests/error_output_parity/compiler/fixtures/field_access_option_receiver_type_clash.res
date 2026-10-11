// error-output-parity: Typecore.Pexp_field selects in-scope labels before reporting option receiver type clash.

type person = {name: string}

let person: option<person> = None

let name = person.name
