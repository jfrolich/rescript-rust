@val external y: bool = "y"

let rec andTail = (a, b, c) =>
  if a { if b { c } else { c && y } } else { andTail(a, b, c) }

let rec orTail = (a, b, c) =>
  if a { if b { c || y } else { c } } else { orTail(a, b, c) }
