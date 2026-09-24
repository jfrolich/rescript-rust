// A function maps its attributes after entering its own async context.
let testFnWithDirective = @directive(await "'use memo'") (name: string) => "Hello " ++ name
