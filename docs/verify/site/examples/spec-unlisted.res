type operation = Deposit(int) | Withdraw(int)

let apply = (balance, operation) =>
  switch operation {
  | Deposit(amount) => balance + amount
  | Withdraw(amount) => balance >= amount ? balance - amount : balance
  }

@spec
let neverOverdrawn: Spec.t<int, operation> = {
  init: 0,
  step: apply,
  always: balance => balance >= 0,
}
