let price = 12.5
let quantity = 3

let total = %Debug.log(price *. Int.toFloat(quantity))
let label = %Debug.log(quantity > 2 ? "bulk" : "single")

%Debug.check(total < 30.0)
