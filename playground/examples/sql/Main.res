// The types of the tables come from schema.sql.
module Db = %Sql.tables()

// A query is checked against the schema while compiling.
module InCity = %Sql.query("select name, vip from customers where city = :city")
module Large = %Sql.query("select * from orders where total >= :minimum and customer_id = :customer")

// A column that is not in the schema does not compile:
// module Emails = %Sql.query("select email from customers")

// Stands in for a database on this page: it prints the SQL it is given and
// answers with these rows.
let db: Sql.db = %raw(`{
  query(sql, params) {
    console.log(sql, params)
    return sql.includes("orders")
      ? [
          {id: 7, customer_id: 1, total: 250.0, shipped_at: null},
          {id: 9, customer_id: 1, total: 120.5, shipped_at: new Date("2026-03-01")},
        ]
      : [{id: 1, name: "Ada", city: "Utrecht", vip: true}]
  }
}`)

InCity.run(db, ~city="Utrecht")->Array.forEach(customer =>
  Console.log(customer.name ++ (customer.vip ? " is a vip" : ""))
)

Large.run(db, ~minimum=100.0, ~customer=1)->Array.forEach(order =>
  switch order.shippedAt {
  | Value(date) => Console.log2(order.id, "shipped on " ++ date->Date.toDateString)
  | Null => Console.log2(order.id, "not shipped")
  }
)

switch Db.Customers.byId(db, 1) {
| Some({name, city: Value(city)}) => Console.log(name ++ " lives in " ++ city)
| _ => ()
}
