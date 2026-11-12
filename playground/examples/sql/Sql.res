open Macro

// What runs the SQL when the program runs: a driver with a `query` method.
type db
@send external exec: (db, string, array<unknown>) => array<'row> = "query"
external param: 'a => unknown = "%identity"

type column = {
  sqlName: string,
  // The type of a value of the column that is not null.
  typ: typ,
  // The field of the row type: `Null.t` when the column can be null, and
  // `customerId` with the name `customer_id` at run time.
  field: Type.field,
}
type table = {sqlName: string, columns: array<column>}

let capitalize = (text: string) => String.toUpperCase(String.charAt(text, 0)) ++ String.slice(text, ~start=1)

// customer_id as customerId
let camel = (name: string) =>
  name->String.split("_")->Array.mapWithIndex((part, i) => i == 0 ? part : capitalize(part))->Array.join("")

let columnType = (sqlType: string): typ =>
  switch String.toLowerCase(sqlType) {
  | "integer" => %type(int)
  | "text" => %type(string)
  | "boolean" => %type(bool)
  | "numeric" => %type(float)
  | "timestamp" => %type(Date.t)
  | other => error(`schema.sql has a column of the type ${other}, which Sql does not know`)
  }

// The tables of schema.sql, read while compiling.
let schema = (): array<table> =>
  readFile("schema.sql")
  ->String.split(";")
  ->Array.filterMap(statement =>
    switch /create\s+table\s+(\w+)\s*\(([\s\S]*)\)/i->RegExp.exec(statement) {
    | Some(found) =>
      switch found->RegExp.Result.matches {
      | [Some(name), Some(body)] =>
        let columns = body->String.split(",\n")->Array.map(line => {
          let words = line->String.trim->String.split(" ")
          let sqlName = words->Array.getUnsafe(0)
          let typ = columnType(words->Array.getUnsafe(1))
          let lower = String.toLowerCase(line)
          let required = lower->String.includes("not null") || lower->String.includes("primary key")
          {
            sqlName,
            typ,
            field: {...Type.field(camel(sqlName), required ? typ : %type(Null.t<${typ}>)), jsName: sqlName},
          }
        })
        Some({sqlName: name, columns})
      | _ => None
      }
    | None => None
    }
  )

let rowType = (name: string, columns: array<column>): decls =>
  Code.raw(`type ${name} = ${Type.name(Type.record(columns->Array.map(c => c.field)))}`)

// module Db = %Sql.tables(): a module per table of the schema, with the
// type of its rows, all of them, and the one with an id.
@macro
let tables = (): decls =>
  Code.decls(
    schema()->Array.map(table => {
      let select = "select * from " ++ table.sqlName
      Code.decls([
        Code.raw(`module ${capitalize(table.sqlName)} = {`),
        rowType("t", table.columns),
        %code(
          let all = (db: Sql.db): array<t> => exec(db, ${Code.string(select)}, [])
          let byId = (db: Sql.db, id: int): option<t> =>
            exec(db, ${Code.string(select ++ " where id = $1")}, [param(id)])[0]
        ),
        Code.raw("}"),
      ])
    }),
  )

let shape = "Sql.query reads: select columns from table where column = :parameter"

// module Q = %Sql.query("select ..."): the query is checked against the
// schema while compiling. `Q.row` is a record of the selected columns, and
// `Q.run` takes a labelled argument per `:parameter`, with the type of the
// column it is compared with.
@macro
let query = (sql: string): decls => {
  let (selected, tableName) = switch /^\s*select\s+(.+?)\s+from\s+(\w+)/i->RegExp.exec(sql) {
  | Some(found) =>
    switch found->RegExp.Result.matches {
    | [Some(selected), Some(tableName)] => (selected, tableName)
    | _ => error(shape)
    }
  | None => error(shape)
  }
  let tables = schema()
  let table = switch tables->Array.find(table => table.sqlName == tableName) {
  | Some(table) => table
  | None =>
    error(
      `There is no table "${tableName}" in schema.sql. It has: ${tables->Array.map(t => t.sqlName)->Array.join(", ")}`,
    )
  }
  let column = (name: string) =>
    switch table.columns->Array.find(c => c.sqlName == name) {
    | Some(column) => column
    | None =>
      error(
        `The table "${tableName}" has no column "${name}". It has: ${table.columns
          ->Array.map(c => c.sqlName)
          ->Array.join(", ")}`,
      )
    }
  let columns =
    String.trim(selected) == "*"
      ? table.columns
      : selected->String.split(",")->Array.map(name => column(String.trim(name)))

  // `city = :city` is `city = $1` for the driver, and the parameter `~city`
  // of the type of the column.
  let params = []
  let rec number = (text: string) =>
    switch /(\w+)\s*(?:=|<>|<=|>=|<|>)\s*:(\w+)/->RegExp.exec(text) {
    | Some(found) =>
      switch found->RegExp.Result.matches {
      | [Some(columnName), Some(name)] =>
        params->Array.push((name, column(columnName).typ))
        number(text->String.replace(":" ++ name, "$" ++ Int.toString(params->Array.length)))
      | _ => text
      }
    | None => text
    }
  let numbered = number(sql)

  let values = params->Array.map(((name, _)) => %code(param(${Code.ident(name)})))
  let run = Code.fn(
    [Code.param("db", %type(Sql.db))]->Array.concat(params->Array.map(((name, typ)) => Code.labelled(name, typ))),
    %code((exec(db, ${Code.string(numbered)}, [${...values}]): array<row>)),
  )
  Code.decls([rowType("row", columns), %code(let run = ${run})])
}
