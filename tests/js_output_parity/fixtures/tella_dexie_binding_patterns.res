type dexieBool = False | True

module type DB = {
  type tableName
  type row
  type key
  let version: int
  let dbName: string
  let stores: array<(tableName, string)>
  let tableName: tableName
  let lookupKey: key
  let row: row
}

module Make = (Db: DB) => {
  type dexie
  type table
  type version
  type collection
  type whereClause

  type indexable
  external string: string => indexable = "%identity"
  external int: int => indexable = "%identity"
  external array: array<indexable> => indexable = "%identity"

  @module("dexie") @new external make: string => dexie = "default"

  @get_index external table: (dexie, Db.tableName) => table = ""

  @send external version: (dexie, int) => version = "version"

  let stores: (version, array<(Db.tableName, string)>) => version = %raw(`
    function(version, schemaDefinition) {
      return version.stores(Object.fromEntries(schemaDefinition));
    }
  `)

  @send external where: (table, Db.key) => whereClause = "where"
  @send external equalsInt: (whereClause, int) => collection = "equals"
  @send external equalsBool: (whereClause, dexieBool) => collection = "equals"
  @send external equalsString: (whereClause, string) => collection = "equals"

  let table = {
    let db = make(Db.dbName)
    db->version(Db.version)->stores(Db.stores)->ignore
    db->table(Db.tableName)
  }

  @send external all: table => Promise.t<array<Db.row>> = "toArray"
  @send external toCollection: table => collection = "toCollection"
  @send external countAll: table => Promise.t<int> = "count"
  @send external count: collection => Promise.t<int> = "count"
  @send external allStringPrimaryKeys: collection => Promise.t<array<string>> = "primaryKeys"
  @send external allIntPrimaryKeys: collection => Promise.t<array<int>> = "primaryKeys"
  @send external limit: (table, int) => table = "limit"
  @send external toArray: collection => Promise.t<array<Db.row>> = "toArray"
  @send external deleteByStringPrimaryKey: (table, string) => Promise.t<int> = "delete"
  @send external deleteByIntPrimaryKey: (table, int) => Promise.t<int> = "delete"
  @send external deleteAll: collection => Promise.t<int> = "delete"

  @send external getByIntPrimaryKeyRaw: (table, ~id: int) => Promise.t<Nullable.t<Db.row>> = "get"
  let getByIntPrimaryKey = (table, ~id) =>
    table->getByIntPrimaryKeyRaw(~id)->Promise.thenResolve(Nullable.toOption)

  @send
  external getByStringPrimaryKeyRaw: (table, ~id: string) => Promise.t<Nullable.t<Db.row>> = "get"
  let getByStringPrimaryKey = (table, ~id) =>
    table->getByStringPrimaryKeyRaw(~id)->Promise.thenResolve(Nullable.toOption)

  @send external put: (table, Db.row) => Promise.t<int> = "put"
  @send external updateIntPrimaryKey: (table, ~k: int, ~values: Db.row) => Promise.t<int> = "update"
  @send
  external updateStringPrimaryKey: (table, ~k: string, ~values: Db.row) => Promise.t<int> = "update"

  let collection = table->where(Db.lookupKey)->equalsInt(1)
  let allValues = (
    string("id"),
    int(1),
    array([string("compound"), int(2)]),
    table->all,
    table->countAll,
    collection->count,
    collection->allStringPrimaryKeys,
    collection->allIntPrimaryKeys,
    table->limit(5)->toCollection->toArray,
    table->where(Db.lookupKey)->equalsBool(True)->deleteAll,
    table->where(Db.lookupKey)->equalsString("story")->toArray,
    table->deleteByStringPrimaryKey("story"),
    table->deleteByIntPrimaryKey(42),
    table->getByIntPrimaryKey(~id=42),
    table->getByStringPrimaryKey(~id="story"),
    table->put(Db.row),
    table->updateIntPrimaryKey(~k=42, ~values=Db.row),
    table->updateStringPrimaryKey(~k="story", ~values=Db.row),
  )
}

module StoriesDb = {
  type tableName = string
  type row = {id: int, title: string}
  type key = string

  let version = 3
  let dbName = "tella-output-parity"
  let stores = [("stories", "&id,title")]
  let tableName = "stories"
  let lookupKey = "id"
  let row = {id: 42, title: "Minimal"}
}

module Stories = Make(StoriesDb)

let output = Stories.allValues
