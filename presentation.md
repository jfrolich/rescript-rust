
# Rescript 12

Last year Rescript 12 was released. 


Big milestone. Finally feels like a mature language.


The thing I worked on, Rewatch was upstreamed. ReScript now has it's own bespoke build system and file watcher.



We achieved a 2-3x speed up in net build times, and support for monorepos using full backward compatibility of bsb (backed by ninja). No changes in the compiler itself.


And it can enable some really cool new features.



# What makes ReScript interesting?

A single thing that draws people in

- For everyone it's something different
- For me: Backend <-> Frontend typesafety using GraphQL and graphql-ppx


What is it in 2026 and beyond?


What is the future of programming languages?


In the early days of LLMs we thought languages with a large training sample would thrive


Now LLMs can write niche languages like Zig and ReScript very well, and they especially thrives in strongly typed languages such as Rust in larger code bases


But... maybe that will also change and at some point llms will write binary code or Webassembly directly.



# Rust compiler experiment


I'd like to introduce you to an experiment.









> Can you rewrite the ReScript compiler in Rust?
* Flibbertigibbeting








Why is rewriting a compiler using an LLM in another language a great fit for current LLMs:


- Clear success critera, see if the AST or IRs are exactly the same given the same input
- Hill climbing (measure progress): you start at 0% but there are a lot of small steps in-between.
- There are a lot of tools for the LLM to know how to improve:
   - Read the source of the reference program and the new one
   - Use a CLI to inspect differences in output
   - Add debug logging and tracing

This is basically the idea behind AutoResearch of Andre Karpathy.




I spent the equivalent of $15k in tokens to build a rescript compiler in Rust.

Note: It's not done yet, but I have an early demo


~ 200kloc Rust code



# Why?

It would be great to have a more integrated build system and compiler.

Ideally it should be a single program.

Aside from performance I think it has a lot of advantages, but especially if we want to make a fast compiler it should be a single program.



To make a really fast compiler you need to:
  - Don't write intermediate results to disk
  - Eliminate subprocess overhead
  - Optimize data structures



We are currently @ ~15kloc/s
Go: 50kloc/s
Jai: 250kloc/s
C: 100kloc/s
Zig: 15kloc/s
TinyCC: 500kloc/s
TypeScript: 20kloc
TypeScript (tsgo): 200kloc/s


I think it would be great to beat tsgo!


One direction would be to rewrite everything in OCaml
 
  - Immature parallelism
  - Performance is not bad, but there is a ceiling
  - Not a great ecosystem
  - Still a lot that needs to change, the current compiler is designed for out of process execution



Before LLMs rewriting the compiler in Rust would be impractical (maybe even insane).


ReScript was bootstrapped off the OCaml typechecker


After ReasonML ReScript went into it's own direction.


I think it's time to **graduate** and have our own compiler (in Rust).


For people that like OCaml: Rust is just an OCaml dialect that has lower level capabilities.



Why a fast compiler:
- Iteration speed is important with agentic engineering
- Feedback loop needs to be as fast as posible
- CI needs to be as fast as possible
- Rescript takes 15s on the Tella codebase; 250kloc




I think the reason why people would adopt ReScript in 2026 and beyond is 100% because it will be the best choice in an agentic workflow.


Like when GraphQL was the new thing, and ReScript was the language that had the best typed query generation.


Agents are slow now, but if they become fast, there is a lot of advantage that the other tooling is also really fast.



Why not TypeScript?


  - The typesystem is complex and less typesafe
  - Performance very easily crumbles in large codebases


The largest barrier for adoption is gone:


  - People don't have to learn it anymore
  - If it results in more solid programs & has faster tooling there is a lot of reason to adopt it.


## Experiment 2: Comptime

I think the largest problem and the largest opportunity with the ReScript language is the state of metaprogramming

You need metaprogramming for:

- Json parse/serialize
- GraphQL type generation
- Type deriving
- Embed lang
- Form generation
- CSS in JS


Why we need to get rid of PPXs

- We can never be a fast compiler with PPX in the current form
- We can not easily advance the compiler with PPX in the current form
- It's just too hard to create a PPX if you need metaprogramming



Metaprogramming usually sucks if you are in a typed language (non homoiconic). But there is one language that I think did a great job at it: Zig. It adds compile time evaluation as a core primitive of the language. 



```rescript
let rec encode = (@comptime type t, value: t): JSON.t => {
  switch @typeInfo(@typeOf(value)) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    fields->Array.forEach(field => {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    })
    JSON.Encode.object(dict)
  | Variant({constructors}) =>
    let result = ref(JSON.Null)
    constructors->Array.forEach(c => {
      if @hasTag(value, c.name) {
        let arr = [JSON.Encode.string(c.name)]
        c.args->Array.forEachWithIndex((argType, i) => {
          Array.push(arr, encode(@argAt(value, i, argType)))
        })
        result := JSON.Encode.array(arr)
      }
    })
    result.contents
  | Array(_) => JSON.Encode.array(Array.map(value, v => encode(v)))
  | _ => @compileError("encode: unsupported type")
  }
}
```

```rescript
let alice: user = {
  name: "Alice",
  age: 30,
  active: true,
  status: Active,
  address: {street: "Main St", city: "NYC"},
}

let aliceJson = encode(user, alice)
```


```javascript
let alice_address = {
  street: "Main St",
  city: "NYC"
};

let alice = {
  name: "Alice",
  age: 30,
  active: true,
  status: "Active",
  address: alice_address
};

let aliceJson = encode$user(alice);

function encode$status(value) {
  let result = null;
  if ((function(v, n) { return (typeof v === "string" ? v : v.TAG) === n; })(value, "Active")) {
    let arr = ["Active"];
    result = arr;
  }
  if ((function(v, n) { return (typeof v === "string" ? v : v.TAG) === n; })(value, "Inactive")) {
    let arr$1 = ["Inactive"];
    result = arr$1;
  }
  if ((function(v, n) { return (typeof v === "string" ? v : v.TAG) === n; })(value, "Pending")) {
    let arr$2 = ["Pending"];
    result = arr$2;
  }
  return result;
}

function encode$address(value) {
  let dict = {};
  dict["street"] = encode$string(value.street);
  dict["city"] = encode$string(value.city);
  return dict;
}

function encode$user(value) {
  let dict = {};
  dict["name"] = encode$string(value.name);
  dict["age"] = encode$int(value.age);
  dict["active"] = encode$bool(value.active);
  dict["status"] = encode$status(value.status);
  dict["address"] = encode$address(value.address);
  return dict;
}
```

```rescript
exception DecodeErr(string)

@comptime
let rec decode = (type t, json: JSON.t): result<t, string> => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => Ok(s) | _ => Error("expected string") }
  | Int =>
    switch json { | Number(n) => Ok(Float.toInt(n)) | _ => Error("expected int") }
  | Bool =>
    switch json { | Boolean(b) => Ok(b) | _ => Error("expected bool") }
  | Record({fields}) =>
    switch json {
    | Object(dict) =>
      try Ok(@record(t, fields->Array.map(field =>
        switch decode(field.typ, Dict.getUnsafe(dict, field.name)) {
        | Ok(v) => v
        | Error(e) => throw(DecodeErr(e))
        }
      ))) catch {
      | DecodeErr(e) => Error(e)
      }
    | _ => Error("expected object")
    }
  | Variant({constructors}) =>
    switch json {
    | Array(items) =>
      switch items[0] {
      | Some(String(name)) => {
          let result = ref(Error("unknown variant: " ++ name))
          constructors->Array.forEach(c => {
            if name == c.name { result := Ok(@constructor(t, c.name)) }
          })
          result.contents
        }
      | _ => Error("expected [name, ...] array")
      }
    | _ => Error("expected variant array")
    }
  | _ => @compileError("decode: unsupported type")
  }
}
```

```javascript
let decodedAlice = decode$user(aliceJson);

function decode$user(json) {
  if (typeof json !== "object" || json === null || Array.isArray(json)) {
    return {
      TAG: "Error",
      _0: "expected object"
    };
  }
  let err;
  let e = err;
  if (e !== undefined) {
    return {
      TAG: "Error",
      _0: e
    };
  } else {
    let v = decode$string(json["name"]);
    let tmp;
    if (v.TAG === "Ok") {
      tmp = v._0;
    } else {
      if (err === undefined) {
        err = v._0;
      }
      tmp = ;
    }
    let v$1 = decode$int(json["age"]);
    let tmp$1;
    if (v$1.TAG === "Ok") {
      tmp$1 = v$1._0;
    } else {
      if (err === undefined) {
        err = v$1._0;
      }
      tmp$1 = ;
    }
    let v$2 = decode$bool(json["active"]);
    let tmp$2;
    if (v$2.TAG === "Ok") {
      tmp$2 = v$2._0;
    } else {
      if (err === undefined) {
        err = v$2._0;
      }
      tmp$2 = ;
    }
    let v$3 = decode$status(json["status"]);
    let tmp$3;
    if (v$3.TAG === "Ok") {
      tmp$3 = v$3._0;
    } else {
      if (err === undefined) {
        err = v$3._0;
      }
      tmp$3 = ;
    }
    let v$4 = decode$address(json["address"]);
    let tmp$4;
    if (v$4.TAG === "Ok") {
      tmp$4 = v$4._0;
    } else {
      if (err === undefined) {
        err = v$4._0;
      }
      tmp$4 = ;
    }
    return {
      TAG: "Ok",
      _0: {
        name: tmp,
        age: tmp$1,
        active: tmp$2,
        status: tmp$3,
        address: tmp$4
      }
    };
  }
}
```


```rescript
type user = { name: string, age: int, active: bool, status: status, address: address }

@comptime
let keys = (type t) => 
  switch @typeInfo(t) {
  | Record({fields}) =>
    @buildType(Variant({
      constructors: fields->Array.map(field => {name: field.name}),
    }))
  | _ => @compileError("expected record")
  }

type userKeys = keys(user)

let k1: userKeys = Name
let k2: userKeys = Age
```


type -> type
type -> value
type + value -> value
value -> type

(type, type) -> type 




```rescript
@comptime
let partial = (type t) =>
  switch @typeInfo(t) {
  | Record({fields}) =>
    @buildRecord(fields->Array.map(field =>
      @recordField({...field, optional: true})
    ))
  | _ => @compileError("partial: expected record")
  }

@comptime
let partialUser = partial(user)

let patch: partialUser = { name: "Alice" }
```


```rescript
@comptime.inline
let upperCase = (value) => String.toUpperCase(value)

let upperStr = upperCase("Bla")
```

```javascript
let upperStr = "BLA"
```


```rescript
type rec typeInfo = 
| Int 
| Float 
| String 
| Bool 
| Unit 
| Char
| Bigint
| Record({name: string, fields: array<fieldInfo>, unboxed: bool})
| Variant({name: string, constructors: array<constructorInfo>, unboxed: bool})
| Array({element: typeInfo}) 
| Option({inner: typeInfo})
| Function({args: array<typeInfo>, returnType: typeInfo})
| External({name: string}) 
| Opaque({name: string}) 
| TiUnknown
and fieldInfo = { 
    name: string, 
    typ: typeInfo, 
    optional: bool, 
    mutable_: bool 
}
and constructorInfo = { 
    name: string, 
    args: array<typeInfo> 
}
```

```rescript
// Recursive types: encode$tree calls itself via Array.map.
let myTree: tree = {
  value: "root",
  children: [
    {value: "child1", children: []},
    {value: "child2", children: []},
  ],
}
let treeJson = encode(myTree)
```

```javascript
function encode$array_tree(value) {
  return value.map(v => encode$tree(v));
}

function encode$tree(value) {
  let dict = {};
  dict["value"] = value.value;
  dict["children"] = encode$array_tree(value.children);
  return dict;
}
```