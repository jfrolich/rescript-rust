/*

Last year Rescript 12 was released. 


Big milestone. Finally feels like a mature language.


The thing I worked on Rewatch was upstreamed. ReScript now has it's own bespoke build system and file watcher.

We achieved a 2-3x speed up in net build times, and support for monorepos using full backward compatibility of bsb (backed by ninja). No changes in the compiler itself.

I talked last year about making rewatch the entry point of the compiler - and a lot of great stuff is happening around that (deamon).



What makes ReScript interesting?


A single thing that draws people in

- For everyone it's something different
- Backend <-> Frontend typesafety using GraphQL and graphql-ppx


What is it in 2026 and beyond?


What is the future of programming languages?


In the early days of LLMs we thought languages with a large training sample would thrive


Now LLMs can write niche languages like Zig and ReScript very well, and they especially thrives in strongly typed languages such as Rust in larger code bases


But... maybe that will also change and at some point llms will write binary code or Webassembly directly.


In this talk I'd like to introduce you to my experiment.


A few months ago I started like this:

> Can you rewrite the ReScript compiler in Rust?


Why is rewriting a compiler using an LLM in another language a great fit for current LLMs:


- Clear success critera, see if the AST or IRs are exactly the same given the same input
- Hill climbing (measure progress): you start at 0% but there are a lot of small steps in-between.
- There are a lot of tools for the LLM to know how to improve:
   - Read the source of the reference program and the new one
   - Use a CLI to inspect differences in output
   - Add debug logging and tracing

This is basically the idea behind AutoResearch of Andre Karpathy.




I spend the equivalent of $15k in tokens to build a rescript compiler in Rust.

Note: It's not done yet, but I have an early demo


~ 200kloc Rust code

Written mostly autonomously with supervision sessions once in a while


Why?


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


After ReasonML it went into it's own direction.


I think it's time to graduate and have our own compiler (in Rust).


For people that like OCaml: Rust is just an OCaml dialect that has lower level capabilities.



Why a fast compiler:
- Iteration speed is important with agentic engineering
- Feedback loop needs to be as fast as posible
- CI needs to be as fast as possible
- Rescript takes 15s on the Tella codebase; 250kloc




I think the reason why people would adopt ReScript in 2026 and beyond is 100% because it will be the best choice in an agentic workflow.


Like when GraphQL was the new thing, and ReScript was the language that had the best typed query generation.


Agents are slow now, but if they become fast, there is a lot of advantage that the other tooling is also really fast.

There's also a few other properties working in our advantage:

  - Fast at scale (it doesn't crumble at huge code bases)
  - Very strict type system


Why not TypeScript?

  - The typesystem is complex and less typesafe
  - Performance very easily crumbles in large codebases

The largest barrier for adoption is gone:

  - People don't have to learn it anymore
  - If it results in more solid programs & has faster tooling there is a lot of reason to adopt it.


Comptime.


I think the largest problem and the largest opportunity with the rescript language is the state of metaprogramming

You need metaprogramming for:

- Json parse/serialize
- GraphQL type generation
- Type deriving
- Embed lang

It's really important to get rid of PPX

- We can never be a fast compiler with PPX in the current form
- We can not easily advance the compiler with PPX in the current form
- It's just too hard to create a PPX if you need metaprogramming



Metaprogramming usually sucks if you are in a typed language (non homoiconic). But there is one language that I think did a great job at it: Zig. It adds compile time evaluation as a core primitive of the language. 


To accomplish something like that in ReScript it would be GREAT if the build system and all compile iterations are a single program.










 */