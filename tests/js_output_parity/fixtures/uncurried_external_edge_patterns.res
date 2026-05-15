@@uncurried

%%raw(`
const outputParityUncurriedScope = {
  somefn() {
    return "constant"
  }
}

function outputParityMakeTarget() {
  return {
    slot: 0,
    pair: [1, "one"],
    run() {
      return this.slot + 1
    },
    pipeRun() {
      return this.slot + 2
    },
    pipeNoUnit() {
      return this.slot + 3
    }
  }
}
`)

type rec kind<_> =
  | Int: kind<int>
  | Str: kind<string>

type target

@val external makeTarget: unit => target = "outputParityMakeTarget"

@new @module external makeModuleClass: string => target = "output-parity-class"

@obj
external makeOptions: (
  ~objectMode: @as(json`false`) _,
  ~level: @int [#low | #high]=?,
  ~name: string,
  unit,
) => _ = ""

@scope("outputParityUncurriedScope")
external constantArgOnly: @as(json`{foo:true}`) _ => string = "somefn"

@set external setWithIgnored: (target, @ignore kind<'a>, 'a) => unit = "slot"
@get external getWithIgnored: (target, @ignore kind<'a>) => 'a = "slot"

@get_index
external getPairAt: (target, @ignore kind<'a>, @ignore kind<'b>, int) => (
  'a,
  'b,
) = ""

@get_index
external getPairAtConst: (
  target,
  @ignore kind<'a>,
  @ignore kind<'b>,
  @as(3) _,
) => ('a, 'b) = ""

@set_index
external setPairAt: (
  target,
  @ignore kind<'a>,
  @ignore kind<'b>,
  int,
  ('a, 'b),
) => unit = ""

@set_index
external setPairAtConst: (
  target,
  @ignore kind<'a>,
  @ignore kind<'b>,
  @as(3) _,
  ('a, 'b),
) => unit = ""

@set
external setIncrement: (target, @this (target, int) => unit) => unit =
  "increment"

@send external sendUnit: (target, unit) => int = "run"
@send external sendPipeUnit: (target, unit) => int = "pipeRun"
@send external sendPipeNoUnit: target => int = "pipeNoUnit"

let optionsValue = (
  makeOptions(~name="plain", ()),
  makeOptions(~level=#high, ~name="ranked", ()),
)

let constantValue = constantArgOnly()

let exerciseTarget = target => {
  setWithIgnored(target, Int, 41)
  setPairAt(target, Int, Str, 0, (1, "one"))
  setPairAtConst(target, Str, Int, ("two", 2))
  setIncrement(target, @this (self, amount) => setWithIgnored(self, Int, amount))

  let slot: int = getWithIgnored(target, Int)
  let pair: (int, string) = getPairAt(target, Int, Str, 0)
  let pairConst: (string, int) = getPairAtConst(target, Str, Int)

  (
    slot,
    pair,
    pairConst,
    sendUnit(target, ()),
    target->sendPipeUnit(),
    target->sendPipeNoUnit,
  )
}

let targetValue = exerciseTarget(makeTarget())

let moduleClassValue = makeModuleClass("token")
