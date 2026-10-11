%%raw(`
function outputParityUseCallback(cb) {
  return cb
}
`)

external ignorePromise: promise<'a> => unit = "%identity"

@val external useCallback: ('input => 'output) => 'input => 'output =
  "outputParityUseCallback"

type pluginContext
type changeEvent

type watcher = {
  watch: @this (pluginContext, string, changeEvent) => promise<unit>,
}

let methodWithAsync = @this receiver => async amount => receiver + amount

let makeWatcher = () => {
  watch: @this
  async (context, name, _event) => {
    Console.log2(name, context)
  },
}

let invokeInlineAsync = () =>
  ignore(
    (
      async amount => {
        let label = await Promise.resolve("callback")
        Console.log2(label, amount)
      }
    )(7),
  )

let scopedLoopAsync = async () => {
  for index in 0 to 3 {
    let asyncClosureAccessingScopedValue = async () => {
      Console.log2("loop", index)
      await Promise.resolve()
    }

    await asyncClosureAccessingScopedValue()
  }
}

let nestedAsyncFactory = () => async value => {
  await value
}

let callbackFromAsync = () =>
  useCallback(async value => {
    await value
  })

let watcherValue = makeWatcher()

let inlineAsyncValue = invokeInlineAsync

let scopedLoopAsyncValue = scopedLoopAsync()->ignorePromise

let nestedAsyncValue = nestedAsyncFactory()(Promise.resolve(1))

let callbackAsyncValue = callbackFromAsync()(Promise.resolve(3))
