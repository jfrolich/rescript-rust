module Tab = {
  type id = int
  type t = {
    id: id,
    url: string,
    width: float,
    height: float,
  }

  @get external favIconUrlRaw: t => option<string> = "favIconUrl"

  let favIconUrl = tab =>
    switch tab->favIconUrlRaw {
    | None
    | Some("") => None
    | icon => icon
    }
}

module ChromeRuntime = {
  type response = {ok: bool}
  type port

  type streamValue = {streamId: string}
  type messageEvent = {
    value: streamValue,
    stopRecording: bool,
  }

  type installedEvent = {reason: [#install | #update | #chrome_update | #shared_module_update]}

  @val @scope(("chrome", "runtime"))
  external sendMessage: (string, 'payload, response => unit) => unit = "sendMessage"

  @val @scope(("chrome", "runtime"))
  external connect: (string, 'options) => port = "connect"

  @send external postMessage: (port, 'payload) => unit = "postMessage"

  @scope("onMessage") @send
  external addListenerOnMessage: (port, messageEvent => unit) => unit = "addListener"

  @scope("onDisconnect") @send
  external addListenerOnDisconnect: (port, unit => unit) => unit = "addListener"

  @val @scope(("chrome", "runtime", "onInstalled"))
  external addInstalledListener: (installedEvent => unit) => unit = "addListener"

  @val @scope(("chrome", "runtime"))
  external lastError: option<{message: string}> = "lastError"

  let connectAndListen = () => {
    let port = connect("recorder", {"name": "capture"})
    addListenerOnMessage(port, event => {
      if event.stopRecording {
        postMessage(port, {"kind": "stop", "streamId": event.value.streamId})
      } else {
        postMessage(port, {"kind": "continue"})
      }
    })
    addListenerOnDisconnect(port, () => Console.log(lastError))
    port
  }

  let notify = payload =>
    sendMessage("extension-id", payload, response => {
      if !response.ok {
        Console.warn(lastError)
      }
    })
}

module ChromeOffscreen = {
  type reason = [
    | #TESTING
    | #AUDIO_PLAYBACK
    | #IFRAME_SCRIPTING
    | #DOM_SCRAPING
    | #BLOBS
    | #LOCAL_STORAGE
  ]

  type createParameters = {
    url: string,
    reasons: array<reason>,
    justification: string,
  }

  type context = {
    contextId: string,
    contextType: [#BACKGROUND | #POPUP | #TAB | #OFFSCREEN_DOCUMENT],
    documentUrl: string,
  }

  type filter = {}

  @val @scope(("chrome", "offscreen"))
  external createDocument: createParameters => promise<unit> = "createDocument"

  @val @scope(("chrome", "offscreen"))
  external closeDocument: unit => promise<unit> = "closeDocument"

  @val @scope(("chrome", "runtime"))
  external getContexts: filter => promise<array<context>> = "getContexts"

  let ensure = async (~url, ~justification) => {
    let contexts = await getContexts({})
    let existing = contexts->Array.find(item => item.contextType == #OFFSCREEN_DOCUMENT)
    if existing->Option.isNone {
      await createDocument({
        url,
        reasons: [#DOM_SCRAPING, #LOCAL_STORAGE],
        justification,
      })
    }
  }
}

module ChromeStorage = {
  type data<'a> = {value: 'a}

  @val @scope(("chrome", "storage", "local"))
  external get: (array<string>, option<data<'a>> => unit) => unit = "get"

  @val @scope(("chrome", "storage", "local"))
  external set: data<'a> => unit = "set"

  @val @scope(("chrome", "storage", "local"))
  external remove: string => unit = "remove"

  let getValue = key =>
    Promise.make((resolve, _reject) => {
      get([key], data => resolve(data->Option.map(item => item.value)))
    })

  let saveAndDrop = item => {
    set(item)
    remove("old-value")
  }
}

module Svix = {
  type t

  @new @module("svix") external make: string => t = "Svix"

  type applicationOptions = {
    name: string,
    uid?: string,
  }

  type application = {
    id: string,
    name: string,
    uid: option<string>,
  }

  module Application = {
    @send @scope("application")
    external create: (t, applicationOptions) => promise<application> = "create"

    @send @scope("application")
    external getOrCreate: (t, applicationOptions) => promise<application> = "getOrCreate"

    @send @scope("application")
    external delete_: (t, string) => promise<unit> = "delete"
  }

  type messageOptions = {
    eventType: string,
    eventId?: string,
    payload: JSON.t,
  }

  module Message = {
    @send @scope("message")
    external create: (t, string, messageOptions) => promise<JSON.t> = "create"
  }

  @val @scope(("process", "env")) @return(nullable)
  external svixApiKey: option<string> = "SVIX_API_KEY"

  let configuredClient = () =>
    switch svixApiKey {
    | Some(key) => Some(make(key))
    | None => None
    }
}

let tabIcon = Tab.favIconUrl({
  id: 1,
  url: "https://tella.tv",
  width: 1280.0,
  height: 720.0,
})

let runtimeListener =
  ChromeRuntime.addInstalledListener(event => Console.log(event.reason))

let chromePort = ChromeRuntime.connectAndListen()
let runtimeNotification = ChromeRuntime.notify({"kind": "ping"})
let offscreenReady = ChromeOffscreen.ensure(~url="/offscreen.html", ~justification="capture")
let offscreenClosed = ChromeOffscreen.closeDocument()
let storedValue = ChromeStorage.getValue("session-id")
let storageWrite = ChromeStorage.saveAndDrop({value: "new-session"})
let maybeSvixClient = Svix.configuredClient()

let svixResult =
  switch maybeSvixClient {
  | Some(client) =>
    Svix.Application.create(client, {name: "Tella", uid: "app_123"})
  | None =>
    let missing: Svix.application = {id: "missing", name: "missing", uid: None}
    Promise.resolve(missing)
  }

let svixGetOrCreate =
  switch maybeSvixClient {
  | Some(client) => Svix.Application.getOrCreate(client, {name: "Tella"})
  | None =>
    let missing: Svix.application = {id: "missing", name: "missing", uid: None}
    Promise.resolve(missing)
  }

let svixDelete =
  switch maybeSvixClient {
  | Some(client) => Svix.Application.delete_(client, "app_123")
  | None => Promise.resolve()
  }

let svixMessage =
  switch maybeSvixClient {
  | Some(client) =>
    let payload: JSON.t = %raw(`({kind: "app.created"})`)
    Svix.Message.create(client, "app_123", {
      eventType: "app.created",
      eventId: "evt_1",
      payload,
    })
  | None => Promise.resolve(%raw(`({})`))
  }

let output = (
  tabIcon,
  runtimeListener,
  chromePort,
  runtimeNotification,
  offscreenReady,
  offscreenClosed,
  storedValue,
  storageWrite,
  svixResult,
  svixGetOrCreate,
  svixDelete,
  svixMessage,
)
