module ProviderAlias = AProvider

type local = {
  message: string,
  nested: int,
}

let build = () => {
  let item = AProvider.make(~name="consumer", ~count=3)
  let payloadItem = AProvider.fromPayload({name: "payload", count: 4, tag: "tag"})

  {
    message: AProvider.label(item) ++ ":" ++ AProvider.label(payloadItem),
    nested: AProvider.Nested.value(AProvider.Nested.make(5)),
  }
}

let consumeExported = () => {
  let (item, code) = AProvider.exportedTuple
  (AProvider.label(item), code, ProviderAlias.classify(#Secondary))
}

let allValues = (build(), consumeExported())
