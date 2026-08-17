let invoke: (module(Provider.Interface), unit) => unit =
  (module(Reducer), ()) => Reducer.handleEffect()
