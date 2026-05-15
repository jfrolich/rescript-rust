module React = {
  type element = Jsx.element
  type component<'props> = Jsx.component<'props>

  let null: element = %raw("null")
  external string: string => element = "%identity"
  external array: array<element> => element = "%identity"
  @module("react/jsx-runtime") external jsx: (component<'props>, 'props) => element = "jsx"
  @module("react/jsx-runtime")
  external jsxKeyed: (component<'props>, 'props, ~key: string=?, @ignore unit) => element = "jsx"
  @module("react/jsx-runtime") external jsxs: (component<'props>, 'props) => element = "jsxs"
  @module("react/jsx-runtime")
  external jsxsKeyed: (
    component<'props>,
    'props,
    ~key: string=?,
    @ignore unit,
  ) => element = "jsxs"
  type fragmentProps = {children?: element}
  @module("react/jsx-runtime") external jsxFragment: component<fragmentProps> = "Fragment"
}

module ReactDOM = {
  type domProps = JsxDOM.domProps

  @module("react/jsx-runtime") external jsx: (string, domProps) => Jsx.element = "jsx"
  @module("react/jsx-runtime") external jsxs: (string, domProps) => Jsx.element = "jsxs"
  @module("react/jsx-runtime")
  external jsxKeyed: (
    string,
    domProps,
    ~key: string=?,
    @ignore unit,
  ) => Jsx.element = "jsx"
  @module("react/jsx-runtime")
  external jsxsKeyed: (
    string,
    domProps,
    ~key: string=?,
    @ignore unit,
  ) => Jsx.element = "jsxs"
}

module Cmdk = {
  module Dialog = {
    @module("cmdk") @scope("Command") @react.component
    external make: (
      ~children: React.element,
      ~className: string=?,
      ~label: string=?,
      ~isOpen: bool,
      ~onOpenChange: bool => unit=?,
    ) => React.element = "Dialog"
  }

  module Item = {
    @module("cmdk") @scope("Command") @react.component
    external make: (
      ~children: React.element,
      ~className: string=?,
      ~disabled: bool=?,
      ~onSelect: string => unit=?,
      ~value: string=?,
      ~keywords: array<string>=?,
      ~forceMount: bool=?,
    ) => React.element = "Item"
  }
}

module BaseDialog = {
  module Root = {
    @react.component @module("@base-ui/react/dialog") @scope("Dialog")
    external make: (
      ~children: React.element,
      ~\"open": bool=?,
      ~defaultOpen: bool=?,
      ~onOpenChange: (bool, 'eventDetails) => unit=?,
      ~modal: bool=?,
      ~dismissible: bool=?,
    ) => React.element = "Root"
  }

  module Trigger = {
    @react.component @module("@base-ui/react/dialog") @scope("Dialog")
    external make: (
      ~children: React.element=?,
      ~className: string=?,
      ~render: React.element=?,
    ) => React.element = "Trigger"
  }
}

module Embed = {
  @module("@dub/embed-react") @react.component
  external make: (~data: [#referrals | #analytics], ~token: string) => React.element =
    "DubEmbed"
}

let onOpenChange = (_open, _details) => ()
let onSelect = value => Console.log(value)

let commandDialog =
  <Cmdk.Dialog isOpen=true className="palette" onOpenChange={_ => ()}>
    <Cmdk.Item value="copy" keywords={["copy", "duplicate"]} onSelect={onSelect}>
      {React.string("Copy")}
    </Cmdk.Item>
  </Cmdk.Dialog>

let baseDialog =
  <BaseDialog.Root \"open"=true defaultOpen=false modal=true onOpenChange={onOpenChange}>
    <BaseDialog.Trigger className="trigger" />
  </BaseDialog.Root>

let embed = <Embed data=#analytics token="token" />

let fragment = <>
  {commandDialog}
  {baseDialog}
  {embed}
</>

let allValues = (commandDialog, baseDialog, embed, fragment)
