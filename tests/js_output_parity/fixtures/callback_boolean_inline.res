type state = Enabled | Disabled

type handler = {onChange: bool => unit}

@val external logEnabled: unit => unit = "logEnabled"
@val external logDisabled: unit => unit = "logDisabled"

let makeHandler = (state: state): handler => {
  let toggle = checked => {
    if checked {
      logEnabled()
    } else {
      logDisabled()
    }
  }
  {
    onChange: _checked => {
      switch state {
      | Enabled => toggle(false)
      | Disabled => toggle(true)
      }
    },
  }
}
