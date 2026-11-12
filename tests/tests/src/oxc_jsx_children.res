@@config({flags: ["-bs-jsx", "4", "-bs-jsx-preserve"]})

let nested = (first, second, text) =>
  first ? <div> {React.string(text)} </div> : second ? <span> {React.string(text)} </span> : <></>

let groups = (enabled, text) => {
  let element = <span> {React.string(text)} </span>
  let elements = [<div> element </div>]
  (elements, enabled ? Some(<div> element </div>) : None)
}

let callbacks = (items, text) =>
  <div>
    {items->Array.map(item => {
      if item {
        <span> {React.string(text)} </span>
      } else {
        <div> <span> {React.string(text)} </span> </div>
      }
    })->React.array}
  </div>

let cases = (value, text) => {
  switch value {
  | 1 => <div> {React.string(text)} </div>
  | 2 => <span> {React.string(text)} </span>
  | _ => <div> <span> {React.string(text)} </span> </div>
  }
}

let nestedValue = (first, second, text) => {
  let child = first ? <div /> : second ? <span> {React.string(text)} </span> : <></>
  <div> child </div>
}

type childrenProps = {children: React.element}
let dynamic = (component: React.component<childrenProps>, text) => {
  module Local = {let make = component}
  <Local> <div> {React.string(text)} </div> </Local>
}

let list = text => list{<div> {React.string(text)} </div>}

let invoked = (first, text) => {
  let result = (first ? (_ => <div> {React.string(text)} </div>) : (_ => <span> {React.string(text)} </span>))(())
  (result, text)
}
