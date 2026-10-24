%%private(let frame = x => <div className=x />)

let y = %raw(`1`)

module M = {
  %%private(
    @react.component
    let make = (~a) => <span> {React.string(a)} </span>
  )
  let el = <make a="b" />
}

let wrapped = %ext(<div />)
