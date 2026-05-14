type props = {
  required: string,
  p01?: string,
  p02?: string,
  p03?: string,
  p04?: string,
  p05?: string,
  p06?: string,
  p07?: string,
  p08?: string,
  p09?: string,
  p10?: string,
  p11?: int,
  p12?: int,
  p13?: int,
  p14?: int,
  p15?: bool,
  p16?: bool,
  p17?: bool,
  p18?: bool,
}

let baseProps = {
  required: "root",
  p03: "visible",
  p12: 12,
  p17: true,
}

let copiedProps = {
  ...baseProps,
  p05: "copied",
  p13: 13,
}

let consumeProps = props =>
  switch (props.p03, props.p05, props.p17) {
  | (Some(left), Some(right), Some(true)) => left ++ right
  | (Some(left), _, _) => left
  | _ => props.required
  }

let packed = [baseProps, copiedProps]->Array.map(consumeProps)

module ComponentLike = {
  type config = {
    props: props,
    children?: array<string>,
  }

  let make = (~props, ~children=?, ()) => {
    props: props,
    children: ?children,
  }
}

let componentValue = ComponentLike.make(~props=copiedProps, ~children=["a", "b"], ())
