let createDomElement = (s, props, children) => {
  let vararg = Js.Array.concat([(prim => prim)(s), (prim => prim)(props)], children);
  return undefined(vararg, null);
};

let anyToUnit = _arg0 => "()";

let anyToTrue = _arg0 => true;

let willReceivePropsDefault = _arg0 => state;

let renderDefault = _self => string("RenderNotImplemented");

let initialStateDefault = _arg0 => "()";

let reducerDefault = (_action, _state) => "NoUpdate";

let convertPropsIfTheyreFromJs = (props, jsPropsToReason, debugName) => {
  let props = (prim => prim)(props);
  let match = [undefined, jsPropsToReason];
  let tuple = match;
  let ctor = tuple[0];
  let ifres;
  if (ctor.TAG === "Some") {
    let props = ctor._0;
    ifres = props;
  } else {
    let tuple = match;
    let ifres;
    if (tuple[0] === "None") {
      let ctor = tuple[1];
      let ifres;
      if (ctor.TAG === "Some") {
        let toReasonProps = ctor._0;
        ifres = {TAG: "Element", _0: toReasonProps(props)};
      } else {
        let tuple = match;
        let ifres;
        if (tuple[0] === "None") {
          let ifres;
          if (tuple[1] === "None") {
            throw ["A JS component called the Reason component " + (debugName + " which didn't implement the JS->Reason React props conversion.")];
            ifres = undefined;
          } else {
            ifres = undefined;
          }
          ifres = ifres;
        } else {
          ifres = undefined;
        }
        ifres = ifres;
      }
      ifres = ifres;
    } else {
      let tuple = match;
      let ifres;
      if (tuple[0] === "None") {
        let ifres;
        if (tuple[1] === "None") {
          throw ["A JS component called the Reason component " + (debugName + " which didn't implement the JS->Reason React props conversion.")];
          ifres = undefined;
        } else {
          ifres = undefined;
        }
        ifres = ifres;
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let createClass = prim => prim;

let basicComponent = debugName => {
  let componentTemplate = {debugName: debugName, reactClassInternal: createClass(debugName), handedOffState: {contents: "None"}, willReceiveProps: willReceivePropsDefault, didMount: anyToUnit, didUpdate: anyToUnit, willUnmount: anyToUnit, willUpdate: anyToUnit, shouldUpdate: anyToTrue, render: renderDefault, initialState: initialStateDefault, retainedProps: "()", reducer: reducerDefault, jsElementWrapped: "None"};
  return componentTemplate;
};

let statelessComponent = debugName => basicComponent(debugName);

let statelessComponentWithRetainedProps = debugName => basicComponent(debugName);

let reducerComponent = debugName => basicComponent(debugName);

let reducerComponentWithRetainedProps = debugName => basicComponent(debugName);

let element = *opt* => {
  let ctor = *opt*;
  let ifres;
  if (ctor.TAG === "Some") {
    let *sth* = ctor._0;
    ifres = *sth*;
  } else {
    ifres = *opt* === "None" ? (prim => prim)(undefined) : undefined;
  }
  let key = ifres;
  return *opt* => {
    let ctor = *opt*;
    let ifres;
    if (ctor.TAG === "Some") {
      let *sth* = ctor._0;
      ifres = *sth*;
    } else {
      ifres = *opt* === "None" ? (prim => prim)(undefined) : undefined;
    }
    let ref = ifres;
    return _arg0 => {
      let element = {TAG: "Element", _0: component};
      let match = component.jsElementWrapped;
      let ctor = match;
      let ifres;
      if (ctor.TAG === "Some") {
        let jsElementWrapped = ctor._0;
        ifres = jsElementWrapped((prim => prim)(ref), (prim => prim)(key));
      } else {
        ifres = match === "None" ? createElement([], {TAG: "Some", _0: ()(element, ref, key)}, component.reactClassInternal) : undefined;
      }
      return ifres;
    };
  };
};

let wrapReasonForJs = (component, _arg1) => {
  let jsPropsToReason = (prim => prim)(jsPropsToReason);
  let uncurriedJsPropsToReason = jsProps => jsPropsToReason(jsProps);
  undefined({TAG: "Some", _0: uncurriedJsPropsToReason});
  return component.reactClassInternal;
};

let wrapJsForReason = WrapProps.wrapJsForReason;