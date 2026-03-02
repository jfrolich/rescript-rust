let undefined = undefined;

let act = func => {
  let reactFunc = _arg0 => {
    func("()");
    return undefined;
  };
  return reactAct(reactFunc);
};

let actAsync = func => {
  let reactFunc = _arg0 => func("()");
  return reactActAsync(reactFunc);
};

let querySelectorAll = (element, string) => Array.from()(querySelectorAll(string, element));

let prepareContainer = (_arg0, _arg1) => {
  let containerElement = createElement("div", document);
  return %refset()({TAG: "Some", _0: containerElement}, container);
};

let cleanupContainer = (_arg0, _arg1) => %refset()("None", container);

let getContainer = container => Belt.Option.getExn(container.contents);