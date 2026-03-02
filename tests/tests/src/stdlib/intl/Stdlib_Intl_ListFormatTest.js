console.log()("---");

console.log()("Intl.ListFormat");

let _formatter = Intl.ListFormat()("None", "None");

let _formatter = Intl.ListFormat()("None", {TAG: "Some", _0: ["en-US", "en-GB"]});

let _formatter = Intl.ListFormat()({TAG: "Some", _0: {localeMatcher: "None", type: {TAG: "Some", _0: "conjunction"}, style: {TAG: "Some", _0: "long"}}}, {TAG: "Some", _0: ["en-US", "en-GB"]});

(prim => {
  
  
})(Intl.ListFormat.supportedLocalesOf()("None", ["en-US", "en-GB"]));

(prim => {
  
  
})(Intl.ListFormat.supportedLocalesOf()({TAG: "Some", _0: {localeMatcher: "lookup"}}, ["en-US", "en-GB"]));

let formatter = Intl.ListFormat()({TAG: "Some", _0: {localeMatcher: "None", type: {TAG: "Some", _0: "conjunction"}, style: {TAG: "Some", _0: "long"}}}, "None");

console.log()(resolvedOptions()(formatter));

console.log()(format()(["one", "two", "three"], formatter));

console.log()(formatToParts()(["one", "two", "three"], formatter));