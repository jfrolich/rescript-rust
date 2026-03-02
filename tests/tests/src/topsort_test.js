let graph = {TAG: "::", _0: ["a", "b"], _1: {TAG: "::", _0: ["a", "c"], _1: {TAG: "::", _0: ["a", "d"], _1: {TAG: "::", _0: ["b", "e"], _1: {TAG: "::", _0: ["c", "f"], _1: {TAG: "::", _0: ["d", "e"], _1: {TAG: "::", _0: ["e", "f"], _1: {TAG: "::", _0: ["e", "g"], _1: "[]"}}}}}}}};

let nexts = (_arg0, _arg1) => Belt.List.reduce((acc, _arg1) => %equal()(x, a) ? {TAG: "::", _0: b, _1: acc} : acc, "[]", g);

let dfs1;

dfs1 = (nodes, graph, visited) => {
  let ifres;
  if (nodes === "[]") {
    ifres = Belt.List.reverse(visited);
  } else {
    let ctor = nodes;
    let ifres;
    if (ctor.TAG === "::") {
      let x = ctor._0;
      let xs = ctor._1;
      let ifres;
      if (Belt.List.has(%equal(), x, visited)) {
        ifres = dfs1(visited, graph, xs);
      } else {
        console.log()(x);
        ifres = dfs1({TAG: "::", _0: x, _1: visited}, graph, Pervasives["@"](xs, nexts(graph, x)));
      }
      ifres = ifres;
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let ifres;

if (%equal()({TAG: "::", _0: "a", _1: {TAG: "::", _0: "d", _1: {TAG: "::", _0: "e", _1: {TAG: "::", _0: "g", _1: {TAG: "::", _0: "f", _1: {TAG: "::", _0: "c", _1: {TAG: "::", _0: "b", _1: "[]"}}}}}}}, dfs1("[]", graph, {TAG: "::", _0: "a", _1: "[]"}))) {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}



console.log()("()");

let ifres;

if (%equal()({TAG: "::", _0: "b", _1: {TAG: "::", _0: "e", _1: {TAG: "::", _0: "g", _1: {TAG: "::", _0: "f", _1: {TAG: "::", _0: "d", _1: "[]"}}}}}, dfs1("[]", {TAG: "::", _0: ["f", "d"], _1: graph}, {TAG: "::", _0: "b", _1: "[]"}))) {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}

let ifres;

if (ifres === "()") {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}



let dfs2;

dfs2 = (nodes, graph, visited) => {
  let aux;
  aux = (nodes, graph, visited) => {
    let ifres;
    if (nodes === "[]") {
      ifres = visited;
    } else {
      let ctor = nodes;
      let ifres;
      if (ctor.TAG === "::") {
        let x = ctor._0;
        let xs = ctor._1;
        ifres = Belt.List.has(%equal(), x, visited) ? aux(visited, graph, xs) : aux(aux({TAG: "::", _0: x, _1: visited}, graph, nexts(graph, x)), graph, xs);
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    return ifres;
  };
  return Belt.List.reverse(aux(visited, graph, nodes));
};

let dfs1 = dfs2;

let ifres;

if (%equal()({TAG: "::", _0: "a", _1: {TAG: "::", _0: "d", _1: {TAG: "::", _0: "e", _1: {TAG: "::", _0: "g", _1: {TAG: "::", _0: "f", _1: {TAG: "::", _0: "c", _1: {TAG: "::", _0: "b", _1: "[]"}}}}}}}, dfs1("[]", graph, {TAG: "::", _0: "a", _1: "[]"}))) {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}



let ifres;

if (%equal()({TAG: "::", _0: "b", _1: {TAG: "::", _0: "e", _1: {TAG: "::", _0: "g", _1: {TAG: "::", _0: "f", _1: {TAG: "::", _0: "d", _1: "[]"}}}}}, dfs1("[]", {TAG: "::", _0: ["f", "d"], _1: graph}, {TAG: "::", _0: "b", _1: "[]"}))) {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}

let ifres;

if (ifres === "()") {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}



let dfs3 = (nodes, graph) => {
  let visited = %makeref()("[]");
  let aux;
  aux = (node, graph) => {
    let ifres;
    if (!Belt.List.has(%equal(), node, visited.contents)) {
      %refset()({TAG: "::", _0: node, _1: visited.contents}, visited);
      ifres = Belt.List.forEach(x => aux(graph, x), nexts(graph, node));
    } else {
      ifres = undefined;
    }
    return ifres;
  };
  Belt.List.forEach(node => aux(graph, node), nodes);
  return Belt.List.reverse(visited.contents);
};

let dfs1 = dfs3;

let ifres;

if (%equal()({TAG: "::", _0: "a", _1: {TAG: "::", _0: "d", _1: {TAG: "::", _0: "e", _1: {TAG: "::", _0: "g", _1: {TAG: "::", _0: "f", _1: {TAG: "::", _0: "c", _1: {TAG: "::", _0: "b", _1: "[]"}}}}}}}, dfs1(graph, {TAG: "::", _0: "a", _1: "[]"}))) {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}



let ifres;

if (%equal()({TAG: "::", _0: "b", _1: {TAG: "::", _0: "e", _1: {TAG: "::", _0: "g", _1: {TAG: "::", _0: "f", _1: {TAG: "::", _0: "d", _1: "[]"}}}}}, dfs1({TAG: "::", _0: ["f", "d"], _1: graph}, {TAG: "::", _0: "b", _1: "[]"}))) {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}

let ifres;

if (ifres === "()") {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}



let grwork = {TAG: "::", _0: ["wake", "shower"], _1: {TAG: "::", _0: ["shower", "dress"], _1: {TAG: "::", _0: ["dress", "go"], _1: {TAG: "::", _0: ["wake", "eat"], _1: {TAG: "::", _0: ["eat", "washup"], _1: {TAG: "::", _0: ["washup", "go"], _1: "[]"}}}}}};

let unsafe_topsort = graph => {
  let visited = %makeref()("[]");
  let sort_nodes;
  let sort_node;
  sort_nodes = nodes => Belt.List.forEach(node => sort_node(node), nodes);
  sort_node = node => {
    let ifres;
    if (!Belt.List.has(%equal(), node, visited.contents)) {
      sort_nodes(nexts(graph, node));
      ifres = %refset()({TAG: "::", _0: node, _1: visited.contents}, visited);
    } else {
      ifres = undefined;
    }
    return ifres;
  };
  Belt.List.forEach(_arg0 => sort_node(x), graph);
  return visited.contents;
};

let ifres;

if (%equal()({TAG: "::", _0: "wake", _1: {TAG: "::", _0: "shower", _1: {TAG: "::", _0: "dress", _1: {TAG: "::", _0: "eat", _1: {TAG: "::", _0: "washup", _1: {TAG: "::", _0: "go", _1: "[]"}}}}}}, unsafe_topsort(grwork))) {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}

let ifres;

if (ifres === "()") {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}



let pathsort = graph => {
  let visited = %makeref()("[]");
  let empty_path = [String_set.empty, "[]"];
  let +> = (node, _arg1) => {
    let ifres;
    if (String_set.has(node, set)) {
      throw [{TAG: "::", _0: node, _1: stack}];
      ifres = undefined;
    } else {
      ifres = [String_set.add(node, set), {TAG: "::", _0: node, _1: stack}];
    }
    return ifres;
  };
  let sort_nodes;
  let sort_node;
  sort_nodes = (path, nodes) => Belt.List.forEach(node => sort_node(node, path), nodes);
  sort_node = (path, node) => {
    let ifres;
    if (!Belt.List.has(%equal(), node, visited.contents)) {
      sort_nodes(nexts(graph, node), +>(path, node));
      ifres = %refset()({TAG: "::", _0: node, _1: visited.contents}, visited);
    } else {
      ifres = undefined;
    }
    return ifres;
  };
  Belt.List.forEach(_arg0 => sort_node(x, empty_path), graph);
  return visited.contents;
};

let ifres;

if (%equal()({TAG: "::", _0: "wake", _1: {TAG: "::", _0: "shower", _1: {TAG: "::", _0: "dress", _1: {TAG: "::", _0: "eat", _1: {TAG: "::", _0: "washup", _1: {TAG: "::", _0: "go", _1: "[]"}}}}}}, pathsort(grwork))) {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}

let ifres;

if (ifres === "()") {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}



try {
  (prim => {
    
    
  })(pathsort({TAG: "::", _0: ["go", "eat"], _1: grwork}));
  let ifres;
  if (false) {
    ifres = undefined;
  } else {
    throw "Match_failure";
    ifres = undefined;
  }
  
} catch (exn) {
  "()";
}

let ifres;

if (undefined === "()") {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}

