import React, { useMemo, useEffect, useRef, useCallback } from "react";
import { parseSexp, buildLocationIndex, findNodeAtCursor } from "./sexp-parser.js";

const KEYWORDS = new Set([
  "structure", "structure_item", "signature", "signature_item",
  "Tstr_value", "Tstr_type", "Tstr_module", "Tstr_open", "Tstr_eval",
  "Tstr_primitive", "Tstr_exception", "Tstr_modtype", "Tstr_include",
  "Texp_ident", "Texp_constant", "Texp_let", "Texp_function",
  "Texp_apply", "Texp_match", "Texp_tuple", "Texp_construct",
  "Texp_record", "Texp_field", "Texp_ifthenelse", "Texp_sequence",
  "Texp_array", "Texp_try", "Texp_variant", "Texp_setfield",
  "Tpat_var", "Tpat_construct", "Tpat_tuple", "Tpat_constant",
  "Tpat_any", "Tpat_alias", "Tpat_or", "Tpat_record",
  "Pstr_value", "Pstr_eval", "Pstr_type", "Pstr_module",
  "Pexp_ident", "Pexp_constant", "Pexp_let", "Pexp_fun",
  "Pexp_apply", "Pexp_match", "Pexp_tuple", "Pexp_construct",
  "Pexp_record", "Pexp_field", "Pexp_ifthenelse", "Pexp_sequence",
  "Ppat_var", "Ppat_construct", "Ppat_tuple", "Ppat_constant",
  "Nonrecursive", "Recursive", "Public", "Private",
  "setglobal", "let", "function", "apply", "prim", "if", "switch",
  "makeblock", "field", "seq", "staticfail", "staticcatch",
]);

/**
 * Find the path from root to a target node.
 * Returns a Set of all ancestor nodes (including the target).
 */
function findAncestorPath(root, target) {
  const ancestors = new Set();
  if (!root || !target) return ancestors;

  function walk(node) {
    if (node === target) {
      ancestors.add(node);
      return true;
    }
    if (node.type === "list" && node.children) {
      for (const child of node.children) {
        if (walk(child)) {
          ancestors.add(node);
          return true;
        }
      }
    }
    return false;
  }
  walk(root);
  return ancestors;
}

export default function TreeView({ sexp, cursorPosition, onNodeClick }) {
  const tree = useMemo(() => {
    if (!sexp) return null;
    try {
      return parseSexp(sexp);
    } catch {
      return null;
    }
  }, [sexp]);

  const locationIndex = useMemo(() => {
    if (!tree) return [];
    return buildLocationIndex(tree);
  }, [tree]);

  const highlightedNode = useMemo(() => {
    if (!locationIndex.length || !cursorPosition) return null;
    const found = findNodeAtCursor(
      locationIndex,
      cursorPosition.line,
      cursorPosition.col
    );
    return found?.node || null;
  }, [locationIndex, cursorPosition]);

  // Precompute the set of nodes on the path from root to highlighted node
  const expandedAncestors = useMemo(() => {
    return findAncestorPath(tree, highlightedNode);
  }, [tree, highlightedNode]);

  if (!tree) {
    return <div className="empty-panel">Failed to parse tree</div>;
  }

  return (
    <div className="tree-root">
      <TreeNode
        node={tree}
        depth={0}
        highlightedNode={highlightedNode}
        expandedAncestors={expandedAncestors}
        onNodeClick={onNodeClick}
      />
    </div>
  );
}

const TreeNode = React.memo(function TreeNode({
  node,
  depth,
  highlightedNode,
  expandedAncestors,
  onNodeClick,
}) {
  const headerRef = useRef(null);
  const [manualCollapsed, setManualCollapsed] = React.useState(null); // null = auto, true/false = manual

  if (!node) return null;
  if (node.type === "atom") return <AtomNode node={node} />;
  if (node.type !== "list") return null;

  // Skip loc nodes
  if (node.tag === "loc") return null;

  // Filter meaningful children
  const contentChildren = node.children.filter((c, i) => {
    if (i === 0 && c.type === "atom" && c.value === node.tag) return false;
    if (c.type === "list" && c.tag === "loc") return false;
    return true;
  });

  const listChildren = contentChildren.filter((c) => c.type === "list");
  const inlineAtoms = contentChildren.filter((c) => c.type === "atom");
  const isCollapsible = listChildren.length > 0;

  const isHighlighted = node === highlightedNode;
  const isOnHighlightPath = expandedAncestors.has(node);

  // Determine collapsed state:
  // - If user manually toggled, respect that
  // - If this node is on the path to the highlighted node, force expand
  // - Otherwise, default collapsed for depth >= 2
  let collapsed;
  if (isOnHighlightPath) {
    collapsed = false; // always expand nodes on the path to cursor
  } else if (manualCollapsed !== null) {
    collapsed = manualCollapsed;
  } else {
    collapsed = depth >= 2;
  }

  // Reset manual override when highlight path changes through this node
  useEffect(() => {
    if (isOnHighlightPath) {
      setManualCollapsed(null);
    }
  }, [isOnHighlightPath]);

  // Scroll highlighted node into view
  useEffect(() => {
    if (isHighlighted && headerRef.current) {
      headerRef.current.scrollIntoView({ block: "nearest", behavior: "smooth" });
    }
  }, [isHighlighted]);

  const handleClick = useCallback(
    (e) => {
      e.stopPropagation();
      if (isCollapsible) setManualCollapsed((prev) => !(prev ?? collapsed));
      if (node.loc && onNodeClick) onNodeClick(node.loc);
    },
    [isCollapsible, node.loc, onNodeClick, collapsed]
  );

  const inlineText =
    inlineAtoms.length > 0 && inlineAtoms.length <= 3
      ? " " +
        inlineAtoms
          .map((a) => (a.quoted ? `"${a.value}"` : a.value))
          .join(" ")
      : "";

  const headerClass = [
    "tree-node-header",
    isHighlighted && "highlighted",
    !isHighlighted && isOnHighlightPath && "highlighted-ancestor",
  ]
    .filter(Boolean)
    .join(" ");

  return (
    <div className="tree-node">
      <div className={headerClass} onClick={handleClick} ref={headerRef}>
        <span className={`tree-toggle${isCollapsible ? "" : " leaf"}`}>
          {isCollapsible ? (collapsed ? "\u25B8" : "\u25BE") : ""}
        </span>
        <span className={KEYWORDS.has(node.tag) ? "tree-keyword" : "tree-tag"}>
          {node.tag || "(...)"}
        </span>
        {inlineText && <span className="tree-atom">{inlineText}</span>}
        {node.loc && !node.loc.ghost && (
          <span className="tree-loc">
            {" "}
            {node.loc.startLine}:{node.loc.startCol}
          </span>
        )}
      </div>
      {isCollapsible && !collapsed && (
        <div className="tree-children">
          {listChildren.map((child, i) => (
            <TreeNode
              key={i}
              node={child}
              depth={depth + 1}
              highlightedNode={highlightedNode}
              expandedAncestors={expandedAncestors}
              onNodeClick={onNodeClick}
            />
          ))}
        </div>
      )}
    </div>
  );
});

function AtomNode({ node }) {
  if (node.quoted) {
    return <span className="tree-string">"{node.value}"</span>;
  }
  if (/^-?\d+(\.\d+)?$/.test(node.value)) {
    return <span className="tree-number">{node.value}</span>;
  }
  return <span className="tree-atom">{node.value}</span>;
}
