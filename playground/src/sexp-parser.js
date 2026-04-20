/**
 * Lightweight S-expression parser.
 * Parses strings like: (foo (bar 1 2) (baz "hello"))
 * into tree structures with location extraction.
 */

/**
 * @typedef {Object} SexpNode
 * @property {'list'|'atom'} type
 * @property {string} [tag] - First element of a list (e.g. "structure_item")
 * @property {SexpNode[]} [children] - Child nodes for lists
 * @property {string} [value] - Value for atoms
 * @property {Location|null} [loc] - Source location if present
 */

/**
 * @typedef {Object} Location
 * @property {number} startLine
 * @property {number} startCol
 * @property {number} endLine
 * @property {number} endCol
 * @property {boolean} ghost
 */

export function parseSexp(input) {
  let pos = 0;

  function skipWhitespace() {
    while (pos < input.length && /\s/.test(input[pos])) pos++;
  }

  function parseAtom() {
    const start = pos;
    if (input[pos] === '"') {
      // Quoted string
      pos++;
      let str = '';
      while (pos < input.length && input[pos] !== '"') {
        if (input[pos] === '\\') {
          pos++;
          if (pos < input.length) str += input[pos];
        } else {
          str += input[pos];
        }
        pos++;
      }
      if (pos < input.length) pos++; // skip closing quote
      return { type: 'atom', value: str, quoted: true };
    }
    // Unquoted atom
    while (pos < input.length && !/[\s()]/.test(input[pos])) pos++;
    const value = input.slice(start, pos);
    return { type: 'atom', value, quoted: false };
  }

  function parseList() {
    pos++; // skip '('
    skipWhitespace();

    const children = [];
    while (pos < input.length && input[pos] !== ')') {
      children.push(parseExpr());
      skipWhitespace();
    }
    if (pos < input.length) pos++; // skip ')'

    // Extract tag (first atom in list)
    const tag = children.length > 0 && children[0].type === 'atom'
      ? children[0].value
      : null;

    // Extract location if present
    const loc = extractLocation(children);

    return {
      type: 'list',
      tag,
      children,
      loc,
    };
  }

  function parseExpr() {
    skipWhitespace();
    if (pos >= input.length) {
      return { type: 'atom', value: '', quoted: false };
    }
    if (input[pos] === '(') {
      return parseList();
    }
    return parseAtom();
  }

  const result = parseExpr();
  return result;
}

/**
 * Extract a location tuple from a list's children.
 * Format: (loc startLine startCol endLine endCol [ghost])
 */
function extractLocation(children) {
  for (const child of children) {
    if (
      child.type === 'list' &&
      child.tag === 'loc' &&
      child.children.length >= 5
    ) {
      const nums = child.children.slice(1).map(c =>
        c.type === 'atom' ? parseInt(c.value, 10) : NaN
      );
      if (nums.slice(0, 4).every(n => !isNaN(n))) {
        return {
          startLine: nums[0],
          startCol: nums[1],
          endLine: nums[2],
          endCol: nums[3],
          ghost: child.children.length > 5 &&
            child.children[5]?.value === 'ghost',
        };
      }
    }
  }
  return null;
}

/**
 * Build a flat index of all nodes with locations for cursor mapping.
 * Returns an array sorted by specificity (smallest range first).
 */
export function buildLocationIndex(tree) {
  const index = [];

  function walk(node, depth) {
    if (node.loc && !node.loc.ghost) {
      index.push({ node, depth, loc: node.loc });
    }
    if (node.type === 'list' && node.children) {
      for (const child of node.children) {
        walk(child, depth + 1);
      }
    }
  }

  walk(tree, 0);

  // Sort by range size (smallest first = most specific)
  index.sort((a, b) => {
    const sizeA = rangeSize(a.loc);
    const sizeB = rangeSize(b.loc);
    return sizeA - sizeB;
  });

  return index;
}

function rangeSize(loc) {
  return (loc.endLine - loc.startLine) * 10000 + (loc.endCol - loc.startCol);
}

/**
 * Find the most specific node containing the given cursor position.
 */
export function findNodeAtCursor(index, line, col) {
  for (const entry of index) {
    const { loc } = entry;
    if (
      (line > loc.startLine || (line === loc.startLine && col >= loc.startCol)) &&
      (line < loc.endLine || (line === loc.endLine && col <= loc.endCol))
    ) {
      return entry;
    }
  }
  return null;
}
