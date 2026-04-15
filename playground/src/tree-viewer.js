/**
 * Collapsible tree viewer component for S-expression trees.
 */

const KEYWORDS = new Set([
  'structure', 'structure_item', 'signature', 'signature_item',
  'Tstr_value', 'Tstr_type', 'Tstr_module', 'Tstr_open', 'Tstr_eval',
  'Tstr_primitive', 'Tstr_exception', 'Tstr_modtype', 'Tstr_include',
  'Texp_ident', 'Texp_constant', 'Texp_let', 'Texp_function',
  'Texp_apply', 'Texp_match', 'Texp_tuple', 'Texp_construct',
  'Texp_record', 'Texp_field', 'Texp_ifthenelse', 'Texp_sequence',
  'Texp_array', 'Texp_try', 'Texp_variant', 'Texp_setfield',
  'Tpat_var', 'Tpat_construct', 'Tpat_tuple', 'Tpat_constant',
  'Tpat_any', 'Tpat_alias', 'Tpat_or', 'Tpat_record',
  'Pstr_value', 'Pstr_eval', 'Pstr_type', 'Pstr_module',
  'Pexp_ident', 'Pexp_constant', 'Pexp_let', 'Pexp_fun',
  'Pexp_apply', 'Pexp_match', 'Pexp_tuple', 'Pexp_construct',
  'Pexp_record', 'Pexp_field', 'Pexp_ifthenelse', 'Pexp_sequence',
  'Ppat_var', 'Ppat_construct', 'Ppat_tuple', 'Ppat_constant',
  'Nonrecursive', 'Recursive', 'Public', 'Private',
  'setglobal', 'let', 'function', 'apply', 'prim', 'if', 'switch',
  'makeblock', 'field', 'seq', 'staticfail', 'staticcatch',
]);

export class TreeViewer {
  constructor(container) {
    this.container = container;
    this.tree = null;
    this.highlightedNode = null;
    this.highlightedAncestors = new Set();
    this.nodeElements = new Map(); // node -> DOM element
    this.onNodeClick = null; // callback(loc)
  }

  render(tree) {
    this.tree = tree;
    this.nodeElements.clear();
    this.container.innerHTML = '';
    if (!tree) return;

    const el = this.renderNode(tree, 0);
    if (el) this.container.appendChild(el);
  }

  renderNode(node, depth) {
    if (!node) return null;

    if (node.type === 'atom') {
      return this.renderAtom(node);
    }

    if (node.type === 'list') {
      return this.renderList(node, depth);
    }

    return null;
  }

  renderAtom(node) {
    const span = document.createElement('span');
    if (node.quoted) {
      span.className = 'tree-string';
      span.textContent = `"${node.value}"`;
    } else if (/^-?\d+(\.\d+)?$/.test(node.value)) {
      span.className = 'tree-number';
      span.textContent = node.value;
    } else {
      span.className = 'tree-atom';
      span.textContent = node.value;
    }
    return span;
  }

  renderList(node, depth) {
    const div = document.createElement('div');
    div.className = 'tree-node';

    // Skip rendering (loc ...) nodes inline - they're metadata
    if (node.tag === 'loc') return null;

    const header = document.createElement('div');
    header.className = 'tree-node-header';
    this.nodeElements.set(node, header);

    // Meaningful children (exclude loc nodes and first atom tag)
    const contentChildren = node.children.filter((c, i) => {
      if (i === 0 && c.type === 'atom' && c.value === node.tag) return false;
      if (c.type === 'list' && c.tag === 'loc') return false;
      return true;
    });

    const hasListChildren = contentChildren.some(c => c.type === 'list');
    const isCollapsible = hasListChildren && contentChildren.length > 0;

    // Toggle button
    const toggle = document.createElement('span');
    toggle.className = 'tree-toggle' + (isCollapsible ? '' : ' leaf');
    toggle.textContent = isCollapsible ? (depth < 2 ? '\u25BE' : '\u25B8') : '';

    // Tag
    const tagSpan = document.createElement('span');
    if (node.tag && KEYWORDS.has(node.tag)) {
      tagSpan.className = 'tree-keyword';
    } else if (node.tag) {
      tagSpan.className = 'tree-tag';
    }
    tagSpan.textContent = node.tag || '(...)';

    // Inline atoms (show simple values on the same line)
    const inlineAtoms = contentChildren.filter(c => c.type === 'atom');
    const inlineText = inlineAtoms.length > 0 && inlineAtoms.length <= 3
      ? ' ' + inlineAtoms.map(a => a.quoted ? `"${a.value}"` : a.value).join(' ')
      : '';

    // Location badge
    let locBadge = '';
    if (node.loc && !node.loc.ghost) {
      locBadge = ` ${node.loc.startLine}:${node.loc.startCol}`;
    }

    header.appendChild(toggle);
    header.appendChild(tagSpan);

    if (inlineText) {
      const inlineSpan = document.createElement('span');
      inlineSpan.className = 'tree-atom';
      inlineSpan.textContent = inlineText;
      header.appendChild(inlineSpan);
    }

    if (locBadge) {
      const locSpan = document.createElement('span');
      locSpan.className = 'tree-loc';
      locSpan.textContent = locBadge;
      header.appendChild(locSpan);
    }

    div.appendChild(header);

    // Children container
    const childrenDiv = document.createElement('div');
    childrenDiv.className = 'tree-children' + (depth >= 2 ? ' collapsed' : '');

    const listChildren = contentChildren.filter(c => c.type === 'list');
    for (const child of listChildren) {
      const childEl = this.renderNode(child, depth + 1);
      if (childEl) childrenDiv.appendChild(childEl);
    }

    if (isCollapsible) {
      div.appendChild(childrenDiv);

      header.addEventListener('click', (e) => {
        e.stopPropagation();
        const collapsed = childrenDiv.classList.toggle('collapsed');
        toggle.textContent = collapsed ? '\u25B8' : '\u25BE';

        // Fire click callback for source highlighting
        if (node.loc && this.onNodeClick) {
          this.onNodeClick(node.loc);
        }
      });
    } else if (node.loc && this.onNodeClick) {
      header.addEventListener('click', (e) => {
        e.stopPropagation();
        this.onNodeClick(node.loc);
      });
    }

    return div;
  }

  /**
   * Highlight a specific node and its ancestors.
   */
  highlight(targetNode) {
    // Clear previous highlights
    if (this.highlightedNode) {
      const el = this.nodeElements.get(this.highlightedNode);
      if (el) el.classList.remove('highlighted');
    }
    for (const ancestor of this.highlightedAncestors) {
      const el = this.nodeElements.get(ancestor);
      if (el) el.classList.remove('highlighted-ancestor');
    }
    this.highlightedAncestors.clear();

    if (!targetNode) {
      this.highlightedNode = null;
      return;
    }

    this.highlightedNode = targetNode;
    const el = this.nodeElements.get(targetNode);
    if (el) {
      el.classList.add('highlighted');
      // Ensure visible by expanding ancestors and scrolling
      this.ensureVisible(el);
    }

    // Highlight ancestors
    const ancestors = this.findAncestors(targetNode);
    for (const ancestor of ancestors) {
      this.highlightedAncestors.add(ancestor);
      const ancestorEl = this.nodeElements.get(ancestor);
      if (ancestorEl) ancestorEl.classList.add('highlighted-ancestor');
    }
  }

  ensureVisible(el) {
    // Expand all collapsed ancestors
    let parent = el.parentElement;
    while (parent && parent !== this.container) {
      if (parent.classList.contains('collapsed')) {
        parent.classList.remove('collapsed');
        // Update toggle icon
        const toggle = parent.previousElementSibling?.querySelector('.tree-toggle');
        if (toggle) toggle.textContent = '\u25BE';
      }
      parent = parent.parentElement;
    }
    // Scroll into view
    el.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  }

  findAncestors(targetNode) {
    const ancestors = [];
    const stack = [{ node: this.tree, path: [] }];
    while (stack.length > 0) {
      const { node, path } = stack.pop();
      if (node === targetNode) return path;
      if (node.type === 'list' && node.children) {
        for (const child of node.children) {
          stack.push({ node: child, path: [...path, node] });
        }
      }
    }
    return ancestors;
  }
}
