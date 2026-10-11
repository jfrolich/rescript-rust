#!/bin/bash
# Triage JS output parity failures by root cause
#
# Usage:
#   ./scripts/triage_js_failures.sh              # analyze existing diffs
#   ./scripts/triage_js_failures.sh --refresh     # re-run tests first, then analyze
#   ./scripts/triage_js_failures.sh --top 5       # show top 5 files per category
#
# Output: grouped failure categories with file lists, sorted by impact (most files first).
# Agents should fix one category at a time for maximum leverage.

set -e

script_dir=$(cd "$(dirname "$0")"; pwd -P)
project_root=$(cd "$script_dir/.."; pwd -P)
DIFF_DIR="$project_root/temp/rust-parity/diffs"
TOP_N=10
REFRESH=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --refresh) REFRESH=true; shift ;;
        --top) TOP_N="$2"; shift 2 ;;
        -h|--help)
            echo "Usage: $0 [--refresh] [--top N]"
            echo "  --refresh   Re-run JS parity tests before triaging"
            echo "  --top N     Show top N files per category (default: 10)"
            exit 0 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

if $REFRESH; then
    echo "Re-running JS parity tests..."
    "$script_dir/test_js_output_parity.sh" --verbose 2>&1 | tail -5
    echo ""
fi

if [[ ! -d "$DIFF_DIR" ]]; then
    echo "No diff directory found at $DIFF_DIR"
    echo "Run ./scripts/test_js_output_parity.sh first"
    exit 1
fi

python3 -c "
import os, sys, re
from collections import defaultdict

diff_dir = '$DIFF_DIR'
top_n = $TOP_N

categories = defaultdict(lambda: {'files': [], 'sample_diff': ''})
file_hunks = []

for f in sorted(os.listdir(diff_dir)):
    if not f.endswith('.diff') or not f.startswith('js_'):
        continue
    path = os.path.join(diff_dir, f)
    with open(path) as fh:
        content = fh.read()

    name = f.replace('js_src_', '').replace('.res.diff', '')
    hunks = content.count('@@ ')

    file_hunks.append((hunks, name))

    # Extract added/removed lines (excluding header)
    added = []
    removed = []
    for line in content.split('\n'):
        if line.startswith('+') and not line.startswith('+++'):
            added.append(line[1:].strip())
        elif line.startswith('-') and not line.startswith('---'):
            removed.append(line[1:].strip())

    added_text = ' '.join(added)
    removed_text = ' '.join(removed)
    all_text = added_text + ' ' + removed_text

    # Categorize by root cause patterns (most specific first)
    cat = None

    # Temp variable naming
    if any(v in all_text for v in ['ifres', '\$\$switch']):
        if 'tmp' in removed_text or 'ifres' in added_text or '\$\$switch' in added_text:
            cat = 'temp-var-naming: tmp vs ifres/switch (lam_compile if/switch temp names)'

    # Recursive module init
    if not cat and 'Primitive_module.init' in all_text:
        cat = 'recursive-module: Primitive_module.init lowering'

    # Switch return placement / fallthrough
    if not cat:
        # Check for return statements moving outside switch
        rm_returns = sum(1 for l in removed if l.strip().startswith('return '))
        add_returns = sum(1 for l in added if l.strip().startswith('return '))
        if rm_returns > 0 and add_returns > 0 and ('case ' in all_text or 'switch' in all_text):
            cat = 'switch-fallthrough: return placement in switch/case blocks'

    # Conditional simplification (ternary vs if/else)
    if not cat and ('typeof' in all_text or '===' in all_text):
        if any(k in added_text for k in ['if (', 'else {']):
            cat = 'cond-simplify: ternary/conditional not folded to simple expression'

    # Array/length/isArray simplification
    if not cat and ('length' in all_text or 'isArray' in all_text or '.length >= 0' in all_text):
        cat = 'array-simplify: missing array length/isArray constant folding'

    # Undefined handling
    if not cat and 'undefined' in added_text and 'undefined' not in removed_text:
        cat = 'undefined-extra: extra undefined values in output'

    # Constant folding (string, int comparisons evaluated at compile time)
    if not cat:
        # Look for patterns like eq(\"...\", true, true) vs eq(\"...\", computed)
        if re.search(r'eq\(.*true,\s*true\)|eq\(.*false,\s*false\)|eq\(.*\d+,\s*\d+\)', all_text):
            if hunks <= 4:
                cat = 'const-fold: compile-time constant evaluation differences'

    # Import differences
    if not cat and ('import ' in added_text or 'import ' in removed_text):
        if added.count('') == 0 or removed.count('') == 0:
            cat = 'imports: different import set or ordering'

    # While/for loop lowering
    if not cat and ('while' in all_text or 'for (' in all_text):
        if 'while (true)' in all_text or '_acc' in all_text or 'contents' in all_text:
            cat = 'loop-lowering: while/for loop compilation differences'

    # Let binding / dead code differences
    if not cat:
        let_adds = sum(1 for l in added if l.strip().startswith('let '))
        let_rms = sum(1 for l in removed if l.strip().startswith('let '))
        if let_adds != let_rms and hunks <= 6:
            cat = 'let-binding: different let binding shape or dead code elimination'

    # Throw/exception
    if not cat and ('throw' in all_text or 'RE_EXN_ID' in all_text):
        cat = 'exception: throw/exception lowering differences'

    # Object literal shape
    if not cat and ('{' in added_text and 'TAG' in all_text):
        cat = 'object-shape: block/record/variant object literal differences'

    # Whitespace / empty lines only
    if not cat:
        real_added = [l for l in added if l.strip()]
        real_removed = [l for l in removed if l.strip()]
        if not real_added or not real_removed:
            cat = 'whitespace: empty line or formatting differences'

    # Catch-all
    if not cat:
        cat = 'other: uncategorized differences'

    categories[cat]['files'].append((name, hunks))
    if not categories[cat]['sample_diff'] and hunks <= 6:
        # Store a compact sample
        sample_lines = [l for l in content.split('\n') if l.startswith('+') or l.startswith('-')]
        sample_lines = [l for l in sample_lines if not l.startswith('+++') and not l.startswith('---')]
        categories[cat]['sample_diff'] = '\n'.join(sample_lines[:8])

# Print summary
total_files = len(file_hunks)
total_hunks = sum(h for h, _ in file_hunks)
print(f'JS Output Parity: {657 - total_files}/657 passing, {total_files} failing, {total_hunks} total hunks')
print(f'=' * 72)
print()

# Sort categories by file count (most impactful first)
for cat, data in sorted(categories.items(), key=lambda x: -len(x[1]['files'])):
    files = data['files']
    total_cat_hunks = sum(h for _, h in files)
    print(f'### {cat}')
    print(f'    {len(files)} files, {total_cat_hunks} hunks')
    print()

    # Show files sorted by hunk count
    for name, h in sorted(files, key=lambda x: -x[1])[:top_n]:
        print(f'    {h:3d} hunks  {name}')
    if len(files) > top_n:
        print(f'    ... +{len(files) - top_n} more')
    print()

    # Show sample diff if available
    if data['sample_diff']:
        print(f'    Sample diff:')
        for line in data['sample_diff'].split('\n'):
            print(f'      {line}')
        print()

# Print quick-win ranking
print()
print(f'=== QUICK WINS (fix one root cause, fix many files) ===')
print()
ranked = sorted(categories.items(), key=lambda x: -len(x[1]['files']))
for cat, data in ranked[:5]:
    files = data['files']
    print(f'  {len(files):3d} files  {cat}')
print()
print('Focus on the top category first — one fix likely resolves all files in that group.')
"
