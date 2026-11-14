#!/usr/bin/env python3
"""Check cost-note coverage of changed Rust function bodies in lowering.

This is a lexical coverage check, not a proof of the stated complexity. Review
loops, callback costs and pool growth manually. Strings/comments, test-only
items, nested functions and impl receivers are distinguished by the scanner.
"""
import argparse
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEXEME = r'r(#+)".*?"\1|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\'|//[^\n]*|/\*.*?\*/'
COST = re.compile(r'Cost:|\bO\(|\b[Oo]ne step|\b[Oo]ne write')


def normalized(source):
    return ''.join(m[0] for m in re.finditer(LEXEME + r'|\S', source, re.S)
                   if not m[0].startswith(('//', '/*')))


def functions(source):
    masked = re.sub(LEXEME, lambda m: re.sub(r'[^\n]', ' ', m[0]), source, flags=re.S)

    def body(start):
        parens = brackets = 0
        for at in range(start, len(masked)):
            ch = masked[at]
            parens += (ch == '(') - (ch == ')')
            brackets += (ch == '[') - (ch == ']')
            if ch == ';' and parens == brackets == 0:
                return None  # trait/extern declaration or a test-only field
            if ch == '{':
                depth, end = 1, at + 1
                while depth and end < len(masked):
                    depth += (masked[end] == '{') - (masked[end] == '}')
                    end += 1
                assert depth == 0, 'unbalanced item'
                return at, end
        return None

    excluded = []
    for match in re.finditer(r'#\[cfg\(test\)\]', masked):
        if re.match(r'\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?(?:fn|mod|impl)\b', masked[match.end():]):
            bounds = body(match.end())
            if bounds:
                excluded.append((match.start(), bounds[1]))
    receivers = []
    for match in re.finditer(r'^\s*impl\b', masked, re.M):
        bounds = body(match.end())
        if bounds:
            receivers.append((match.start(), bounds[1], normalized(source[match.start():bounds[0]])))
    rows = []
    for match in re.finditer(r'\bfn\s+(\w+)\s*(?:<|\()', masked):
        if any(a <= match.start() < b for a, b in excluded):
            continue
        # Start at the name: the regex may already have consumed the opening '('.
        bounds = body(match.start() + 3 + len(match[1]))
        if bounds is None:
            continue
        start = source.rfind('\n', 0, match.start()) + 1
        lines = source[:start].splitlines()
        docs = []
        for line in reversed(lines):
            if line.strip().startswith(('///', '#[')):
                docs.insert(0, line.strip())
            else:
                break
        receiver = next((name for a, b, name in reversed(receivers) if a <= match.start() < b), '')
        parents = [row['name'] for row in rows if row['start'] < match.start() < row['end']]
        rows.append(dict(name=match[1], key=(receiver, tuple(parents), match[1]),
                         start=match.start(), end=bounds[1], line=source.count('\n', 0, match.start()) + 1,
                         docs='\n'.join(docs), code=normalized(source[match.start():bounds[1]])))
    return rows


def self_test():
    sample = '''
struct S { #[cfg(test)] counter: usize }
impl S {
    /// Cost: O(1): reads one row.
    fn get(&self) -> usize { let text = "fn fake() { }"; 0 }
    #[cfg(test)] fn helper() { panic!("not production"); }
    fn run() { #[cfg(test)] println!("test"); fn inner() { } }
}
#[cfg(test)] mod tests { fn ignored() {} }
trait T { fn required(); }
impl T for S { fn required() {} }
impl Other { fn get(&self) -> usize { let text = "fn fake() { }"; 0 } }
'''
    rows = functions(sample)
    assert [r['name'] for r in rows] == ['get', 'run', 'inner', 'required', 'get']
    assert COST.search(rows[0]['docs']) and not COST.search(rows[1]['docs'])
    assert rows[0]['key'] != rows[-1]['key']
    assert rows[2]['key'][1] == ('run',)
    assert normalized('fn f(){ "a b" }') != normalized('fn f(){ "ab" }')
    assert normalized('fn f(){ /* note */ 0 }') == normalized('fn f(){ 0 }')
    print('cost scanner self-tests: passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', default='origin/ocaml-to-rust-rewrite')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
    paths = [ROOT / 'compiler-rust/src/bir/untagged_plan.rs',
             ROOT / 'compiler-rust/src/bir/untagged_plan/metadata.rs']
    paths += sorted(p for p in (ROOT / 'compiler-rust/src/bir/lower').glob('*.rs')
                    if not p.name.endswith('_tests.rs'))
    total = changed = 0
    errors = []
    for path in paths:
        relative = path.relative_to(ROOT)
        old = subprocess.run(['git', 'show', f'{args.base}:{relative}'], cwd=ROOT,
                             text=True, capture_output=True)
        if old.returncode and subprocess.run(['git', 'rev-parse', '--verify', args.base], cwd=ROOT,
                                            capture_output=True).returncode:
            raise SystemExit(f'unknown base: {args.base}')
        before = {r['key']: r['code'] for r in functions(old.stdout)}
        for row in functions(path.read_text()):
            total += 1
            if before.get(row['key']) == row['code']:
                continue
            changed += 1
            if not COST.search(row['docs']) or 'amortized for a pool push' in row['docs']:
                errors.append(f'{relative}:{row["line"]}: {row["name"]}: missing or generic cost note')
    print(f'cost docs: production functions={total}; changed/new={changed}; missing/generic={len(errors)}')
    if errors:
        raise SystemExit('\n'.join(errors))


if __name__ == '__main__':
    main()
