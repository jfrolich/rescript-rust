#!/usr/bin/env python3
"""Parse a callgrind out file (--dump-instr=yes, no compression) and symbolize.

load(path) -> (self_cost, arcs, summary)
  self_cost: {(ob, fn): {addr: cost}}
  arcs: list of (caller(ob,fn), call_addr, callee(ob,fn), incl_cost)
symbolize(binary, addrs, cache_path) -> {addr: [(function, file, line), ...]} innermost first
"""
import json, os, subprocess, sys, collections

def load(path):
    self_cost = collections.defaultdict(lambda: collections.defaultdict(int))
    arcs = []
    ob = fn = cob = cfn = None
    pending_call = False
    summary = 0
    with open(path, 'r', errors='replace') as f:
        for line in f:
            c = line[0]
            if c.isdigit():
                sp = line.split()
                addr = int(sp[0], 0); cost = int(sp[1]) if len(sp) > 1 else 0
                if pending_call:
                    arcs.append(((ob, fn), addr, (cob if cob else ob, cfn), cost))
                    pending_call = False; cob = None
                else:
                    self_cost[(ob, fn)][addr] += cost
            elif line.startswith('fn='):
                fn = line[3:].rstrip('\n')
            elif line.startswith('ob='):
                ob = line[3:].rstrip('\n')
            elif line.startswith('cob='):
                cob = line[4:].rstrip('\n')
            elif line.startswith('cfn='):
                cfn = line[4:].rstrip('\n')
            elif line.startswith('calls='):
                pending_call = True
            elif line.startswith('summary:'):
                summary = int(line.split()[1])
    return self_cost, arcs, summary

def symbolize(binary, addrs, cache_path):
    cache = {}
    if os.path.exists(cache_path):
        with open(cache_path) as f:
            cache = {int(k): v for k, v in json.load(f).items()}
    todo = sorted(a for a in addrs if a not in cache)
    if todo:
        p = subprocess.run(['llvm-symbolizer', '--obj=' + binary, '--inlines', '--output-style=JSON', '--demangle'],
                           input='\n'.join(hex(a) for a in todo) + '\n', capture_output=True, text=True)
        n = 0
        for line in p.stdout.splitlines():
            if not line.strip():
                continue
            d = json.loads(line)
            a = int(d['Address'], 16)
            frames = [(s.get('FunctionName', ''), s.get('FileName', ''), s.get('Line', 0)) for s in d.get('Symbol', [])]
            cache[a] = frames
            n += 1
        with open(cache_path, 'w') as f:
            json.dump({str(k): v for k, v in cache.items()}, f)
    return cache
