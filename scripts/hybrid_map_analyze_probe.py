#!/usr/bin/env python3
"""Aggregate per-map B storage counters. No timing inference."""
import collections
import json
from pathlib import Path

root = Path('/tmp/rescript-hybrid-map-experiment')
groups = collections.defaultdict(collections.Counter)
for line in (root / 'logs/map-probe.log').open():
    if not line.startswith('HYBRID_MAP '):
        continue
    _, caller, *nums = line.split()
    entries, span, cap, inserts, requests, requested, initialized, moved, size = map(int, nums)
    for key in ['all', caller]:
        g = groups[key]
        g.update(maps=1, entries=entries, span_slots=span, capacity_bytes=cap*size,
                 insert_calls=inserts, allocation_or_resize_requests=requests,
                 requested_capacity_bytes=requested*size,
                 initialized_slot_bytes=initialized*size, prepend_moved_slot_bytes=moved*size,
                 tiny_maps=int(entries <= 8), tiny_capacity_bytes=cap*size if entries <= 8 else 0,
                 sparse_maps=int(span > 256 and span > 8*entries))
        g['max_span'] = max(g['max_span'], span)
        g['max_capacity_bytes'] = max(g['max_capacity_bytes'], cap*size)
(root / 'map-probe-summary.json').write_text(json.dumps(groups, indent=2, sort_keys=True))
print(json.dumps(groups, indent=2, sort_keys=True))
