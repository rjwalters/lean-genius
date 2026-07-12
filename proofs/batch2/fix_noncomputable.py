#!/usr/bin/env python3
"""Parse diag files for `failed to compile definition, consider marking it as
'noncomputable'` errors and insert the keyword at the flagged def site.

usage: fix_noncomputable.py <diag-file> [...]
Idempotent: skips lines already carrying `noncomputable`.
"""
import re, sys, os
from collections import defaultdict

os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))

sites = defaultdict(set)   # path -> {line numbers (1-based)}
pat = re.compile(r"error: (Proofs/\S+\.lean):(\d+):\d+: .*(?:failed to compile definition, consider marking it as 'noncomputable'|not supported by code generator; consider marking definition as `noncomputable`)")
for f in sys.argv[1:]:
    for line in open(f, errors='replace'):
        m = pat.search(line)
        if m:
            sites[m.group(1)].add(int(m.group(2)))

for path, lns in sorted(sites.items()):
    if not os.path.exists(path):
        print('MISSING', path); continue
    lines = open(path).read().splitlines(keepends=True)
    changed = 0
    for ln in lns:
        i = ln - 1
        if i >= len(lines):
            continue
        stripped = lines[i].lstrip()
        if 'noncomputable' in lines[i]:
            continue
        m = re.match(r'(?:private |protected )?(def|abbrev|instance)\b', stripped)
        if not m:
            print('SKIP-nondef', path, ln, stripped[:60])
            continue
        indent = lines[i][:len(lines[i]) - len(stripped)]
        mod = re.match(r'(private |protected )', stripped)
        if mod:
            rest = stripped[len(mod.group(1)):]
            lines[i] = indent + mod.group(1) + 'noncomputable ' + rest
        else:
            lines[i] = indent + 'noncomputable ' + stripped
        changed += 1
    if changed:
        open(path, 'w').write(''.join(lines))
    print('EDITED' if changed else 'NOCHANGE', path, sorted(lns), f'({changed} added)')
