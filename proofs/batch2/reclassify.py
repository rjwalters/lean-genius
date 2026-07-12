#!/usr/bin/env python3
"""Recompute the class column for RESIDUAL ledger rows from the freshest diag
entry available, using merge_results.classify. Rows with no diag entry at all
keep their current class (or doctor-unclassified). GREEN/PRE-EXISTING rows are
untouched.

usage: reclassify.py            # rewrites verify-results.tsv in place
"""
import re, os, collections
os.chdir(os.path.dirname(os.path.abspath(__file__)))

# load only the classify()/parse_diag() defs from merge_results.py (its module
# level code would run a merge if imported directly)
_mr_src = open('merge_results.py').read()
_mr_src = _mr_src[:_mr_src.index('args = sys.argv')]
_ns = {'__file__': os.path.abspath('merge_results.py')}
exec(compile(_mr_src, 'merge_results.py', 'exec'), _ns)
class MR:
    classify = staticmethod(_ns['classify'])

# chronological wave order (freshest last wins)
ORDER = ['A','B2','C','D1','D2','E','E2','E3','F1','F2','G','H1','H2',
         'T1','T2','S1','S2','S3',
         'W0smoke','W0aa','W0ab','W0ac','W0ad','W0ae','W0af','W0ag','W0ah',
         'DR1','DR2','DR3','REG']

entries = {}
for w in ORDER:
    path = f'diag-{w}.txt'
    if not os.path.exists(path):
        continue
    cur = None
    for line in open(path, errors='replace'):
        m = re.match(r'^===== (\S+)', line)
        if m:
            cur = m.group(1); entries[cur] = []
        elif cur is not None and line.strip():
            entries[cur].append(line.strip())

rows = {}
for line in open('verify-results.tsv'):
    parts = line.rstrip('\n').split('\t')
    if len(parts) >= 2:
        rows[parts[0]] = (parts[1], parts[2] if len(parts) > 2 else '')

changed = 0
for t, (status, cls) in rows.items():
    if status != 'RESIDUAL':
        continue
    if t in entries and entries[t]:
        newcls = MR.classify(entries[t])
        if newcls != cls:
            rows[t] = (status, newcls); changed += 1
    elif cls in ('', 'unclassified'):
        rows[t] = (status, 'doctor-unclassified'); changed += 1

with open('verify-results.tsv', 'w') as f:
    for t in sorted(rows):
        s, c = rows[t]
        f.write(f"{t}\t{s}\t{c}\n")

print(f'reclassified {changed} rows')
hist = collections.Counter(v[1] for v in rows.values() if v[0] == 'RESIDUAL')
for k, n in hist.most_common(30):
    print(f'  {n}\t{k}')
