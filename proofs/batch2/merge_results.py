#!/usr/bin/env python3
"""Merge wave results + diag files into verify-results.tsv.

usage: merge_results.py [--results file ...] [--diag file ...]
Reads existing verify-results.tsv, overlays new results (PASS->GREEN,
FAIL->RESIDUAL with class from diag if available), rewrites sorted.
"""
import re, sys, os, collections

os.chdir(os.path.dirname(os.path.abspath(__file__)))

def parse_diag(path):
    d, cur = {}, None
    for line in open(path):
        m = re.match(r'^===== (\S+)', line)
        if m:
            cur = m.group(1); d.setdefault(cur, [])
        elif cur is not None and line.strip():
            d[cur].append(line.strip())
    return d

def classify(errs):
    txt = ' | '.join(errs)
    if not txt: return 'doctor-unclassified'
    if txt == 'TIMEOUT-60s': return 'slow-timeout60'
    if "token 'Λ'" in txt: return 'lambda-reserved-token'
    if 'PartENat' in txt: return 'partenat-removal'
    m = re.search(r'Unknown (?:constant|identifier) `([^`]+)`', txt)
    if m: return 'unknown-const:' + m.group(1)
    if 'maxRecDepth' in txt or 'maximum recursion' in txt: return 'decide-maxrecdepth'
    if 'unexpected token' in txt: return 'parse-error'
    if 'failed to synthesize' in txt: return 'instance-synth'
    if 'Type mismatch' in txt or 'type mismatch' in txt: return 'type-mismatch'
    if 'rewrite' in txt: return 'rewrite-drift'
    if re.search(r'linarith|omega|unsolved goals|simp|No goals|norm_num|positivity|ring', txt):
        return 'proof-drift'
    if 'Invalid field' in txt: return 'dot-notation-drift'
    if 'noncomputable' in txt: return 'noncomputable'
    if 'Function expected' in txt or 'Application type mismatch' in txt:
        return 'signature-drift'
    if re.search(r'Unknown identifier|unknown identifier', txt): return 'unknown-ident'
    if 'fail to show termination' in txt or 'termination' in txt: return 'termination-drift'
    if 'No goals to be solved' in txt or 'no goals' in txt: return 'proof-drift'
    if 'could not synthesize default value' in txt: return 'autoparam-drift'
    if re.search(r"don't know how to synthesize|universe level metavariables|Invalid pattern|Invalid `⟨\.\.\.⟩` notation|invalid", txt):
        return 'elab-drift'
    if 'sorry' in txt: return 'uses-sorry'
    if 'TIMEOUT' in txt or 'timeout' in txt: return 'slow-timeout'
    if re.search(r'Tactic .* failed|tactic .* failed', txt): return 'proof-drift'
    return 'unclassified'

args = sys.argv[1:]
results, diags = [], []
mode = None
for a in args:
    if a == '--results': mode = 'r'
    elif a == '--diag': mode = 'd'
    elif mode == 'r': results.append(a)
    elif mode == 'd': diags.append(a)

diag = {}
for p in diags:
    if os.path.exists(p): diag.update(parse_diag(p))

rows = {}
if os.path.exists('verify-results.tsv'):
    for line in open('verify-results.tsv'):
        parts = line.rstrip('\n').split('\t')
        if len(parts) >= 2:
            rows[parts[0]] = (parts[1], parts[2] if len(parts) > 2 else '')

for p in results:
    if not os.path.exists(p): continue
    for line in open(p):
        parts = line.split()
        if len(parts) != 2: continue
        status, t = parts
        if status == 'PASS':
            rows[t] = ('GREEN', '')
        else:
            cls = classify(diag[t]) if t in diag else rows.get(t, ('', 'doctor-unclassified'))[1] or 'doctor-unclassified'
            rows[t] = ('RESIDUAL', cls)

with open('verify-results.tsv', 'w') as f:
    for t in sorted(rows):
        s, c = rows[t]
        f.write(f"{t}\t{s}\t{c}\n")

c = collections.Counter(v[0] for v in rows.values())
print(f"total={len(rows)} GREEN={c.get('GREEN',0)} RESIDUAL={c.get('RESIDUAL',0)}")
cls = collections.Counter(v[1] for v in rows.values() if v[0] == 'RESIDUAL')
for k, n in cls.most_common(20):
    print(f"  {n}\t{k}")
