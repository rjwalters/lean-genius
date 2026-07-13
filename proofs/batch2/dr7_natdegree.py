#!/usr/bin/env python3
"""Replace drifted `norm_num [natDegree…]`/`simp [natDegree…]` degree-computation
blocks with `compute_degree!` in files whose diag shows an unsolved
`….natDegree = N` goal (#38065 increment 2, map §7e/§7f).

usage: dr7_natdegree.py <diag files…>
"""
import re, sys, os

os.chdir('/Users/rwalters/GitHub/lean-genius/.loom/worktrees/issue-38065/proofs')

files = set()
lines_iter = (l for p in sys.argv[1:] for l in open(p, errors='replace'))
prev = ''
for l in lines_iter:
    if '.natDegree = ' in l and 'unsolved goals' in prev:
        m = re.search(r'error: (Proofs/[\w\']+\.lean)', prev)
        if m:
            files.add(m.group(1))
    if 'natDegree' in l and 'unsolved goals' in l:
        m = re.search(r'error: (Proofs/[\w\']+\.lean)', l)
        if m:
            files.add(m.group(1))
    prev = l

# also accept: error line then goal line with natDegree two lines later
for p in sys.argv[1:]:
    ls = open(p, errors='replace').read().split('\n')
    for i, l in enumerate(ls):
        if 'unsolved goals' in l and 'error: ' in l:
            ctx = '\n'.join(ls[i + 1:i + 3])
            if '.natDegree = ' in ctx:
                m = re.search(r'error: (Proofs/[\w\']+\.lean)', l)
                if m:
                    files.add(m.group(1))

BLOCK = re.compile(
    r'(norm_num|simp(?: only)?)\s*\[\s*natDegree[^\]]*\]', re.S)
for f in sorted(files):
    if not os.path.exists(f):
        continue
    s = open(f).read()
    s2, n = BLOCK.subn('compute_degree!', s)
    if n:
        open(f, 'w').write(s2)
        print(f'{f}: {n} block(s) -> compute_degree!')
