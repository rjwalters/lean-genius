#!/usr/bin/env python3
"""Doctor increment-2 wave DR7: neutralize no-progress tactic calls (#38065).

`<tac> made no progress` on v4.31 means the goal/hyp state was UNCHANGED by the
call, so replacing the call with `skip` is semantics-preserving on v4.31: the
rest of the proof sees the identical state. Either the proof then completes
(v4.26 relied on a simp-set that is now a no-op) or the true downstream error
surfaces for the next diagnosis round.

Driven by diag files passed as argv (freshest last); only lines whose col points
at a recognizable tactic call are touched. Idempotent.
"""
import re, os, sys, collections

ROOT = '/Users/rwalters/GitHub/lean-genius/.loom/worktrees/issue-38065/proofs'
os.chdir(ROOT)

# (file, line, col) sites from "made no progress" errors
sites = {}
for path in sys.argv[1:]:
    for l in open(path, errors='replace'):
        m = re.search(r"error: (Proofs/[\w']+\.lean):(\d+):(\d+): `([\w ]+)` made no progress", l)
        if m:
            sites[(m.group(1), int(m.group(2)), int(m.group(3)))] = m.group(4)

# tactic-call regex starting at the flagged column
TAC = re.compile(
    r'(?:d?simp(?:_arith)?(?:!|\?)?(?: only)?'
    r'|field_simp|ring_nf|push_cast|norm_cast|beta_reduce|push_neg)'
    r'(?:\s*\[[^\]\n]*\])?'
    r'(?:\s+at\s+[^;<⟩\n]+?)?'
    r'(?=\s*(?:$|;|<;>|\)|⟩|--))')

log = collections.Counter()
byfile = collections.defaultdict(list)
for (f, ln, col), tac in sites.items():
    byfile[f].append((ln, col, tac))

for f, lst in sorted(byfile.items()):
    if not os.path.exists(f):
        continue
    lines = open(f, encoding='utf-8').read().split('\n')
    changed = False
    for ln, col, tac in sorted(lst, key=lambda x: (-x[0], -x[1])):
        if ln - 1 >= len(lines):
            continue
        src = lines[ln - 1]
        if col >= len(src):
            continue
        m = TAC.match(src, col)
        if not m:
            log[f'skip (no match): {tac}'] += 1
            continue
        lines[ln - 1] = src[:col] + 'skip' + src[m.end():]
        log[f'neutralized {tac}'] += 1
        changed = True
    if changed:
        open(f, 'w', encoding='utf-8').write('\n'.join(lines))
        log['files'] += 1

for k, v in sorted(log.items()):
    print(f'{k}: {v}')
