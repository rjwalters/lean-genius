#!/usr/bin/env python3
"""Build a runner3-style diag file from runner5 chunk logs (#38065 inc-2).

usage: extract_diags.py <results-file> <diag-out> <log-glob-prefix>...

For each FAIL target, collect up to 4 `error:` lines (+2 context lines each)
from the chunk logs: first errors in the target's own file, else errors in any
file of its Proofs import closure (dependency failures), else the raw
"Some required targets logged failures" block naming it.
"""
import sys, os, re, glob, functools

os.chdir('/Volumes/Stripe/lean-genius/doctor-b/proofs')
results, diag_out = sys.argv[1], sys.argv[2]
prefixes = sys.argv[3:]

# error lines per source file across all logs
err_by_file = {}
loglines = []
for p in prefixes:
    for lf in sorted(glob.glob(p + '-*.log')):
        loglines.extend(open(lf, errors='replace').read().split('\n'))
for i, l in enumerate(loglines):
    m = re.search(r'error: (?:\./)?Proofs/([\w\']+)\.lean:\d+', l)
    if m:
        err_by_file.setdefault(m.group(1), []).append(
            '\n'.join(x for x in loglines[i:i + 3] if x.strip()))

imports = {}
for fn in os.listdir('Proofs'):
    if fn.endswith('.lean'):
        imports[fn[:-5]] = re.findall(
            r'^import Proofs\.([\w\']+)',
            open(f'Proofs/{fn}', errors='replace').read(), re.M)

@functools.lru_cache(maxsize=None)
def closure(m):
    out = []
    for d in imports.get(m, ()):
        out.append(d)
        out.extend(closure(d))
    return tuple(dict.fromkeys(out))

with open(diag_out, 'w') as out:
    for l in open(results):
        st, t = l.split()
        if st != 'FAIL':
            continue
        entries = err_by_file.get(t)
        if not entries:
            for d in closure(t):
                if d in err_by_file:
                    entries = err_by_file[d]
                    break
        out.write(f'===== {t}\n')
        if entries:
            seen = set()
            n = 0
            for e in entries:
                if e in seen:
                    continue
                seen.add(e)
                out.write(e + '\n')
                n += 1
                if n >= 4:
                    break
        else:
            out.write('(no error lines captured in chunk logs)\n')
print('diag written:', diag_out)
