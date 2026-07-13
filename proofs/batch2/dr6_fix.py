#!/usr/bin/env python3
"""Doctor increment-2 wave DR6 mechanical sweeps (issue #38065).

Families (all diag-driven, restricted to files implicated by RESIDUAL rows):
  1. SimpleGraph Std.Symm/Std.Irrefl use-sites (diag line-targeted):
       X.symm ARG   -> X.adj_symm ARG      (Function-expected sites)
       X.loopless V -> X.loopless.irrefl V (Function-expected sites)
  2. SimpleGraph structure-instance fields (Adj-context heuristic):
       symm ... :=      -> symm.symm ... :=
       loopless ... :=  -> loopless.irrefl ... :=
  3. Verified unknown-const renames (only in files whose diag flags the name).
  4. `open scoped Topology` for lost 𝓝 notation.
  5. NormedSpace.exp dropped-scalar sweep (nsexp family).
  6. Umbrella `import Mathlib` for unknown-const rows still on submodule imports.

Prints a per-family edit log; idempotent.
"""
import re, os, json, collections, sys

ROOT = '/Users/rwalters/GitHub/lean-genius/.loom/worktrees/issue-38065/proofs'
SCR = '/private/tmp/claude-501/-Users-rwalters-GitHub-lean-genius/3191fbf6-af2a-4a7f-8220-2fd75a0ce237/scratchpad'
os.chdir(ROOT)

diag = json.load(open(f'{SCR}/fresh-diag.json'))
touched = set()
log = collections.Counter()

def read(f):
    return open(f, encoding='utf-8').read()

def write(f, s):
    open(f, 'w', encoding='utf-8').write(s)
    touched.add(f)

# ---------- family 1: line-targeted symm/loopless use-sites ----------
site_fixes = collections.defaultdict(list)  # file -> [(line, kind, term)]
for t, ls in diag.items():
    for i, l in enumerate(ls):
        m = re.search(r'error: Proofs/([\w\']+)\.lean:(\d+):\d+: Function expected at', l)
        if not m or i + 1 >= len(ls):
            continue
        term = ls[i + 1].strip()
        f, ln = f'Proofs/{m.group(1)}.lean', int(m.group(2))
        m2 = re.match(r'^([\w\.\(\)\' ]*?)\.symm$', term)
        if m2:
            site_fixes[f].append((ln, 'symm', m2.group(1)))
        m3 = re.match(r'^([\w\.\(\)\' ]*?)\.loopless$', term)
        if m3:
            site_fixes[f].append((ln, 'loopless', m3.group(1)))

for f, fixes in site_fixes.items():
    if not os.path.exists(f):
        continue
    lines = read(f).split('\n')
    for ln, kind, base in sorted(set(fixes)):
        if ln - 1 >= len(lines):
            continue
        src = lines[ln - 1]
        if kind == 'symm':
            new = src.replace(f'{base}.symm', f'{base}.adj_symm')
            key = 'use-site adj_symm'
        else:
            new = src.replace(f'{base}.loopless', f'{base}.loopless.irrefl')
            if '.loopless.irrefl.irrefl' in new:
                continue
            key = 'use-site loopless.irrefl'
        if new != src:
            lines[ln - 1] = new
            log[key] += 1
    write(f, '\n'.join(lines))

# ---------- family 2: structure-instance fields near an Adj binding ----------
# collect all files implicated by residual diags + residual modules themselves
resid_files = set()
for t, ls in diag.items():
    if os.path.exists(f'Proofs/{t}.lean'):
        resid_files.add(f'Proofs/{t}.lean')
    for l in ls:
        m = re.search(r'Proofs/([\w\']+)\.lean', l)
        if m and os.path.exists(f'Proofs/{m.group(1)}.lean'):
            resid_files.add(f'Proofs/{m.group(1)}.lean')

FIELD_SYMM = re.compile(r'^(\s*)symm(\s*| [^:={}]*):=')
FIELD_LOOP = re.compile(r'^(\s*)loopless(\s*| [^:={}]*):=')
for f in sorted(resid_files):
    lines = read(f).split('\n')
    out = list(lines)
    changed = False
    for i, l in enumerate(lines):
        # context: an Adj field within the previous 8 lines (SimpleGraph instance)
        ctx = '\n'.join(lines[max(0, i - 8):i])
        if not re.search(r'\bAdj\b', ctx):
            continue
        if re.match(r'^\s*(symm\.symm|loopless\.irrefl)', l):
            continue
        if re.search(r':=\s*by constructor', l):
            continue
        m = FIELD_SYMM.match(l)
        if m:
            out[i] = FIELD_SYMM.sub(lambda mm: f'{mm.group(1)}symm.symm{mm.group(2)}:=', l, count=1)
            log['field symm.symm'] += 1
            changed = True
            continue
        m = FIELD_LOOP.match(l)
        if m:
            out[i] = FIELD_LOOP.sub(lambda mm: f'{mm.group(1)}loopless.irrefl{mm.group(2)}:=', l, count=1)
            log['field loopless.irrefl'] += 1
            changed = True
    if changed:
        write(f, '\n'.join(out))

# ---------- family 3: verified renames, diag-gated ----------
RENAMES = [
    ('Finset.eq_empty_of_forall_not_mem', 'Finset.eq_empty_of_forall_notMem'),
    ('Set.eq_empty_of_forall_not_mem', 'Set.eq_empty_of_forall_notMem'),
    ('eq_empty_of_forall_not_mem', 'eq_empty_of_forall_notMem'),
    ('Finset.card_offDiag', 'Finset.offDiag_card'),
    ('inv_le_inv_of_le', 'inv_anti₀'),
    ('Int.natAbs_ofNat', 'Int.natAbs_natCast'),
    ('Finset.card_Icc', 'Nat.card_Icc'),
    ('pow_lt_pow_right ', 'pow_lt_pow_right₀ '),
    ('pow_lt_pow_right]', 'pow_lt_pow_right₀]'),
    ('Nat.nth_prime_zero', 'Nat.nth_prime_zero_eq_two'),
    ('sigma_isMultiplicative', 'isMultiplicative_sigma'),
    ('NormedSpace.exp_eq_tsum (𝔸 := ℝ)', 'NormedSpace.exp_eq_tsum ℝ (𝔸 := ℝ)'),
]
for t, ls in diag.items():
    f = f'Proofs/{t}.lean'
    if not os.path.exists(f):
        continue
    txt = '\n'.join(ls)
    flagged = [(o, n) for o, n in RENAMES if o.rstrip(' ]') in txt]
    if not flagged:
        continue
    s = read(f)
    s0 = s
    for o, n in flagged:
        if n in ('Nat.nth_prime_zero_eq_two',) and 'nth_prime_zero_eq_two' in s:
            continue
        if o == 'eq_empty_of_forall_not_mem' and ('Finset.eq_empty_of_forall_not_mem' in s or 'Set.eq_empty_of_forall_not_mem' in s):
            continue  # namespaced variant already handled
        ns = s.replace(o, n)
        if ns != s:
            log[f'rename {o.strip()}'] += 1
            s = ns
    if s != s0:
        write(f, s)

# ---------- family 4: 𝓝 notation loss ----------
for t in open(f'{SCR}/fam-nhds.txt'):
    t = t.strip()
    f = f'Proofs/{t}.lean'
    if not t or not os.path.exists(f):
        continue
    s = read(f)
    if 'open scoped Topology' in s or 'open Topology' in s:
        continue
    lines = s.split('\n')
    last_imp = max(i for i, l in enumerate(lines) if l.startswith('import')) if any(l.startswith('import') for l in lines) else -1
    lines.insert(last_imp + 1, '\nopen scoped Topology')
    write(f, '\n'.join(lines))
    log['open scoped Topology'] += 1

# ---------- family 5: NormedSpace.exp dropped scalar ----------
for t in open(f'{SCR}/fam-nsexp.txt'):
    t = t.strip()
    f = f'Proofs/{t}.lean'
    if not t or not os.path.exists(f):
        continue
    s = read(f)
    s0 = s
    s = re.sub(r'NormedSpace\.exp\s+(?:ℝ|ℂ|𝕜|𝕂)\s+\(', 'NormedSpace.exp (', s)
    s = re.sub(r'NormedSpace\.exp\s+(?:ℝ|ℂ|𝕜|𝕂)\)', 'NormedSpace.exp)', s)
    s = re.sub(r'(?<![\w.])exp\s+(?:ℝ|ℂ|𝕜|𝕂)\s+\(', 'exp (', s)
    if s != s0:
        write(f, s)
        log['nsexp scalar drop'] += 1

# ---------- family 6: umbrella import for unknown-const rows ----------
for t in open(f'{SCR}/fam-unknown.txt'):
    t = t.strip()
    f = f'Proofs/{t}.lean'
    if not t or not os.path.exists(f):
        continue
    s = read(f)
    if re.search(r'^import Mathlib$', s, re.M):
        continue
    if not re.search(r'^import Mathlib\.', s, re.M):
        continue
    lines = s.split('\n')
    out, done = [], False
    for l in lines:
        if l.startswith('import Mathlib.'):
            if not done:
                out.append('import Mathlib')
                done = True
            continue
        out.append(l)
    write(f, '\n'.join(out))
    log['umbrella import'] += 1

print('touched files:', len(touched))
for k, v in sorted(log.items()):
    print(f'  {k}: {v}')
open(f'{SCR}/dr6-touched.txt', 'w').write('\n'.join(sorted(
    os.path.basename(f)[:-5] for f in touched)) + '\n')
