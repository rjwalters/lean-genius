#!/usr/bin/env python3
"""Doctor increment-3 wave DR9 mechanical sweeps (issue #38065).

Families (restricted to RESIDUAL-ledger files):
  1. Token-boundary verified renames (v4.31-source-verified):
       div_lt_iff/lt_div_iff/div_le_iff/le_div_iff(_div_) -> ₀ forms,
       le_of_not_lt -> le_of_not_gt, lt_of_not_le -> lt_of_not_ge,
       tsum_le_tsum/tsum_pos/tsum_eq_zero_add -> Summable.-qualified,
       inv_anti_of_pos -> inv_anti₀, set_integral_congr -> setIntegral_congr_fun.
  2. Qualified-name renames (plain string, all verified in v4.31 source):
       Function.nmem_support -> Function.notMem_support (hub: CauchySchwarzIntegral…),
       Matrix.smul_mulVec_assoc -> Matrix.smul_mulVec,
       Matrix.dotProduct* -> dotProduct* (namespace dropped),
       Real.tendsto_rpow_atTop -> tendsto_rpow_atTop,
       Finset.Nat.card_* -> Nat.card_*, Nat.nth_prime_one -> _eq_three,
       Ordinal.zero_le -> zero_le, Nat.primeFactors_prime -> Nat.Prime.primeFactors,
       Nat.primeFactors_nonempty -> Nat.nonempty_primeFactors.mpr,
       Nat.strong_rec_on -> Nat.strongRecOn, List.Chain'.rel_head -> List.IsChain.rel_head,
       Real.pi_gt_314 -> Real.pi_gt_d2, Real.pi_lt_315 -> Real.pi_lt_d2,
       set_integral_* -> setIntegral_*.
  3. rw-list rewrite: div_add_div_same -> ← add_div (order-safe).
  4. Arg-swap: Nat.pos_pow_of_pos A H -> pow_pos H A.
  5. Complex.abs compat shim (increment-1 recipe, map §7d) for residual files
     using Complex.abs without a shim in their Proofs-import closure
     + verified Complex lemma renames (abs_apply->norm_def, sq_abs->sq_norm, …).
Prints per-family edit log; idempotent.
"""
import re, os, collections

ROOT = '/Users/rwalters/GitHub/lean-genius/.loom/worktrees/issue-38065/proofs'
SCR = '/private/tmp/claude-501/-Users-rwalters-GitHub-lean-genius/3191fbf6-af2a-4a7f-8220-2fd75a0ce237/scratchpad'
os.chdir(ROOT)

resid = [l.strip() for l in open(f'{SCR}/resid-files.txt') if l.strip()]
resid = [f for f in resid if os.path.exists(f)]
touched = set()
log = collections.Counter()

def read(f):
    return open(f, encoding='utf-8').read()

def write(f, s):
    open(f, 'w', encoding='utf-8').write(s)
    touched.add(f)

# ---------- family 1: token-boundary renames ----------
# (old, new): old must not be preceded by [A-Za-z0-9_'.₀] nor followed by [A-Za-z0-9_'₀]
TOKEN_RENAMES = [
    ('div_lt_div_iff', 'div_lt_div_iff₀'),
    ('div_le_div_iff', 'div_le_div_iff₀'),
    ('div_lt_iff', 'div_lt_iff₀'),
    ('lt_div_iff', 'lt_div_iff₀'),
    ('div_le_iff', 'div_le_iff₀'),
    ('le_div_iff', 'le_div_iff₀'),
    ('le_of_not_lt', 'le_of_not_gt'),
    ('lt_of_not_le', 'lt_of_not_ge'),
    ('inv_anti_of_pos', 'inv_anti₀'),
]
# tsum family: additionally must not be preceded by '.' (dot/qualified uses stay)
TSUM_RENAMES = [
    ('tsum_le_tsum', 'Summable.tsum_le_tsum'),
    ('tsum_pos', 'Summable.tsum_pos'),
    ('tsum_eq_zero_add', 'Summable.tsum_eq_zero_add'),
]
BOUND_L = r"(?<![A-Za-z0-9_'．.₀])"
BOUND_R = r"(?![A-Za-z0-9_'₀])"

for f in resid:
    s = read(f)
    s0 = s
    for o, n in TOKEN_RENAMES:
        s, cnt = re.subn(BOUND_L + re.escape(o) + BOUND_R, n, s)
        if cnt:
            log[f'token {o}'] += cnt
    for o, n in TSUM_RENAMES:
        s, cnt = re.subn(BOUND_L + re.escape(o) + BOUND_R, n, s)
        if cnt:
            log[f'token {o}'] += cnt
    if s != s0:
        write(f, s)

# ---------- family 2: qualified-name renames ----------
QUAL_RENAMES = [
    ('Function.nmem_support', 'Function.notMem_support'),
    ('Matrix.smul_mulVec_assoc', 'Matrix.smul_mulVec'),
    ('Matrix.dotProduct', 'dotProduct'),
    ('Real.tendsto_rpow_atTop', 'tendsto_rpow_atTop'),
    ('Finset.Nat.card_', 'Nat.card_'),
    ('Ordinal.zero_le', 'zero_le'),
    ('Nat.primeFactors_nonempty', 'Nat.nonempty_primeFactors.mpr'),
    ('Nat.strong_rec_on', 'Nat.strongRecOn'),
    ("List.Chain'.rel_head", 'List.IsChain.rel_head'),
    ('Real.pi_gt_314', 'Real.pi_gt_d2'),
    ('Real.pi_lt_315', 'Real.pi_lt_d2'),
]
for f in resid:
    s = read(f)
    s0 = s
    for o, n in QUAL_RENAMES:
        if o in s:
            s2 = s.replace(o, n)
            if s2 != s:
                log[f'qual {o}'] += s.count(o)
                s = s2
    # primeFactors_prime (exact; _pow variant is a different v4.31 name)
    s, c0 = re.subn(r'Nat\.primeFactors_prime(?![_\w])', 'Nat.Prime.primeFactors', s)
    if c0: log['qual Nat.primeFactors_prime'] += c0
    # nth_prime numerals (skip already-migrated _eq_ forms)
    s, c1 = re.subn(r'Nat\.nth_prime_one(?!_eq)', 'Nat.nth_prime_one_eq_three', s)
    if c1: log['qual Nat.nth_prime_one'] += c1
    s, c2 = re.subn(r'Nat\.nth_prime_zero(?!_eq)', 'Nat.nth_prime_zero_eq_two', s)
    if c2: log['qual Nat.nth_prime_zero'] += c2
    # set_integral_* -> setIntegral_* (congr -> congr_fun)
    s, c3 = re.subn(r'\bset_integral_congr\b(?!_)', 'setIntegral_congr_fun', s)
    if c3: log['qual set_integral_congr'] += c3
    s, c4 = re.subn(r'\bset_integral_(\w+)', r'setIntegral_\1', s)
    if c4: log['qual set_integral_*'] += c4
    if s != s0:
        write(f, s)

# ---------- family 3: div_add_div_same in rw/simp lists ----------
for f in resid:
    s = read(f)
    s0 = s
    s = s.replace('← div_add_div_same', 'add_div')
    s = s.replace('div_add_div_same', '← add_div')
    if s != s0:
        log['div_add_div_same'] += s0.count('div_add_div_same')
        write(f, s)

# ---------- family 4: Nat.pos_pow_of_pos arg swap ----------
ARG = r"(?:[\w.']+|\((?:[^()]|\([^()]*\))*\))"
PPP = re.compile(r'Nat\.pos_pow_of_pos\s+(' + ARG + r')\s+(' + ARG + r')')
for f in resid:
    s = read(f)
    s2, cnt = PPP.subn(lambda m: f'pow_pos {m.group(2)} {m.group(1)}', s)
    if cnt:
        log['pos_pow_of_pos swap'] += cnt
        write(f, s2)

# ---------- family 5: Complex.abs shim + lemma renames ----------
SHIM = 'noncomputable def Complex.abs (z : ℂ) : ℝ := ‖z‖'
CX_RENAMES = [
    ('Complex.abs_apply', 'Complex.norm_def'),
    ('Complex.sq_abs', 'Complex.sq_norm'),
    ('Complex.abs_exp', 'Complex.norm_exp'),
    ('Complex.abs.nonneg', 'norm_nonneg'),
    ('Complex.abs.sum_le', 'norm_sum_le'),
]
imports = {}
for fn in os.listdir('Proofs'):
    if fn.endswith('.lean'):
        try:
            imports[fn[:-5]] = re.findall(r'^import Proofs\.([\w\']+)',
                                          read(f'Proofs/{fn}'), re.M)
        except Exception:
            imports[fn[:-5]] = []

def closure(m, seen=None):
    if seen is None:
        seen = set()
    for d in imports.get(m, ()):
        if d not in seen:
            seen.add(d)
            closure(d, seen)
    return seen

def has_shim(f):
    return 'def Complex.abs' in read(f)

for f in resid:
    s = read(f)
    # only real code usage (not just comments) — cheap heuristic: usage count
    if 'Complex.abs' not in s:
        continue
    mod = os.path.basename(f)[:-5]
    s0 = s
    for o, n in CX_RENAMES:
        if o in s:
            log[f'cx {o}'] += s.count(o)
            s = s.replace(o, n)
    # shim needed if neither this file nor its Proofs-closure defines it
    if 'Complex.abs' in s and 'def Complex.abs' not in s:
        dep_shim = any(os.path.exists(f'Proofs/{d}.lean') and has_shim(f'Proofs/{d}.lean')
                       for d in closure(mod))
        if not dep_shim:
            lines = s.split('\n')
            imp_idx = [i for i, l in enumerate(lines) if l.startswith('import')]
            if imp_idx:
                at = imp_idx[-1] + 1
                lines.insert(at, '')
                lines.insert(at + 1, '/-- v4.31 compat shim: `Complex.abs` was removed from Mathlib (use `‖·‖`). -/')
                lines.insert(at + 2, SHIM)
                s = '\n'.join(lines)
                log['cx shim inserted'] += 1
    if s != s0:
        write(f, s)

print('touched files:', len(touched))
for k, v in sorted(log.items()):
    print(f'  {k}: {v}')
open(f'{SCR}/dr9-touched.txt', 'w').write('\n'.join(sorted(
    os.path.basename(f)[:-5] for f in touched)) + '\n')
