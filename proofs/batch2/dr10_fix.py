#!/usr/bin/env python3
"""Doctor increment-3 wave DR10 mechanical sweeps (issue #38065).

Families (all v4.31-source-verified, restricted to RESIDUAL files):
  1. reduceDite -> reduceDIte (simp-attr casing).
  2. Matrix stdBasisMatrix -> single (incl. lemma-name suffixes), dedupe simp args.
  3. Zsqrtd projection renames: mul_re -> re_mul, add_im -> im_add, ….
  4. Nat.primeFactorsList_prime_pow hp (pos) -> Nat.Prime.primeFactorsList_pow hp
     (positivity hypothesis dropped in v4.31).
  5. Nat.nth_prime_strictMono -> (Nat.nth_strictMono Nat.infinite_setOf_prime).
  6. Dot-on-underapplied-iff fixes (v4.31 no longer resolves `C.mpr` when C
     has explicit args): Nat.find_eq_iff.mpr -> (Nat.find_eq_iff _).mpr, ….
  7. Complex.norm_eq_abs compat theorem after existing Complex.abs shims;
     direct rewrites where the file has no shim.
"""
import re, os, collections

ROOT = '/Users/rwalters/GitHub/lean-genius/.loom/worktrees/issue-38065/proofs'
SCR = '/private/tmp/claude-501/-Users-rwalters-GitHub-lean-genius/3191fbf6-af2a-4a7f-8220-2fd75a0ce237/scratchpad'
os.chdir(ROOT)

resid = set()
for l in open('batch2/verify-results.tsv'):
    p = l.rstrip('\n').split('\t')
    if p[1] == 'RESIDUAL' and os.path.exists(f'Proofs/{p[0]}.lean'):
        resid.add(f'Proofs/{p[0]}.lean')
touched = set()
log = collections.Counter()

def read(f): return open(f, encoding='utf-8').read()
def write(f, s):
    open(f, 'w', encoding='utf-8').write(s)
    touched.add(f)

SIMPLE = [
    ('reduceDite', 'reduceDIte'),
    ('Zsqrtd.mul_re', 'Zsqrtd.re_mul'),
    ('Zsqrtd.mul_im', 'Zsqrtd.im_mul'),
    ('Zsqrtd.add_re', 'Zsqrtd.re_add'),
    ('Zsqrtd.add_im', 'Zsqrtd.im_add'),
    ('Zsqrtd.sub_re', 'Zsqrtd.re_sub'),
    ('Zsqrtd.sub_im', 'Zsqrtd.im_sub'),
    ('Nat.nth_prime_strictMono', '(Nat.nth_strictMono Nat.infinite_setOf_prime)'),
]
DOT_UNDERAPP = [
    ('Nat.find_eq_iff.mpr', '(Nat.find_eq_iff _).mpr'),
    ('Nat.find_eq_iff.mp', '(Nat.find_eq_iff _).mp'),
    ('Nat.primeFactorsList_eq_nil.mpr', '(Nat.primeFactorsList_eq_nil _).mpr'),
    ('Nat.primeFactorsList_eq_nil.mp', '(Nat.primeFactorsList_eq_nil _).mp'),
]
PFL = re.compile(r'Nat\.primeFactorsList_prime_pow\s+([\w.\']+)(\s+\((?:[^()]|\([^()]*\))*\))?')

for f in sorted(resid):
    s = read(f)
    s0 = s
    for o, n in SIMPLE + DOT_UNDERAPP:
        if o in s:
            log[o] += s.count(o)
            s = s.replace(o, n)
    s, c = PFL.subn(lambda m: f'Nat.Prime.primeFactorsList_pow {m.group(1)}', s)
    if c: log['primeFactorsList_prime_pow'] += c
    # stdBasisMatrix family
    if 'stdBasisMatrix' in s:
        log['stdBasisMatrix'] += s.count('stdBasisMatrix')
        s = s.replace('stdBasisMatrix', 'single')
        s = s.replace('Matrix.single, Matrix.single', 'Matrix.single')
        s = s.replace('Matrix.StdBasisMatrix', 'Matrix.single')
    if s != s0:
        write(f, s)

# family 7: Complex.norm_eq_abs
COMPAT = ('/-- v4.31 compat: `Complex.norm_eq_abs` removed with `Complex.abs`. -/\n'
          'theorem Complex.norm_eq_abs (z : ℂ) : ‖z‖ = Complex.abs z := rfl')
for f in sorted(resid):
    s = read(f)
    if 'Complex.norm_eq_abs' not in s:
        continue
    s0 = s
    if 'def Complex.abs' in s and 'theorem Complex.norm_eq_abs' not in s:
        s = s.replace('noncomputable def Complex.abs (z : ℂ) : ℝ := ‖z‖',
                      'noncomputable def Complex.abs (z : ℂ) : ℝ := ‖z‖\n\n' + COMPAT)
        log['norm_eq_abs compat'] += 1
    else:
        # shimless files: rewrite the known patterns away
        s = s.replace('rw [Complex.norm_eq_abs, Complex.sq_abs]', 'rw [Complex.sq_norm]')
        s = s.replace('Complex.norm_eq_abs, Complex.norm_def', 'Complex.norm_def')
        if 'Complex.norm_eq_abs' in s and s != s0:
            log['norm_eq_abs leftover'] += 1
    if s != s0:
        write(f, s)
        log['norm_eq_abs file'] += 1

print('touched files:', len(touched))
for k, v in sorted(log.items()):
    print(f'  {k}: {v}')
open(f'{SCR}/dr10-touched.txt', 'w').write('\n'.join(sorted(
    os.path.basename(f)[:-5] for f in touched)) + '\n')
