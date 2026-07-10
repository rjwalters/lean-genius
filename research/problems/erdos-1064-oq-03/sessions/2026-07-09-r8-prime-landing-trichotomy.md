# Session 2026-07-09 (researcher-8) — prime-landing trichotomy: full classifier value

**Mode**: REVISIT (RICH tier; fresh branch off origin/main) | **Outcome**: progress
(UNVERIFIED — Docker infra fully down all session: containerd `meta.db` + content-store
blob input/output errors, image build fails, `docker images` errors; operator-level, not
a code issue)

## What I Did
Completed the **transport-admissible prime-landing classification**. The file already
had the `.lt` criterion `classifySeed_lt_iff_of_seedS_one_seedE_prime`
(reversal ⇔ `φ(seedB a) + 2^{seedT a} < 2·(a − φ a)`) but **no `.eq`/`.gt` companions**,
so prime-landing seeds were only half-decided. Added:

- `classifySeed_eq_compare_of_seedS_one_seedE_prime` — the full-trichotomy refinement:
  for `seedS a = 1` and `seedE a` prime,
  `classifySeed a = compare (φ(seedB a) + 2^{seedT a}) (2·(a − φ a))`.
  Reduces the *entire* computable classifier to one two-term comparison, mirroring how
  `classifySeed_classifies` reduces the general family to
  `compare (φ a) (φ(seedE a)·2^{seedT a−1})`.
- `classifySeed_eq_iff_of_seedS_one_seedE_prime` — `.eq` companion (equality regime).
- `classifySeed_gt_iff_of_seedS_one_seedE_prime` — `.gt` companion (forward regime).

## Proof recipe
- The trichotomy is a structural generalization of the existing (VERIFIED) `.lt` proof:
  same `seed_spec` unpacking, same `hsub : φ(e)·2^{t−1} = e·2^{t−1} − 2^{t−1}` (from
  `e` prime), same `hstep`/`hCeq` at `s = 1`. Instead of `compare_lt_iff_lt` + one
  `omega`, do `rcases lt_trichotomy (φ a) (e·2^{t−1} − 2^{t−1})` and rewrite each of the
  three `compare` branches (`compare_lt_iff_lt`/`compare_eq_iff_eq`/`compare_gt_iff_gt`)
  with the matching seed-side relation closed by `omega`.
- The doubling identity `2a − φ(seedB a) = 2·(e·2^{t−1})` (from `hCeq`, `hEPt`) plus
  evenness of `φ(seedB a)` (`Nat.totient_even`) and `2^{t−1} ≥ 1` let `omega` clear the
  halves so `φ a ⋛ φ(e)·2^{t−1}` matches `(φ(seedB a) + 2^{t}) ⋛ 2·(a − φ a)` termwise.
- The two iff corollaries are one-line `rw [trichotomy, compare_eq_iff_eq/compare_gt_iff_gt]`.

## Sanity (paper) checks against the file's known seeds
- `21` (b=15, t=1, e=17 prime): `φ(15)+2 = 8+2 = 10 < 2·(21−12) = 18` → `.lt` ✓ (reversal).
- Sophie–Germain `15` (b=5? — via `3q`, e=q=5 prime): both sides `4q = 20` → `.eq` ✓.

## New declarations (all 0 sorry / 0 new axiom; UNVERIFIED, infra down)
- `classifySeed_eq_compare_of_seedS_one_seedE_prime`
- `classifySeed_eq_iff_of_seedS_one_seedE_prime`
- `classifySeed_gt_iff_of_seedS_one_seedE_prime`

## Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+~85 lines, 3 theorems)

## Next Steps
- Elementary side remains complete; only open direction is the density-1 analytic
  forward statement (smooth-number density / Luca–Pomerance) — a genuine Mathlib gap.
- Optional: an `.eq`/`.gt` analogue of `prime_landing_family_reversal` packaging the
  criterion into infinitely-often family membership (`EqualitySet`/`ForwardSet`).
