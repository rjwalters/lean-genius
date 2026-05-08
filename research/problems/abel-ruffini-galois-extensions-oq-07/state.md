# Current State

**Phase**: ACT
**Since**: 2026-05-08T15:30:00Z
**Iteration**: 7

## Current Focus

Iteration 7 axiom-free `|G| = p² · q`, case `p > q` committed:
`burnside_p_squared_q_p_gt_q` plus the private helper
`sylow_count_eq_one_of_lt_prime`. The axiom `burnside_pq_nontrivial`
statement is unchanged; this iteration discharges the `(a, b) = (2, 1)`
shape **whenever `p > q`** axiom-free. The remaining `p < q` case (S7.5)
and exceptional `(p, q) = (2, 3), |G| = 12` case (S8) follow.

## Active Approach

Sylow-counting analysis on `|G| = p² · q`:

- **`p > q` (this iteration)**: `n_p ≡ 1 [MOD p]` (Sylow's third theorem)
  and `n_p ∣ q` (Sylow's `card_dvd_index`). Since `q` is prime,
  `n_p ∈ {1, q}`; the case `n_p = q` would force `p ∣ q - 1`, but
  `q < p` makes that impossible. Hence `n_p = 1`, the unique Sylow
  `p`-subgroup is normal, and `burnside_pq_with_normal_pSylow` discharges.
- **`p < q ≠ 3` (S7.5)**: symmetric `n_q = 1` analysis. Three cases for
  `n_q ∈ {1, p, p²}`; rule out `n_q = p` by `q ∣ p - 1` contradiction
  with `p < q`; rule out `n_q = p²` via `q ∣ p² - 1` (only `(p, q) = (2, 3)`
  qualifies, excluded by hypothesis).
- **Exceptional `(p, q) = (2, 3), |G| = 12` (S8)**: when `n_3 = 4`, count
  `4 × 2 = 8` elements of order 3; remaining 4 form a unique `V_4`
  Sylow 2-subgroup, so `n_2 = 1` and the Sylow 2-subgroup is normal.

## Blockers

The residual axiom (orders divisible by `p²` or `q²` for distinct primes,
once `(2, 1)` and `(1, 2)` shapes are peeled off) requires either character
theory + algebraic-integer hypotheses or transfer + focal subgroup theory.
Mathlib's `Mathlib.GroupTheory.Focal` provides scaffolding for the
character-free route (focal subgroup, `transferFocal`,
`commutator_inf_eq_focalSubgroup`); estimated 200-400 lines on top of this
for full Goldschmidt-Matsuyama.

## Next Action

1. **(S7.5)** Prove `burnside_p_squared_q_p_lt_q` axiom-free per
   `session-6-p-squared-q-spec.md` §5 (~40 lines). Two `sorry`s in spec:
   `n_q ≠ p` (ruled out by `q ∣ p - 1`, `p < q`); `n_q ≠ p²` (ruled out
   by `q ∣ p² - 1` and exceptional flag).
2. **(S8)** Prove `burnside_p_squared_q_twelve` for the exceptional case
   `(p, q) = (2, 3), |G| = 12` via element counting (~70 lines).
3. **(post-S8)** Augment the main `burnside_pq` dispatch to peel off
   `(a, b) = (2, 1)` and `(1, 2)` axiom-free before invoking the
   (further-narrowed) axiom.
4. **(S9+)** `|G| = p² · q²` Sylow analysis (~150 lines); then
   Goldschmidt-Matsuyama on top of `Mathlib.GroupTheory.Focal`.

## Iteration 7 Builds (researcher-5, 2026-05-08)

- Updated `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`
  (502→614 lines, 13→15 theorems, 1 axiom unchanged, 0 sorries).
- Added `import Mathlib.GroupTheory.Sylow`.
- `sylow_count_eq_one_of_lt_prime` (private helper, ~12 lines): if
  `n ∣ q` (q prime), `q < p`, `n ≡ 1 [MOD p]`, then `n = 1`. Proof:
  `Nat.Prime.eq_one_or_self_of_dvd` + `Nat.modEq_iff_dvd'` + `omega`.
- `burnside_p_squared_q_p_gt_q` (~50 lines, axiom-free): pick a Sylow
  p-subgroup P, show `|P| = p²` via `Sylow.card_eq_multiplicity` (with
  factorization computation: `factorization (p²·q) p = 2` via
  `Nat.factorization_mul_apply_of_coprime` + `Prime.factorization_pow` +
  `factorization_eq_zero_of_not_dvd`); compute `P.index = q` via
  `Subgroup.card_mul_index`; derive `n_p = 1` via `card_sylow_modEq_one` +
  `Sylow.card_dvd_index` + the helper; promote to `Subsingleton` via
  `Nat.card_eq_one_iff_unique`; `Sylow.normal_of_subsingleton` makes P
  normal; `burnside_pq_with_normal_pSylow` discharges.
- New sanity-check example: `|G| = 75 = 5² · 3` axiom-free.
- Updated gallery entry meta.json (lineCount 502→614, theoremCount 13→15,
  substantiveTheoremCount 13→15, axiomCount unchanged at 1, added
  Mathlib.GroupTheory.Sylow import, added 7 new mathlibDependencies for
  Sylow API, added Part III.6 section, updated assumptions text,
  added new mainTheorems entry).

**Counts**: lineCount 614, theoremCount 15, substantiveTheoremCount 15,
axiomCount 1 (unchanged, but `(a, b) = (2, 1)` with `p > q` now
discharged outside the axiom), sorries 0.
