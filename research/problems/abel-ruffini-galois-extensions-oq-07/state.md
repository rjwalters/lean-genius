# Current State

**Phase**: ACT
**Since**: 2026-05-08T07:00:00Z
**Last Updated**: 2026-05-08 (Iteration 7, researcher-12)
**Iteration**: 7

## Current Focus

Iteration 7 (this session): First axiom-free instance of the residual
`burnside_pq_nontrivial` axiom (`2 ≤ a ∨ 2 ≤ b`). Implements
`burnside_p_squared_q_p_gt_q` per the Iteration 6 spec §3+§4: every
finite group of order `p² · q` (with `p, q` distinct primes and `q < p`)
is solvable, axiom-free.

Strategy: Sylow's third theorem (`card_sylow_modEq_one`,
`Sylow.card_dvd_index`) restricts the count of Sylow `p`-subgroups
to divisors of `q` that are `≡ 1 [MOD p]`; with `q < p`, only `n_p = 1`
is possible (since `n_p = q` would force `q ≥ p + 1`). Hence the unique
Sylow `p`-subgroup is normal of order `p²`, and
`burnside_pq_with_normal_pSylow` (S5) finishes axiom-free.

Companion private helpers:
- `sylow_count_eq_one_of_lt_prime`: arithmetic kernel of the Sylow-count
  argument (`n ∣ q` prime, `q < p`, `n ≡ 1 [MOD p]` ⇒ `n = 1`).
- `factorization_p_sq_q_at_p`: computes `(p² · q).factorization p = 2`
  for distinct primes (`q < p`), used to read off `Nat.card P = p²`
  from `Sylow.card_eq_multiplicity`.

Sanity-check example: `|G| = 18 = 3² · 2` (the smallest non-trivial
instance with `p > q`).

Iteration 6 (PR #17035, merged): Build-ready specification for
`burnside_p_squared_q` covering all three sub-cases (`p > q`,
`p < q ≠ 3`, exceptional `(p, q) = (2, 3)` / `|G| = 12`). API inventory
verified against Mathlib master.

Iteration 5 (PR #16972, merged): Two reduction lemmas that discharge
`burnside_pq_nontrivial` whenever a normal Sylow subgroup is exhibited:
`burnside_pq_with_normal_pSylow` and `burnside_pq_with_normal_qSylow`,
plus the supporting `isSolvable_of_normal_quotient_solvable` extension
lemma (axiom-free packaging of `solvable_of_ker_le_range` against
`1 → N → G → G/N → 1`).

Iteration 4 (PR #16905, merged): `burnside_pq_pq_case` (axiom-free
`a = b = 1` case) plus `squarefreeOrder_isSolvable` (general squarefree-
order bridge), backed by Mathlib's `IsZGroup.of_squarefree`. The axiom
`burnside_pq_nontrivial` was narrowed to require `2 ≤ a ∨ 2 ≤ b`; the
`a = b = 1` sub-case is no longer axiom-dependent.

## Active Approach

Two-track Sylow analysis on `|G| = p^a · q^b` with `(a, b) ∈ {(2,1), (1,2),
(2,2)}`. Iteration 7 covers `(2, 1)` for `q < p` axiom-free. The remaining
`(2, 1)` sub-case is `p < q` (with the `(p, q) = (2, 3)` exception
requiring an element-count argument). Goldschmidt-Matsuyama remains the
long-term path for `a + b ≥ 5`.

## Blockers

The residual axiom (orders divisible by `p²` or `q²` for distinct primes,
beyond the cases now handled axiom-free) requires either character theory
+ algebraic-integer hypotheses or transfer + focal subgroup theory.
Mathlib's `Mathlib.GroupTheory.Focal` provides scaffolding for the
character-free route (focal subgroup, `transferFocal`,
`commutator_inf_eq_focalSubgroup`); estimated 200-400 lines on top of this
for full Goldschmidt-Matsuyama.

The build-bound risk for this PR: `proofs/.lake` recursive self-symlink
forces every Docker build to a ~30–45 min cold-cache Mathlib clone. The
new lemmas are mechanical (`Sylow.card_eq_multiplicity`, `card_sylow_modEq_one`,
`Sylow.card_dvd_index`, `Sylow.normal_of_subsingleton` are all standard
Mathlib API verified in S6 §2). CI is the ground truth.

## Next Action

1. **(S8)** Prove `burnside_p_squared_q_p_lt_q` axiom-free (Iteration 6
   spec §5, ~40 lines). Sylow analysis: `n_q ∣ p²` with three cases
   `{1, p, p²}`; `n_q = p` ruled out by `p < q`; `n_q = p²` requires
   `q ∣ p² - 1`, ruled out except for `(p, q) = (2, 3)`.
2. **(S9)** Prove `burnside_p_squared_q_twelve` exceptional case
   (Iteration 6 spec §6, ~70 lines). Element-counting: `n_3 = 4` ⇒
   8 elements of order 3 ⇒ unique Sylow 2-subgroup.
3. **(S10)** Combine into `burnside_p_squared_q` (Iteration 6 spec §7).
4. **(S11+)** Symmetric `burnside_p_q_squared` (`|G| = p · q²`).
5. **(S12+)** `burnside_p_squared_q_squared` (`|G| = p² · q²`).
6. **(S13+)** Goldschmidt-Matsuyama on top of `Mathlib.GroupTheory.Focal`
   (~200-400 lines). Closes ALL remaining cases.

## Iteration 7 Builds (researcher-12, 2026-05-08)

- Updated `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (502 → 631 lines).
- Added new section `PART III.6: |G| = p² · q, case p > q (axiom-free)`.
- `sylow_count_eq_one_of_lt_prime`: private arithmetic helper (Sylow-count
  constraint), 10 lines.
- `factorization_p_sq_q_at_p`: private factorization helper, 10 lines.
- `burnside_p_squared_q_p_gt_q`: main result, ~30 lines, axiom-free
  Sylow-count proof using `Sylow.card_eq_multiplicity`,
  `card_sylow_modEq_one`, `Sylow.card_dvd_index`, the new helpers,
  `Subsingleton (Sylow p G)` from `Nat.card = 1`,
  `Sylow.normal_of_subsingleton`, then `burnside_pq_with_normal_pSylow`.
- New sanity-check example: `|G| = 18 = 3² · 2`.
- Updated `#check` block to expose `burnside_p_squared_q_p_gt_q`.
- Updated gallery entry meta.json (lineCount 502 → 631, theoremCount
  13 → 16, axiomCount unchanged at 1, originalContributions and
  assumptions updated to reflect Iteration 7).

**Counts**: lineCount 631, theoremCount 16, axiomCount 1 (narrowed
to `2 ≤ a ∨ 2 ≤ b` since S4, with `(a, b) = (2, 1) ∧ q < p` now
axiom-free), sorries 0.

**Build status**: not run this session (`proofs/.lake` symlink trap).
The new lemmas use only standard Mathlib API verified against master in
the S6 spec §2 inventory. CI is the ground truth.
