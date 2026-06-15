# Research State: birthday-problem-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-13
**Iteration**: 4

## Current Focus
ACT-1 written: `proofs/Proofs/BirthdayProblemOQ01OQ01OQ03.lean` (new file,
namespace `BirthdayDistributionNonUniform`, `import Mathlib`). Implements the
T1–T4 plan from knowledge.md as a self-contained definitional model matching the
parent's rigor. **Build-pending** — written during the 2026-06-13 Docker outage,
shipped as a DRAFT PR (not machine-checked yet).

S5 (2026-06-15): the previously-deferred **T3 converse** is now written, closing
the last math gap. Added `sum_sq_sub_uniform` (variance identity
`∑ (1/d − p k)² = collisionProb p − 1/d`), `uniform_of_collisionProb_eq` (the CS
equality case via vanishing sum of squares), and `collisionProb_eq_iff_uniform`
(the full `collisionProb p = 1/d ↔ p` uniform). The variance-identity route is
the one surfaced and numerically certified in #24188; re-certified here exactly
over ℚ (20000 random vectors, d=2..12, identity holds; equality ⟺ uniform for
d=2..39). Still build-pending (blackout persists, see Blockers).

## Active Approach
- `collisionProb p = ∑ k, (p k)²`, `expectedCollisions n p = C(n,2)·collisionProb p`.
- T1 `collisionProb_uniform`: uniform `p ≡ 1/d` ⟹ `collisionProb = 1/d`
  (+ `expectedCollisions_uniform = C(n,2)/d`).
- T2 `collisionProb_ge`: Cauchy–Schwarz lower bound `1/d ≤ collisionProb p`.
  CS step is a **verbatim port over ℝ** of
  `ProbMethodSecondMoment.sq_sum_le_card_mul_sum_sq` (induction + `sub_sq` + `nlinarith`).
- T3 `collisionProb_eq_of_uniform`: forward direction.
- T3 converse `uniform_of_collisionProb_eq` + full `collisionProb_eq_iff_uniform`:
  via `sum_sq_sub_uniform` (variance identity) → `Finset.sum_eq_zero_iff_of_nonneg`
  + `sq_eq_zero_iff`. Uniform is the *unique* minimizer.
- T4 `expectedCollisions_ge`: `C(n,2)/d ≤ expectedCollisions p n`.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1

## Blockers
ACT file is written but cannot be machine-checked: the 2026-06-13 Docker /
`lake build` verification outage persists (`docker info` down) and the Aristotle
backend returns 404. Residual risk is confined to Mathlib v4.26 lemma-name /
API surface (e.g. `div_le_iff₀`, `nsmul_eq_mul`, `Finset.card_univ`) — all
build-surfaced, hence the DRAFT.

## Next Action
When Docker/verification is restored: build via
`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ01OQ03`, fix any
v4.26 API drift (watch `sub_sq`/`Finset.mul_sum`/`Finset.sum_eq_zero_iff_of_nonneg`/
`sq_eq_zero_iff` surface for the new T3-converse lemmas), un-draft the PR, then
promote status to completed. The math is now complete (T1–T4 + full T3 equality
characterization); the only remaining stretch (beyond OQ closure) is a genuine
product-PMF expectation derivation of E[X].
