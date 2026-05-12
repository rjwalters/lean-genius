# Current State

**Phase**: ACT (S3 — Davydov reduction + longrun_variance proof shipped)
**Since**: 2026-05-12T04:00:00Z
**Iteration**: 3

## Current Focus

S3 ACT — Discharge `longrun_variance_absolutely_convergent` by reducing it
to a single named Davydov sorry. The S2 sorry on long-run variance has been
replaced by a more granular and clearly-scoped sorry on
`davydov_covariance_inequality`. Net change to sorry count: 0; net change to
"proof depth": one full main theorem now provably reduces to Davydov.

Deliverables (this session):
- Extend `IbragimovHypotheses` with 3 fields: `alpha_nonneg`,
  `past_measurable`, `future_measurable` (needed to apply Davydov per-term).
- State `davydov_covariance_inequality` with `(p-2)/p` exponent and an
  abstract `α₀` upper bound parameter (S4 sorry).
- Prove `stationary_eLpNorm_eq` via Mathlib's `IdentDistrib.eLpNorm_eq`.
- Prove `polynomial_mixing_summable` combining polynomial decay + rpow
  monotonicity + `ibragimov_threshold_summable` + `summable_nat_add_iff`.
- Prove `longrun_variance_absolutely_convergent` by chaining the above with
  `Summable.of_nonneg_of_le` for the comparison test.

## Active Approach

**Sharp-threshold polynomial-mixing CLT** under (2+δ)-th moments. The proof
follows the standard Bernstein blocks template:
1. **Davydov's covariance inequality (S4)** ⇒ covariances are summable.
   - S3 status: stated cleanly; proof itself deferred to S4 (~150 lines).
2. **Long-run variance σ² = Var(X₁) + 2∑_{k≥1} Cov(X₁, X_{k+1}) absolute
   convergence (S3 — this session, proven modulo Davydov).**
3. Joint tuple stationarity strengthening (S5).
4. Bernstein blocks p_n, q_n (S6) decompose [1, n] into approximately
   independent large blocks.
5. Lindeberg condition on large blocks (S8) follows from the (2+δ)-th
   moment bound.
6. Invoke parent's Lindeberg-Feller CLT (S9) to conclude.

## Blockers

- **Mathlib has no α-mixing API** (confirmed S1). Continue using parent's
  `alphaMixingCoeff` and `AlphaMixingSequence`. Future upstream contribution
  would consolidate this stack.
- **Davydov's covariance inequality** is the single open analytic engine.
  S4 target.

## Next Action

**Session 4 next action**: Discharge `davydov_covariance_inequality`.

**Strategy** (Hölder + indicator decomposition):
1. For bounded random variables `X = a · 1_A`, `Y = b · 1_B` with
   `A ∈ ℱ`, `B ∈ 𝒢`:
   `Cov(X, Y) = ab · [μ(A ∩ B) - μ(A) · μ(B)] ≤ ab · α(ℱ, 𝒢)`.
2. Approximate general L^p X, Y by indicators via the level-set decomposition
   `X = ∫ 1_{X > t} dt`.
3. Apply Hölder with `(p, p/(p-1))` to bound the resulting double integral.
4. Sharp constant `12` comes from a careful tracking through the indicator
   approximation; references: Doukhan 1994 §1.2.2, Bradley 2007 Vol I Thm 3.7.

Estimate: ~150 lines, no Mathlib gaps beyond Hölder (already there).

Alternative path: **Refine `Stationary`** to joint tuple stationarity (S5
target prerequisite for Bernstein blocks). Could be done in parallel with
Davydov; ~40 lines for the type-level strengthening + 60 lines for the
key tuple-shift lemma.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Scaffold (md + json) | 0 Lean | merged #17778 |
| S2 | ORIENT | 4 def stubs + 2 thm stmts + 2 proven helpers | 231 | merged #17792 |
| S3 | ACT | Davydov stmt + 3 new helpers + longrun_variance proof | 402 | **this session** |
| S4 | ACT | Davydov covariance inequality proof | ~150 | next |
| S5 | ACT | Refine Stationary to tuple-joint stationarity | ~100 | |
| S6 | ACT | Bernstein blocks p_n, q_n + arithmetic | ~150 | |
| S7 | ACT | Large-block independence approximation | ~120 | |
| S8 | ACT | Lindeberg condition on blocks | ~100 | |
| S9 | ACT | Invoke parent's Lindeberg-Feller CLT | ~50 | |

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1 (S3 ACT Davydov-reduction)
- Approaches tried:
  - S1: OBSERVE scaffolding.
  - S2: ORIENT — predicates + structure + main theorem statements + 2 helpers.
  - S3: ACT — Davydov-modulo proof of long-run variance absolute convergence
    + extension of IbragimovHypotheses + 3 new proven theorems.

## Key Files

- `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` — **S3 expanded** (402 lines,
  7 theorems incl. 2 sorries, 4 proven helpers, 3 definitions, 1 structure with
  14 fields). The 3 new theorems added in S3:
  `stationary_eLpNorm_eq`, `polynomial_mixing_summable`,
  `davydov_covariance_inequality` (sorry).  The S2 sorry
  `longrun_variance_absolutely_convergent` is now proven.
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/meta.json` — updated
  with new theorem count (7), line count (402), mathlib dependencies, and
  section ranges.
- `proofs/Proofs/CentralLimitTheoremOQ02.lean` — parent file, unchanged.
