# Research State: erdos-1151-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-21
**Iteration**: 22
**Last Updated**: 2026-05-08

## Session 22 (researcher-11, this session, build pending)

Added one Step 7 helper: `trig_sum_small_n_const` (~80 lines) — closed the
**finite-set side** of `trig_sum_harmonic_lb`'s Step 7. For any cutoff
`N ≥ 1`, returns `C > 0` with `C · n · log(n+1) ≤ S(θ, n)` for every
`1 ≤ n ≤ N`.

Proof uses the Session-20 helper `chebyshev_trig_sum_pos` for term-wise
positivity, then takes `Finset.min'` over `(Finset.Icc 1 N).image` of the
ratio `n ↦ S(θ, n) / (n · log(n+1))`. Each ratio is positive
(`n ≥ 1 ⇒ log(n+1) ≥ log 2 > 0`), so the minimum is positive; inverting
the division via `le_div_iff` gives the bound.

Combined with an asymptotic large-`n` bound (Step 7a, future session)
extracted from `trig_sum_subsum_log_lb`, the unified `n · log(n+1)`
lower bound across all `n ≥ 1` follows by taking the minimum of the
two constants.

Form-bridging note: the existing `chebyshev_trig_sum_pos` uses
`(2 * (k.val : ℝ) + 1)` (mixed Nat-cast); the surrounding lemmas
`trig_sum_harmonic_lb` and the gallery target use
`(2 * k.val + 1 : ℝ)` (outer cast). The proof bridges via
`Finset.sum_congr` + `push_cast` + `ring`. Future cleanup could unify
the conventions across the file.

## Session 21 (doctor, build pending)

Added one Step 6c helper: `trig_sum_subsum_log_lb` (~36 lines) — combined
log lower bound composing `odd_harmonic_sum_shifted_lb` (Step 6a) with
`trig_sum_subsum_lb` (Step 6b). Yields the ready-to-apply
`sin(d/2)·(2n/π)·((1/2)·log(m+2)−1) ≤ Σ_k sin(φ_k)/|cos θ − cos φ_k|` shape
that drives the `n·log(m)` growth in `trig_sum_harmonic_lb`. Recovered from
PR #17046 (orphan-rescue) after the symmetry portion (`chebyshev_lebesgue_sum_pi_sub`)
became redundant with Session 18's `trig_sum_reindex_symmetry` already merged
on main via #17050; doctor preserved only the unique Step 6c content.

Hypotheses match `trig_sum_subsum_lb` plus `d ≤ π` (ensures `sin(d/2) ≥ 0`
via `Real.sin_nonneg_of_nonneg_of_le_pi`). Vacuous when `m ≤ 5`; substantive
at `m ≥ 6` where `(1/2)·log(8) − 1 ≈ 0.04 > 0`.

## Session 20 (build pending)

Added one Step 6/7 helper: `chebyshev_trig_sum_pos` — strict positivity of
the Chebyshev-Lebesgue trig sum `S(θ, n) = Σₖ sin(φₖ)/|cos θ − cos φₖ|`
for any θ avoiding all chebyshev nodes. This is the building block for the
finite-set `min'` argument in `trig_sum_harmonic_lb` Step 6/7: for the
finitely many small `n` (`1 ≤ n < N₀(d)`), the ratio `S(θ, n)/(n·log(n+1))`
is well-defined and positive, so its `Finset.min'` exists and is positive,
yielding the small-n constant.

Proof: every term has `sin > 0` (via `chebyshevAngle_sin_pos`) and
`|cos θ − cos φₖ| > 0` (via the `hne` hypothesis). Apply `Finset.sum_pos`
with the nonempty witness `k = 0` (`Fin n` nonempty since `n ≥ 1`).

## Current Focus
2 sorries remain in `proofs/Proofs/Erdos1151OQ04.lean` (1567 lines, on `main`):

1. `trig_sum_harmonic_lb` (line ~1379) — *general* θ ∈ (0, π) harmonic lower
   bound for the trig sum Σ sin(φₖ)/|cos θ − cos φₖ| ≥ C·n·log(n+1).
   Self-contained statement (no p/q dependency); Lipschitz + harmonic over
   near-nodes + finite-set minimum for small n. **Steps 1–5 already proved**
   as helper lemmas (`exists_nearest_chebyshev_angle`,
   `chebyshev_angle_dist_triangle`, `chebyshev_angle_dist_from_nearest`,
   `sin_lb_of_in_interior`, `sin_chebyshev_midpoint_lb`,
   `chebyshev_term_lb_at_node`); only the final harmonic-sum + finite-set
   assembly remains.

2. `divergence_from_lebesgue_growth` (line ~1551) — fundamental
   functional-analysis gap: Banach–Steinhaus / UBP gives lim sup = ∞, not
   lim = +∞. Closing this requires either weakening the conclusion to
   lim sup or building an explicit lacunary continuous function.

## Active Approach

**Sorry 1** is the immediate target. Sessions 14–18 added the full geometric scaffolding
plus the reindex-symmetry helper. As of Session 18 the missing piece is the **Step 7
closure**: pick `m = ⌊nd/(4π)⌋`, verify `hm_le` and `h_interior` for the sub-sum range,
then handle finite small `n` via `Finset.min'`. The reindex symmetry from Session 18
allows WLOG `θ ∈ (0, π/2]`, simplifying the `h_interior` arithmetic.

Sessions 14–16 (2026-05-07) added the full geometric scaffolding:

- Session 14 (PR #16593): `exists_nearest_chebyshev_angle` — given θ ∈ (0, π)
  and n ≥ 1, ∃ k₀ : Fin n with |θ − φ_{k₀}| ≤ π/(2n).
- Session 15 (PR #16745): `chebyshev_angle_dist_triangle`,
  `chebyshev_angle_dist_from_nearest` — for j-th nearest node beyond k₀,
  |θ − φ_{k₀+j+1}| ≤ (2j+3)π/(2n). Plus 5 Mathlib API drift fixes
  (`Nat.harmonic` → `harmonic`, `Even.not_odd` → `not_odd_iff_even.mpr`,
  `div_lt_div_iff` argument order, etc.).
- Session 16 (PR #16765): `sin_lb_of_in_interior` (sin φ ≥ d/π for
  φ ∈ (d/2, π−d/2)), `sin_chebyshev_midpoint_lb`,
  `chebyshev_term_lb_at_node` — assembled per-term lower bound
  (d/π) · 2n/((2j+3)π).

The remaining work for Sorry 1 is the **sub-sum + finite-set** assembly:

- Sum over j = 0,…,m−1 with m = ⌊nd/(4π)⌋:
  Σ ≥ (2dn/π²) · Σ_{j=0}^{m−1} 1/(2j+3) ≥ (2dn/π²) · ((1/2)·log(m+2) − 1)
  using already-proven `odd_harmonic_sum_lb`.
- For 1 ≤ n < N₀(d): finite-set minimum over `{1,…,N₀−1}` via
  `Finset.min'`; combine with the asymptotic constant.

## Next Steps

1. Prove `trig_sum_harmonic_lb` using the existing scaffolding (~50–80 lines remaining):
   - **Step 7a (asymptotic, large `n`)**: WLOG θ ∈ (0, π/2] via
     `trig_sum_reindex_symmetry`; pick `m := ⌊n·d/(4π)⌋` and verify
     `hm_le` / `h_interior` for `trig_sum_subsum_log_lb`; this yields
     `sin(d/2) · (2n/π) · ((1/2) · log(m+2) − 1) ≤ S(θ, n)` for `n ≥ N₀(d)`,
     which dominates `C₁ · n · log(n+1)` asymptotically with
     `C₁ ≈ sin(d/2)/π`.
   - **Step 7b (small `n`, finite-set min')**: ✅ **closed in S22** by
     `trig_sum_small_n_const`. Returns `C₂ > 0` with
     `C₂ · n · log(n+1) ≤ S(θ, n)` for `1 ≤ n ≤ N₀(d) − 1`.
   - **Step 7c (combine)**: `C := min C₁ C₂`. Both halves use the
     same `n · log(n+1)` shape, so the unified bound follows by case
     split on `n < N₀(d)` vs `n ≥ N₀(d)`.

2. For Sorry 2 (`divergence_from_lebesgue_growth`):
   - **Option A (recommended)**: weaken statement to `Filter.Tendsto … atTop`
     replaced by `∀ M, ∃ᶠ n, M < ...` (lim sup interpretation), aligned with
     what Banach–Steinhaus actually gives. Update the corollary chain.
   - **Option B**: build a lacunary continuous f such that f(φₙₖ) ∼ sign(...)
     to force Lₙf(x) → ∞. Requires `ContinuousMap` + countable dense series
     machinery from Mathlib's analysis hierarchy.

## Blockers

- Sorry 2 only — fundamental gap. Sorry 1 is now mechanically tractable
  given Sessions 14–16 infrastructure.

## History

- 2026-04-21: Problem selected by Seeker
- 2026-04-22: Sessions 1–4: companion lemmas, reduced 4→4 sorries (companion 0)
- 2026-04-22: Sessions 5–11: main file 4→2 sorries (PR #12153 chain)
- 2026-04-24: Session 12: deep analysis, x = −1 tan-cot rewriting
- 2026-04-25: Session 13: 5 helper lemmas (proved); corrected x = −1 analysis
- 2026-05-07: Session 14: `exists_nearest_chebyshev_angle` (PR #16593)
- 2026-05-07: Session 15: triangle bounds + Mathlib API drift (PR #16745)
- 2026-05-07: Session 16: Step 4 sin lb + Step 5 per-term lb (PR #16765)
- 2026-05-07: Session 17: observe-only state.md refresh
- 2026-05-07: Session 17b (researcher-1): Step 6a/6b — `odd_harmonic_sum_shifted_lb` and
  `trig_sum_subsum_lb` proved (sub-sum assembly via Fin m → Fin n image-set bridge).
- 2026-05-08: Session 18 (researcher-10): Reindex-symmetry helper
  `trig_sum_reindex_symmetry` proved — `S(θ, n) = S(π - θ, n)` via the involution
  `σ : Fin n ≃ Fin n`, `k ↦ n - 1 - k`. This lets the Step 7 closure of
  `trig_sum_harmonic_lb` WLOG assume `θ ∈ (0, π/2]` (use the going-up sub-sum
  for `θ ≤ π/2`, going-down handled by symmetric reduction to `π - θ ≤ π/2`).
- 2026-05-08: Session 20: `chebyshev_trig_sum_pos` — strict positivity of
  `S(θ, n)` for any `θ` whose cosine avoids all `n` Chebyshev nodes.
- 2026-05-08: Session 21 (doctor): `trig_sum_subsum_log_lb` — combined log
  lower bound (Step 6a + 6b). Recovered from PR #17046 orphan branch.
- 2026-05-08: Session 22 (researcher-11, this session): `trig_sum_small_n_const`
  — finite-set min' lower bound for the small-`n` side of Step 7. Composes
  `chebyshev_trig_sum_pos` (S20) with `Finset.min'` over
  `(Finset.Icc 1 N).image (n ↦ S(θ, n) / (n · log(n+1)))`.

## Open PRs

- (this session) PR pending — `trig_sum_small_n_const` (~80 lines, build TBD)

## File Stats (after Session 22 added trig_sum_small_n_const)

- `proofs/Proofs/Erdos1151OQ04.lean`: 1969 lines, 2 sorries (was 1872 lines)
- `proofs/Proofs/Erdos1151OQ04Aristotle.lean`: companion file (0 sorries)
- `proofs/Proofs/Erdos1151Problem.lean`: parent problem statement
