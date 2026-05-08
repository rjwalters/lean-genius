# Research State: erdos-1151-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-21
**Iteration**: 26
**Last Updated**: 2026-05-09

## Session 26 (researcher-12, this session, build pending)

Added the **Step 7a/asymptotic side packaging** as a new private helper
`trig_sum_harmonic_lb_asymp_le_half_pi` (~120 lines). For any
`θ ∈ (0, π/2]` whose cosine avoids all Chebyshev nodes:

```
∃ N₀ : ℕ, ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n ≥ N₀,
  C₁ · n · log(n+1) ≤ S(θ, n)
```

with `C₁ = sin(θ/2) / (2π)` and `N₀ = max N₀_log 4` (where `N₀_log` comes
from S24's `chebyshev_quarter_floor_log_asymp_lb`, and `4` is S23's hyp).

**Composition** (purely from already-merged helpers):

  1. `exists_nearest_chebyshev_angle` → `k₀ : Fin n` with closeness.
  2. `m := ⌊n·θ/(4π)⌋` via `Nat.floor_le` + `Nat.lt_floor_add_one`.
  3. S23 `chebyshev_quarter_floor_hm_le_and_cap_max` → `hm_le` + `hcap_max`.
  4. S22 `chebyshev_h_interior_of_close_and_max_index_cap` → `h_interior` (d := θ).
  5. S21 `trig_sum_subsum_log_lb` → `sin(θ/2)·(2n/π)·((1/2)·log(m+2)−1) ≤ S(θ,n)`.
  6. S24 `chebyshev_quarter_floor_log_asymp_lb` → `(1/4)·log(n+1) ≤ (1/2)·log(m+2)−1`.
  7. Multiply by nonneg `sin(θ/2)·(2n/π)`, algebraically rearrange to
     `(sin(θ/2)/(2π))·n·log(n+1) ≤ S(θ,n)`.
  8. Cast bridge mixed-cast → outer-cast sum form via
     `Finset.sum_congr` + `push_cast` + `ring`.

**Why this matters**: this is **exactly** the `hlarge` hypothesis consumed
by `trig_sum_combine_small_large_const` (Step 7c, in flight as PR #17457).
Once that PR merges, the `θ ∈ (0, π/2]` branch of `trig_sum_harmonic_lb`
closes in ~10 lines: pass S26 helper's output (`N₀`, `C₁`, `hlarge`) to
S25's combine helper. The general `θ ∈ (0, π)` branch then follows in ~20
lines via `trig_sum_reindex_symmetry` (S18, merged): `S(θ, n) = S(π−θ, n)`,
and `π−θ ∈ (0, π/2)` when `θ ∈ [π/2, π)`.

**No conflict with PR #17457**: this S26 helper inserts AT THE SAME
POSITION as #17457's combine helper (between S24 and `trig_sum_harmonic_lb`),
but the two helpers are independent. Whichever lands first triggers a
trivial rebase in the other.

## Session 24 (researcher-4, build pending, merged via #17438)

Added the **Step 7a residue (asymptotic log lower bound)** as a new private
helper `chebyshev_quarter_floor_log_asymp_lb` (~80 lines). For any `θ > 0`:

```
∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ m : ℕ,
  (n : ℝ) * θ / (4π) - 1 ≤ (m : ℝ) →
  (1/4) * log((n : ℝ) + 1) ≤ (1/2) * log((m : ℝ) + 2) - 1.
```

The standard Step 7a caller-side choice `m := ⌊n·θ/(4π)⌋ : ℕ` satisfies
the input hypothesis via `Nat.lt_floor_add_one`. Composed with the merged
S21 helper `trig_sum_subsum_log_lb` (whose RHS factor is exactly
`(1/2) · log((m : ℝ) + 2) − 1`), this yields an asymptotic
`(sin(θ/2) / (2π)) · n · log(n+1)` lower bound for the trig sum, ready
for `trig_sum_combine_small_large_const` (open: PR #17386).

**Witness**: `N₀ = ⌈16π² · e⁴ / θ²⌉` (provided by `exists_nat_gt(K + 1)`),
`c = 1/4`. The proof reduces

  `(1/2) · log(m+2) − 1 ≥ (1/4) · log(n+1)`  ⟺  `(m+2)² ≥ (n+1) · e⁴`

via `Real.log_le_log` + `Real.log_mul` + `Real.log_exp` + `Real.log_pow`.
From the hypothesis `m + 2 ≥ n·θ/(4π)`, `(m+2)² ≥ n²·θ²/(16π²)`. The
remaining `n²·θ²/(16π²) ≥ (n+1)·e⁴` ⟺ `n² ≥ K·(n+1)` where
`K := 16π²·e⁴/θ²`, which holds when `n ≥ K + 1`:

  `n² = n·n ≥ (K+1)·n ≥ K·n + n ≥ K·n + K = K·(n+1)`.

**Why this matters**: this is the **genuinely-asymptotic step** flagged
in PR #17386's body as "Step 4 (the genuinely-mathematical residue)".
With S21 (subsum_log_lb) + S22 (h_interior + small_n_const) + S23
(quarter_floor_hm_le_and_cap_max) + S24 (this session) merged, the only
remaining work for `trig_sum_harmonic_lb` is the **mechanical glue**:
WLOG-reduce to `θ ∈ (0, π/2]` via `trig_sum_reindex_symmetry` (S18),
pick `m := ⌊n·θ/(4π)⌋`, chain the merged helpers, and feed the result
to `trig_sum_combine_small_large_const`. No further inequality residue.

## Session 23 (researcher-3, build pending, merged via #17396)

Added the **Step 7a m-choice + arithmetic packager** as a new private helper
`chebyshev_quarter_floor_hm_le_and_cap_max` (~110 lines). Given:

  • `θ ∈ (0, π/2]`, `n ≥ 4`,
  • the standard nearest-node closeness `|θ - φ_{k₀}| ≤ π/(2n)`, and
  • any `m : ℕ` with `(m : ℝ) ≤ n·θ/(4π)` (e.g. `m := ⌊n·θ/(4π)⌋` via
    `Nat.floor_le`),

the lemma simultaneously discharges both arithmetic preconditions of the
trig sub-sum chain:

  • `hm_le`: `k₀.val + m + 1 ≤ n` (input to `trig_sum_subsum_log_lb`),
  • `hcap_max`: `(2(k₀+m)+1)·π/(2n) ≤ π - θ/2` (input to S22's
    `chebyshev_h_interior_of_close_and_max_index_cap`).

**Proof skeleton** (with `θ ≤ π/2` and `n ≥ 4`):

  1. `m·π/n ≤ θ/4 ≤ π/8`: multiply `(m : ℝ) ≤ n·θ/(4π)` by `π/n > 0`.
  2. `φ_{k₀} ≤ θ + π/(2n)` from `abs_le.mp hk₀_close`.
  3. `φ_{k₀+m} = φ_{k₀} + m·π/n ≤ π/2 + π/8 + π/8 = 3π/4 ≤ π - θ/2`.
  4. `2 k₀ ≤ n` (ℕ) from `(2k₀+1)π ≤ 2nθ + π ≤ nπ + π`; divide by π via
     `nlinarith`, cast.
  5. `8 m ≤ n` (ℕ) from `m·π/n ≤ π/8`, multiply by `8n`; cast.
  6. `omega` closes `k₀.val + m + 1 ≤ n` from `2 k₀ ≤ n`, `8 m ≤ n`,
     `n ≥ 4` (since `8(k₀+m+1) ≤ 5n + 8 ≤ 8n` for `n ≥ 3`).

**Why packaged this way**: the next session (Step 7a glue) will pick the
concrete `m := ⌊n·θ/(4π)⌋` and need both `hm_le` and `hcap_max` in the
*same* shape consumed by S22's `chebyshev_h_interior_of_close_and_max_index_cap`
verifier. Bundling both into one lemma keeps the asymptotic-branch caller
free of arithmetic boilerplate. The generality `(m : ℝ) ≤ n·θ/(4π)`
(rather than fixing `m := Nat.floor …`) leaves room for a tighter choice
if a future variant prefers `m := ⌊n·θ/(4π)⌋ - 1` for cleaner log estimates.

## Session 22 (researcher-3, h_interior verifier, merged via #17324)

Earlier in S22, researcher-3 added `chebyshev_h_interior_of_close_and_max_index_cap`
(~75 lines) — the **abstract h_interior verifier** that bridges:

  • `hk₀_close : |θ - φ_{k₀}| ≤ π/(2n)` and
  • `hcap_max : φ_{k₀+m} ≤ π - θ/2`

into the full `h_interior` of `trig_sum_subsum_lb` / `trig_sum_subsum_log_lb`
(setting `d = θ`). For each `j : Fin m`, both `θ/2 ≤ φ_{k₀+j+1}` (from
the closeness lower bound + section-spacing `(j+1)·π/n ≥ π/n = 2·(π/(2n))`)
and `φ_{k₀+j+1} ≤ π - θ/2` (monotone in the index, capped at `m`). All
arithmetic via `linarith` + `field_simp`. The S23 helper
`chebyshev_quarter_floor_hm_le_and_cap_max` (this session) is the natural
feeder for this lemma's `hcap_max` input when `m := ⌊n·θ/(4π)⌋`.

## Session 22 (researcher-11, trig_sum_small_n_const, merged via #17330)

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

1. Prove `trig_sum_harmonic_lb` using the existing scaffolding (~30–60 lines remaining):
   - **Step 7a (asymptotic, large `n`)**: WLOG `θ ∈ (0, π/2]` via
     `trig_sum_reindex_symmetry`; pick `m := ⌊n·θ/(4π)⌋` (with `Nat.floor_le`
     supplying the `(m : ℝ) ≤ n·θ/(4π)` hypothesis), then chain
     `chebyshev_quarter_floor_hm_le_and_cap_max` (S23) →
     `chebyshev_h_interior_of_close_and_max_index_cap` (S22) →
     `trig_sum_subsum_log_lb` to obtain
     `sin(θ/2) · (2n/π) · ((1/2) · log(m+2) − 1) ≤ S(θ, n)` for `n ≥ N₀(θ)`.
     Asymptotically dominates `C₁ · n · log(n+1)` with `C₁ ≈ sin(θ/2)/π`,
     once `log(m+2) ≥ (1/2)·log(n+1)` is established (use
     `Nat.lt_floor_add_one` + log-monotonicity).
   - **Step 7b (small `n`, finite-set min')**: ✅ **closed in S22** by
     `trig_sum_small_n_const`. Returns `C₂ > 0` with
     `C₂ · n · log(n+1) ≤ S(θ, n)` for `1 ≤ n ≤ N₀(θ) − 1`.
   - **Step 7c (combine)**: `C := min C₁ C₂`. Both halves use the
     same `n · log(n+1)` shape, so the unified bound follows by case
     split on `n < N₀(θ)` vs `n ≥ N₀(θ)`.

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
- 2026-05-08: Session 22 (researcher-11): `trig_sum_small_n_const` — finite-set
  min' lower bound for the small-`n` side of Step 7. Composes
  `chebyshev_trig_sum_pos` (S20) with `Finset.min'` over
  `(Finset.Icc 1 N).image (n ↦ S(θ, n) / (n · log(n+1)))`. Merged via #17330.
- 2026-05-08: Session 22 (researcher-3): `chebyshev_h_interior_of_close_and_max_index_cap`
  — abstract h_interior verifier from `hk₀_close` + `hcap_max`. Merged via #17324.
- 2026-05-08: Session 23 (researcher-3): `chebyshev_quarter_floor_hm_le_and_cap_max`
  — m-choice + arithmetic packager that, for `θ ∈ (0, π/2]`, `n ≥ 4`, and any
  `m : ℕ` with `(m : ℝ) ≤ n·θ/(4π)`, produces both `hm_le` and `hcap_max`
  inputs simultaneously. Merged via #17396.
- 2026-05-08: Session 24 (researcher-4): `chebyshev_quarter_floor_log_asymp_lb`
  — asymptotic log lower bound `(1/4)·log(n+1) ≤ (1/2)·log(m+2) − 1` for
  `n ≥ N₀(θ)` and `(m : ℝ) ≥ n·θ/(4π) − 1`. The genuinely-asymptotic step
  flagged in PR #17386's body; with this and the open combine helper merged,
  the only remaining work for `trig_sum_harmonic_lb` is the WLOG/m-choice glue.
  Merged via #17438.
- 2026-05-08: Session 25 (researcher-1, in flight): `trig_sum_combine_small_large_const`
  — Step 7c min-of-two-constants closure, replay of stale PR #17386 onto
  fresh `origin/main`. Open as PR #17457.
- 2026-05-09: Session 26 (researcher-12, this session): `trig_sum_harmonic_lb_asymp_le_half_pi`
  — asymptotic large-`n` packaging for `θ ∈ (0, π/2]`. Composes
  `exists_nearest_chebyshev_angle` (S14), `chebyshev_quarter_floor_hm_le_and_cap_max`
  (S23), `chebyshev_h_interior_of_close_and_max_index_cap` (S22),
  `trig_sum_subsum_log_lb` (S21), and `chebyshev_quarter_floor_log_asymp_lb`
  (S24) into the single `hlarge` hypothesis consumed by S25's
  combine helper. PR pending.

## Open PRs

- (this session, S26) PR pending — `trig_sum_harmonic_lb_asymp_le_half_pi`
  (~140 lines, build TBD) — packages the asymptotic large-`n` side for
  `θ ∈ (0, π/2]`; exactly the `hlarge` hypothesis #17457's combine
  helper expects.
- PR #17457 (researcher-1, S25 replay of stale PR #17386) —
  `trig_sum_combine_small_large_const` Step 7c min-of-two-constants closure.

## File Stats (after Session 26 added trig_sum_harmonic_lb_asymp_le_half_pi)

- `proofs/Proofs/Erdos1151OQ04.lean`: 2425 lines, 2 sorries (was 2288 on origin/main)
- `proofs/Proofs/Erdos1151OQ04Aristotle.lean`: companion file (0 sorries)
- `proofs/Proofs/Erdos1151Problem.lean`: parent problem statement
