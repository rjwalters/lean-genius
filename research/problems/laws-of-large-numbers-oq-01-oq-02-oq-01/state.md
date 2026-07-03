# Current State

**Phase**: ACT (S4b step-1 truncation reduction SHIPPED — remaining S4b analytic layer)
**Since**: 2026-07-03
**Iteration**: 7 (S4b step-1 i.i.d. Borel–Cantelli truncation SHIPPED; S4b step-2 tail-sum; S4a variance L¹-bound; S3 martingale; S2 Kronecker; S1 survey)

## Current Focus

**S2 (Kronecker), S3 (Kolmogorov martingale assembly), S4a (variance L¹ bound),
S4b step-2 (tail-sum) and S4b step-1 (i.i.d. truncation) are ALL DONE — do not
re-derive any.** All in `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean`,
verified 0-sorry / 0-axiom (only propext/Classical.choice/Quot.sound).

## S4b step-1 — DONE (iteration 7, this session)

The **i.i.d. Borel–Cantelli truncation reduction** — connecting the step-2 tail-sum bound
to the actual truncation event — is now in the file (§ TruncationReduction), all
**0-sorry / 0-axiom** (`#print axioms` = propext/Classical.choice/Quot.sound on all three):

- `rpow_inv_lt_iff_lt_rpow` — elementary threshold reindex `a^{1/p} < b ↔ a < bᵖ`
  (`0<p`, `0≤a`, `0≤b`), via `Real.rpow_lt_rpow_iff` + `Real.rpow_inv_rpow`.
- `tsum_measure_truncation_ne_top_of_identDistrib` — for i.i.d. `Xᵢ` with `𝔼|X₀|ᵖ<∞`,
  the truncation tail sum `∑ᵢ μ{i^{1/p} < |Xᵢ|} ≠ ∞`. Proof: transfer each tail measure
  to `X₀` (`IdentDistrib.measure_mem_eq` on the measurable set `{y | i^{1/p}<|y|}`),
  reindex to `{i < |X₀|ᵖ}` (`rpow_inv_lt_iff_lt_rpow`), peel the `i=0` term
  (`tsum_eq_zero_add'`, bounded by `1`), and dominate the rest by
  `tsum_measure_add_one_ne_top` (step 2) with `Z=|X₀|ᵖ`.
- `ae_eventually_abs_le_rpow_of_identDistrib` — feeds the finiteness into
  `MeasureTheory.ae_eventually_notMem` ⟹ `∀ᵐ ω, ∀ᶠ i, |Xᵢ ω| ≤ i^{1/p}`, the exact
  Borel–Cantelli output reducing MZ to its truncated version.

**Do NOT re-derive.** The truncation is now justified: a.s. `Xᵢ = Yᵢ` eventually where
`Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}`.

### Reusable gotcha (Mathlib v4.26)

- **`Summable.tsum_eq_zero_add` (dot form) is `whnf`-pathological** on a
  `μ {ω | … }`-valued summand: `rw [Summable.tsum_eq_zero_add ENNReal.summable]` blows past
  1 000 000 heartbeats at `whnf`, *even on a fully abstract `g : ℕ → ℝ≥0∞`* and even when
  stated as a fully-typed `have`. **Fix: use the primed, non-dot idiom
  `rw [tsum_eq_zero_add' ENNReal.summable]`** (this is exactly how Mathlib's own
  `Topology/Instances/ENNReal/Lemmas.lean` peels ENNReal tsums). Compiles instantly.

## Active Approach

None in-flight. Next work item is S4b step-3 / step-4 below.

## Blockers

- **S4b step-3 (centered-truncation control, ~1 session):** `∑ᵢ 𝔼Yᵢ / n^{1/p} → 0`
  using `𝔼X = 0` and a moment/`rpow` estimate on the truncated means (Kronecker-style).
- **S4b step-4 (variance-sum estimate, ~1–2 sessions):** `∑ᵢ Var(Yᵢ)/i^{2/p} < ∞`
  (uses `p < 2`, so `2/p > 1` — this is where `p < 2` is *essential*). Then feed into
  `ae_tendsto_sum_of_indep_of_variance_bdd` (S4a) and lift via
  `ae_tendsto_kronecker_average_zero` (S2) for the final M–Z normalisation.

**DONE (do not re-derive):** S1 survey · S2 Kronecker · S3 martingale · **S4a variance
L¹-bound** (`ae_tendsto_sum_of_indep_of_variance_bdd` + `eLpNorm_two_sq_eq_evariance` +
`eLpNorm_two_partialSum_le`) · **S4b step-2 tail-sum** · **S4b step-1 i.i.d. truncation**
(this iteration). All 0-axiom.

## Next Action

- **S4b step-3 (next):** centered-truncation control `∑ᵢ 𝔼Yᵢ / n^{1/p} → 0`. With
  step-1 done, the surviving work is the two analytic estimates (step-3 centering,
  step-4 variance sum using `p<2`), then final assembly:
  `ae_tendsto_average_zero_of_variance_weighted_bdd` (S5) applied to the centered
  truncations `Yᵢ − 𝔼Yᵢ`, combined with the step-1 a.s. eventual `Xᵢ = Yᵢ`.

## Attempt Counts

- Total attempts: 7 (S1 survey; S2 Kronecker; S3 martingale assembly; +glue; S4a variance L¹ bound; S4b step-2 tail-sum; S4b step-1 i.i.d. truncation)
- Current approach attempts: 1 (S4b step-1 — landed after diagnosing the `tsum_eq_zero_add` whnf pathology; salvaged prior interrupted draft off origin/main)
- Approaches tried: 6 (S1 literature/decomposition; S2 Abel+Toeplitz;
  S3 natural-filtration martingale + upcrossing engine; S4a orthogonality + eLpNorm bridge;
  S4b step-2 discrete layer cake via lintegral_tsum + floor count;
  S4b step-1 IdentDistrib transfer + rpow reindex + tsum peel + first Borel–Cantelli)
