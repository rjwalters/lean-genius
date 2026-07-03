# Current State

**Phase**: ACT (S4b step-2 tail-sum SHIPPED — remaining S4b analytic layer)
**Since**: 2026-07-03
**Iteration**: 6 (S4b step-2 discrete-layer-cake tail-sum SHIPPED; S4a variance L¹-bound; S3 martingale; S2 Kronecker; S1 survey)

## Current Focus

**S2 (Kronecker) and S3 (Kolmogorov martingale assembly) are BOTH DONE — do not
re-derive either.** All in `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean`,
verified 0-sorry / 0-axiom (only propext/Classical.choice/Quot.sound):

- `LawsOfLargeNumbers.MZ.kronecker_lemma` (L135) — S2
- `LawsOfLargeNumbers.MZ.tendsto_weighted_average_zero` (L60) — S2 Toeplitz core
- `LawsOfLargeNumbers.MZ.ae_tendsto_kronecker_average_zero` (L285) — a.e. lift
- `LawsOfLargeNumbers.MZ.martingale_sum_of_indep_mean_zero` (L338) — **S3 NEW**:
  shifted partial sums of independent mean-zero L¹ vars are a martingale wrt the
  natural filtration (via `iIndepFun.condExp_natural_ae_eq_of_lt` +
  `martingale_of_condExp_sub_eq_zero_nat`).
- `LawsOfLargeNumbers.MZ.ae_tendsto_sum_of_indep_of_eLpNorm_bdd` (L382) — **S3
  NEW**: Kolmogorov's criterion reduced to a uniform L¹ bound, via
  `Submartingale.exists_ae_tendsto_of_bdd` + a one-step index shift.

The S3 survey was right: the a.e.-convergence engine and all glue lemmas were
already in Mathlib; S3 was assembly, and it is now assembled.

## Active Approach

None in-flight. Next work item is S4 below.

## S4b step-2 — DONE (iteration 6, PR pending)

The **discrete layer-cake tail-sum bound** — the Borel–Cantelli input for the truncation
step — is now in `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean` (§ TailSum), all
**0-sorry / 0-axiom** (`#print axioms` = propext/Classical.choice/Quot.sound):

- `tsum_indicator_add_one_le` — pure ENNReal helper: `∑ₙ 𝟙{n+1 ≤ z} = ⌊z⌋₊ ≤ z`.
- `tsum_measure_add_one_le_lintegral` — `∑ₙ μ{Z ≥ n+1} ≤ ∫⁻ ofReal Z` for measurable
  `Z ≥ 0`. Proof: `lintegral_indicator_one` + `lintegral_tsum` swap + pointwise count.
- `tsum_measure_add_one_ne_top` — finiteness corollary feeding `measure_limsup_eq_zero`.

**Do NOT re-derive this.** Applied to `Z = |X₀|ᵖ` (with identical distribution and
`𝔼|X₀|ᵖ < ∞`), it yields `∑ᵢ P(|Xᵢ| > i^{1/p}) < ∞`, hence a.s. `Xᵢ = Yᵢ` eventually.

## Blockers

- **S4b step-1 (identical-distribution reduction, ~1 session):** connect the tail-sum
  bound to the i.i.d. truncation. From `IdentDistrib (Xᵢ) (X₀)` derive
  `μ{|Xᵢ| > i^{1/p}} = μ{|X₀|ᵖ > i}`, then apply `tsum_measure_add_one_ne_top` with
  `Z = |X₀|ᵖ` and the first Borel–Cantelli lemma (`measure_limsup_eq_zero`, needs the
  `≠ ∞` we now provide) to get `∀ᵐ ω, ∀ᶠ i, Xᵢ ω = Yᵢ ω` where `Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}`.
- **S4b step-3 (centered-truncation control, ~1 session):** `∑ᵢ 𝔼Yᵢ / n^{1/p} → 0`
  using `𝔼X = 0` and a moment/`rpow` estimate on the truncated means (Kronecker-style).
- **S4b step-4 (variance-sum estimate, ~1–2 sessions):** `∑ᵢ Var(Yᵢ)/i^{2/p} < ∞`
  (uses `p < 2`, so `2/p > 1` — this is where `p < 2` is *essential*). Then feed into
  `ae_tendsto_sum_of_indep_of_variance_bdd` (S4a) and lift via
  `ae_tendsto_kronecker_average_zero` (S2) for the final M–Z normalisation.

**DONE (do not re-derive):** S1 survey · S2 Kronecker · S3 martingale · **S4a variance
L¹-bound** (`ae_tendsto_sum_of_indep_of_variance_bdd` + `eLpNorm_two_sq_eq_evariance` +
`eLpNorm_two_partialSum_le`, 0-axiom) · **S4b step-2 tail-sum** (this iteration).

## Next Action

- **S4b step-1 (next):** identical-distribution reduction — from `IdentDistrib (Xᵢ) (X₀)`
  get `μ{|Xᵢ| > i^{1/p}} = μ{|X₀|ᵖ > i}`, apply `tsum_measure_add_one_ne_top` (this
  iteration) + first Borel–Cantelli (`measure_limsup_eq_zero`) ⟹ a.s. `Xᵢ = Yᵢ` eventually.
  Then S4b step-3 (centering) and step-4 (variance sum, uses `p<2`).

## Attempt Counts

- Total attempts: 6 (S1 survey; S2 Kronecker; S3 martingale assembly; +glue; S4a variance L¹ bound; S4b step-2 tail-sum)
- Current approach attempts: 1 (S4b step-2 tail-sum — landed on 2nd elaboration; calc restructure of the lintegral_tsum swap)
- Approaches tried: 5 (S1 literature/decomposition; S2 Abel+Toeplitz;
  S3 natural-filtration martingale + upcrossing engine; S4a orthogonality + eLpNorm bridge;
  S4b discrete layer cake via lintegral_tsum + floor count)
