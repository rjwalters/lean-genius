# Current State

**Phase**: ACT (S4a variance L¹-bound SHIPPED — S4b truncation remains)
**Since**: 2026-07-03
**Iteration**: 5 (S4a Kolmogorov-from-variance-sum SHIPPED; S3 martingale; S2 Kronecker; S1 survey)

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

## Blockers

- **S4a (variance L¹ bound, ~1 short session, self-contained):** discharge the
  `hbdd` hypothesis of `ae_tendsto_sum_of_indep_of_eLpNorm_bdd` from
  `∑ Var(X_i) < ∞`. On a probability space,
  `eLpNorm S_n 1 ≤ eLpNorm S_n 2 = sqrt(Var[S_n]) = sqrt(∑_{i≤n} Var[X_i]) ≤
  sqrt(∑ Var)`. Named Mathlib pieces: `ProbabilityTheory.IndepFun.variance_sum`
  (variance of independent sum = sum of variances), `evariance` ↔ `eLpNorm 2`
  bridge under mean-zero (`evariance_eq_lintegral_ofReal` / `variance` real
  form), `eLpNorm_le_eLpNorm_of_exponent_le` (needs `IsProbabilityMeasure`).
  Fiddly part: ENNReal/rpow bookkeeping connecting `eLpNorm _ 2` to the real
  `variance`. This yields the standalone Kolmogorov convergence criterion.
- **S4b (truncation + moment estimates, multi-session):** the M–Z-specific
  analytic layer — truncation `Y_i = X_i·1{|X_i| ≤ i^{1/p}}`, `∑ P(X_i≠Y_i)<∞`
  (Borel–Cantelli), centered-truncation control, and the variance-sum estimate
  `∑ Var(Y_i)/i^{2/p} < ∞` (uses `p < 2`). Then combine S4a + Kronecker lift.

## Next Action

- **S4a — DONE (iteration 5, PR pending).** `ae_tendsto_sum_of_indep_of_variance_bdd`
  discharges the `hbdd` L¹ bound from `∑_{i≤n} Var(Xᵢ) ≤ V`, plus the two supporting
  lemmas `eLpNorm_two_sq_eq_evariance` (the mean-zero `‖X‖₂² = eVar[X]` bridge — Mathlib
  gap) and `eLpNorm_two_partialSum_le` (uniform L² bound). All 0-axiom, build ✔ 7743 jobs.
- **S4b (next):** the truncation moment-estimate layer — `Y_i = X_i·1{|X_i| ≤ i^{1/p}}`,
  `∑ P(X_i≠Y_i)<∞` (Borel–Cantelli), centered-truncation control, variance-sum estimate
  `∑ Var(Y_i)/i^{2/p} < ∞` (uses `p < 2`). Then feed S4a into the Kronecker lift
  `ae_tendsto_kronecker_average_zero` for the final M–Z normalisation.

## Attempt Counts

- Total attempts: 5 (S1 survey; S2 Kronecker; S3 martingale assembly; +glue; S4a variance L¹ bound)
- Current approach attempts: 1 (S4a variance bound — landed on 2nd build)
- Approaches tried: 4 (S1 literature/decomposition; S2 Abel+Toeplitz;
  S3 natural-filtration martingale + upcrossing engine; S4a orthogonality + eLpNorm bridge)
