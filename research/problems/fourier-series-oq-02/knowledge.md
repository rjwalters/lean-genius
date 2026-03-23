# Knowledge Base: fourier-series-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Fourier coefficient decay under Hölder continuity: if f is α-Hölder on AddCircle T,
then ‖ĉ_n(f)‖ ≤ (C/2)·(T/(2|n|))^α. The proof uses half-period translation:
e_{-n}(x + T/(2n)) = -e_{-n}(x), giving a difference formula 2c_n = ∫(f(x)-f(x+s))·e(x)dμ.

---

## Insights

### Iteration 3 (2026-03-23): Core analytical infrastructure proved

**Key breakthroughs:**
- `quotient_norm_mk_le` from `Mathlib.Analysis.Normed.Group.Quotient` directly gives
  ‖↑s‖ ≤ |s| on AddCircle, resolving the prior blocker for distance bounds.
- `HolderWith` edist → dist conversion requires careful ENNReal → ℝ machinery:
  `edist_dist` rewrites, then `ENNReal.toReal_le_toReal` with finiteness proofs,
  then `ENNReal.toReal_rpow` and `ENNReal.toReal_ofReal`.
- `integral_product_bound` chains four Mathlib results:
  1. `norm_integral_le_integral_norm` (triangle inequality for integrals)
  2. `fourier_norm_one` (‖e_n(x)‖ = 1, so product norm = difference norm)
  3. `integral_mono_of_nonneg` with `holder_translation_bound` (pointwise bound)
  4. `integral_const` + `IsProbabilityMeasure.measure_univ` (total mass 1)

### Iteration 2 (2026-03-23): Initial infrastructure

- `fourier_apply` unfolds to ↑(n • x).toCircle → unit norm via simp
- `fourier_add_half_inv_index` takes explicit `(hT : 0 < T)`, not Fact instance
- `|halfPeriod T n|` simplifies via `abs_div + abs_of_pos + abs_mul + Int.abs_cast`

---

## Dead Ends

### fourierCoeff_difference_formula direct proof
Attempted to prove directly but hit integrability wall: `integral_sub` requires
`Integrable (fun x => f x * fourier (-n) x) haarAddCircle` which is not available
for general `f : AddCircle T → ℂ`. Adding integrability hypotheses changes the axiom
signature and breaks downstream `fourierCoeff_holder_decay`. Needs careful handling
of the non-integrable case (where both sides are 0 by convention).

**Possible approach:** Add `(hf_cont : Continuous f)` hypothesis to difference formula,
then discharge integrability via `Continuous.integrable` on compact AddCircle.
But this changes the axiom signature — need to update downstream code too.
