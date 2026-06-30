import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# q-Fold Residue-Class Splitting of the Geometric Series

## What This Proves

Fix an integer modulus `q ≥ 1` and a residue `a`.  For a ratio `r` in any
complete normed field with `‖r‖ < 1`, the arithmetic-progression subseries with
common difference `q` is itself a geometric series of ratio `r^q`:

  ∑_{n=0}^{∞} r^(q·n + a)  =  r^a / (1 − r^q).

Summing these `q` subseries over the residues `a = 0, 1, …, q−1` recombines into
the full geometric series:

  ∑_{a=0}^{q-1} ∑_{n=0}^{∞} r^(q·n + a)  =  ∑_{m=0}^{∞} r^m  =  1/(1 − r).

This is the `q`-fold generalisation of the even/odd (`q = 2`) splitting recorded
in `GeometricSeriesOQ09`, which is recovered here as the special case `q = 2`,
`a ∈ {0, 1}`.

## Why This Is Not Already in Mathlib

Mathlib provides the plain geometric series `tsum_geometric_of_norm_lt_one`
(`∑ rⁿ = (1−r)⁻¹`) but not the residue-class subsums.  The content is the
reindexing `r^(q·n + a) = r^a · (r^q)ⁿ`, together with the bound
`‖r^q‖ = ‖r‖^q < 1` (valid because `q ≥ 1`) which makes Mathlib's lemma
applicable at the new ratio `r^q`, plus the recombination identity, which rests
on the factorisation `1 − r^q = (1 − r)(1 + r + ⋯ + r^{q-1})`.

## Proof Strategy

1. **Key bound.** `‖r^q‖ = ‖r‖^q < 1` from `q ≠ 0` (`pow_lt_one₀`).
2. **Residue subseries.** Rewrite `r^(q·n + a) = r^a · (r^q)ⁿ` and apply
   `hasSum_geometric_of_norm_lt_one` at ratio `r^q`, scaled by `HasSum.mul_left`.
3. **Recombination.** Sum the `q` closed forms `r^a · (1−r^q)⁻¹` over
   `a : Fin q`.  Factor out `(1−r^q)⁻¹`, evaluate `∑_{a<q} r^a` with
   `geom_sum_eq`, and simplify using `1 − r^q = (1 − r)(∑_{a<q} r^a)`.

## Status: 0 sorries, 0 axioms (over any complete normed field)
-/

namespace GeometricSeriesOQ09OQ01

-- Several supporting lemmas are purely algebraic and do not use completeness;
-- `CompleteSpace` is only needed where the geometric series is summed.
set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜}

/-! ## Nonvanishing denominators -/

/-- `r ≠ 1` whenever `‖r‖ < 1`. -/
lemma ne_one (hr : ‖r‖ < 1) : r ≠ 1 := fun h => by simp [h] at hr

/-- `1 - r ≠ 0` whenever `‖r‖ < 1`. -/
lemma one_sub_ne_zero (hr : ‖r‖ < 1) : (1 : 𝕜) - r ≠ 0 :=
  sub_ne_zero.mpr (ne_one hr).symm

/-- `‖r^q‖ < 1` whenever `‖r‖ < 1` and `q ≠ 0`: the key bound that lets us apply
the geometric-series lemma at the new ratio `r^q`. -/
lemma norm_pow_lt_one (hr : ‖r‖ < 1) {q : ℕ} (hq : q ≠ 0) : ‖r ^ q‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg r) hr hq

/-- `1 - r^q ≠ 0` whenever `‖r‖ < 1` and `q ≠ 0`. -/
lemma one_sub_pow_ne_zero (hr : ‖r‖ < 1) {q : ℕ} (hq : q ≠ 0) :
    (1 : 𝕜) - r ^ q ≠ 0 :=
  sub_ne_zero.mpr fun h => by simpa [← h] using norm_pow_lt_one hr hq

/-! ## Residue-class subseries -/

/-- **Residue subseries, `HasSum` form**: for `q ≠ 0` and any residue `a`,
`∑_{n} r^(q·n + a) = r^a / (1 − r^q)`. -/
theorem hasSum_geometric_residue (hr : ‖r‖ < 1) {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    HasSum (fun n : ℕ => r ^ (q * n + a)) (r ^ a * (1 - r ^ q)⁻¹) := by
  have h := hasSum_geometric_of_norm_lt_one (norm_pow_lt_one hr hq)
  have key : (fun n : ℕ => r ^ (q * n + a)) = (fun n : ℕ => r ^ a * (r ^ q) ^ n) := by
    funext n; rw [pow_add, pow_mul]; ring
  rw [key]
  exact h.mul_left (r ^ a)

/-- **Residue subseries, `tsum` form**: `∑_{n} r^(q·n + a) = r^a / (1 − r^q)`. -/
theorem tsum_geometric_residue (hr : ‖r‖ < 1) {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    ∑' n : ℕ, r ^ (q * n + a) = r ^ a * (1 - r ^ q)⁻¹ :=
  (hasSum_geometric_residue hr hq a).tsum_eq

/-- Each residue subseries is summable. -/
theorem summable_geometric_residue (hr : ‖r‖ < 1) {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    Summable (fun n : ℕ => r ^ (q * n + a)) :=
  (hasSum_geometric_residue hr hq a).summable

/-! ## Recombination: the q subseries reassemble the full series -/

/-- The algebraic heart of the recombination: `1 − r^q` factors as
`(1 − r) · (∑_{a<q} r^a)`. -/
lemma one_sub_pow_eq (r : 𝕜) (q : ℕ) :
    (1 : 𝕜) - r ^ q = (1 - r) * ∑ a ∈ Finset.range q, r ^ a := by
  rw [Finset.mul_sum]
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ]
    ring

/-- **Recombination, `tsum` form**: summing the `q` residue-class subseries over
`a = 0, …, q−1` recovers the full geometric series
`∑_{m} r^m = 1/(1 − r)`. -/
theorem tsum_residues_eq_geometric (hr : ‖r‖ < 1) {q : ℕ} (hq : q ≠ 0) :
    ∑ a ∈ Finset.range q, (∑' n : ℕ, r ^ (q * n + a)) = ∑' m : ℕ, r ^ m := by
  have hfull : ∑' m : ℕ, r ^ m = (1 - r)⁻¹ := tsum_geometric_of_norm_lt_one hr
  have hne : (1 : 𝕜) - r ≠ 0 := one_sub_ne_zero hr
  have hqne : (1 : 𝕜) - r ^ q ≠ 0 := one_sub_pow_ne_zero hr hq
  rw [hfull]
  -- replace each subseries by its closed form and factor out (1 - r^q)⁻¹
  simp_rw [tsum_geometric_residue hr hq]
  rw [← Finset.sum_mul]
  -- now: (∑_{a<q} r^a) * (1 - r^q)⁻¹ = (1 - r)⁻¹
  have hsum : (1 - r) * ∑ a ∈ Finset.range q, r ^ a = 1 - r ^ q :=
    (one_sub_pow_eq r q).symm
  field_simp [hne, hqne]
  linear_combination hsum

/-! ## Connection to the even/odd (q = 2) case -/

/-- Specialisation `q = 2, a = 0` recovers the even subseries
`∑ r^(2n) = 1/(1 − r²)` of `GeometricSeriesOQ09`. -/
theorem tsum_geometric_even (hr : ‖r‖ < 1) :
    ∑' n : ℕ, r ^ (2 * n) = (1 - r ^ 2)⁻¹ := by
  have h := tsum_geometric_residue hr (q := 2) (by norm_num) 0
  simpa using h

/-- Specialisation `q = 2, a = 1` recovers the odd subseries
`∑ r^(2n+1) = r/(1 − r²)` of `GeometricSeriesOQ09`. -/
theorem tsum_geometric_odd (hr : ‖r‖ < 1) :
    ∑' n : ℕ, r ^ (2 * n + 1) = r * (1 - r ^ 2)⁻¹ := by
  have h := tsum_geometric_residue hr (q := 2) (by norm_num) 1
  simpa using h

/-! ## Concrete values -/

/-- Sanity check at `r = 1/2`, `q = 3`, `a = 0`: `∑ (1/2)^(3n) = ∑ (1/8)ⁿ = 8/7`. -/
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ (3 * n + 0) = 8 / 7 := by
  rw [tsum_geometric_residue (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) (by norm_num) 0]
  norm_num

/-- Sanity check at `r = 1/2`, `q = 3`, `a = 2`: `∑ (1/2)^(3n+2) = 2/7`. -/
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ (3 * n + 2) = 2 / 7 := by
  rw [tsum_geometric_residue (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) (by norm_num) 2]
  norm_num

end GeometricSeriesOQ09OQ01
