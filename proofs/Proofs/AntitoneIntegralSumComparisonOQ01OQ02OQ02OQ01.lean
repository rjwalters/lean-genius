/-
  Antitone integral–sum comparison — OQ-01-OQ-02-OQ-02-OQ-01:
  identifying the generalized Euler constant of `1/x` with the Euler–Mascheroni constant `γ`.

  The parent thread (`AntitoneIntegralSumComparisonOQ01OQ02OQ02`) builds, for an antitone
  nonnegative summand `f` on `[1, ∞)`, the **generalized Euler constant**

      `generalizedEuler f := ⨆ n, defect f n`,   `defect f n := ∑_{i<n} f(1+i) − ∫₁^{1+n} f`,

  and proves its abstract properties: the defect is monotone, bounded by `f 1`, and converges
  to `generalizedEuler f` (`tendsto_defect`). That is a *gap constant* attached to any such `f`,
  with no claim about its value. This file pins the value in the archetypal case `f = 1/x`:

      `generalizedEuler (fun x => 1/x) = Real.eulerMascheroniConstant`.

  The identification is exact and 0-axiom. For `f = 1/x` the defect is, term for term,
  Mathlib's Euler–Mascheroni sequence:

      `defect (1/·) n = ∑_{i<n} 1/(1+i) − ∫₁^{1+n} 1/x = harmonic n − log (n+1)`,

  using `harmonic n = ∑_{i<n} (i+1)⁻¹` and `∫₁^{1+n} x⁻¹ = log((1+n)/1) = log(n+1)`
  (`integral_one_div_of_pos`). Both `defect (1/·)` (via the parent's `tendsto_defect`) and
  `n ↦ harmonic n − log (n+1)` (via Mathlib's `Real.tendsto_harmonic_sub_log_add_one`) converge,
  the latter to `γ`; since they are the *same* sequence, uniqueness of limits
  (`tendsto_nhds_unique`) forces `generalizedEuler (1/·) = γ`.

  This turns the parent's abstract enclosure `generalizedEuler (1/·) ∈ [0, 1]` into the sharp
  value `γ ≈ 0.5772…`, and connects the bespoke gap-constant construction to Mathlib's canonical
  Euler–Mascheroni development.

  All results are fully machine-checked (0 axioms, 0 sorries).
-/

import Mathlib
import Proofs.AntitoneIntegralSumComparisonOQ01OQ02OQ02

namespace AntitoneIntegralSumComparisonOQ01OQ02OQ02OQ01

open Finset Filter Topology MeasureTheory intervalIntegral Real

/-- `fun x => 1/x` is antitone on `[1, ∞)` (indeed on the positive reals). -/
theorem antitoneOn_one_div : AntitoneOn (fun x => 1 / x) (Set.Ici (1 : ℝ)) := by
  intro a ha b _ hab
  simp only [Set.mem_Ici] at ha
  exact one_div_le_one_div_of_le (by linarith) hab

/-- `fun x => 1/x` is nonnegative on `[1, ∞)`. -/
theorem one_div_nonneg_on (x : ℝ) (hx : (1 : ℝ) ≤ x) : 0 ≤ (fun x => 1 / x) x := by
  simp only
  positivity

/-- **The `1/x` defect is exactly the Euler–Mascheroni sequence.**  Term for term,
`defect (1/·) n = harmonic n − log (n+1)`: the Riemann sum `∑_{i<n} 1/(1+i)` is `harmonic n`,
and the integral `∫₁^{1+n} 1/x` is `log (n+1)`. -/
theorem defect_one_div_eq (n : ℕ) :
    AntitoneIntegralSumComparisonOQ01OQ02OQ02.defect (fun x => 1 / x) n
      = (harmonic n : ℝ) - Real.log ((n : ℝ) + 1) := by
  simp only [AntitoneIntegralSumComparisonOQ01OQ02OQ02.defect]
  have hsum : ∑ i ∈ Finset.range n, 1 / (1 + (i : ℝ)) = (harmonic n : ℝ) := by
    rw [harmonic]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_div, add_comm]
  have hint : (∫ x in (1 : ℝ)..(1 + (n : ℝ)), 1 / x) = Real.log ((n : ℝ) + 1) := by
    rw [integral_one_div_of_pos (by norm_num) (by positivity), div_one, add_comm]
  rw [hsum, hint]

/-- **Main identification.**  The generalized Euler constant of the harmonic summand `1/x`
equals the Euler–Mascheroni constant `γ`.

`defect (1/·)` converges to `generalizedEuler (1/·)` (parent `tendsto_defect`, from antitonicity
and nonnegativity), and — being termwise equal to `harmonic n − log (n+1)` — it also converges
to `γ` (`Real.tendsto_harmonic_sub_log_add_one`).  Uniqueness of limits identifies the two. -/
theorem generalizedEuler_one_div_eq_eulerMascheroniConstant :
    AntitoneIntegralSumComparisonOQ01OQ02OQ02.generalizedEuler (fun x => 1 / x)
      = Real.eulerMascheroniConstant := by
  have h1 := AntitoneIntegralSumComparisonOQ01OQ02OQ02.tendsto_defect
    antitoneOn_one_div one_div_nonneg_on
  rw [show AntitoneIntegralSumComparisonOQ01OQ02OQ02.defect (fun x => 1 / x)
        = (fun n => (harmonic n : ℝ) - Real.log ((n : ℝ) + 1)) from funext defect_one_div_eq] at h1
  exact tendsto_nhds_unique h1 Real.tendsto_harmonic_sub_log_add_one

/-- **Sharp enclosure, as a corollary.**  The parent's abstract bound
`generalizedEuler (1/·) ∈ [0, 1]` (`f 1 = 1`) is now pinned to the value `γ ∈ (1/2, 2/3)`. -/
theorem generalizedEuler_one_div_mem_Ioo :
    AntitoneIntegralSumComparisonOQ01OQ02OQ02.generalizedEuler (fun x => 1 / x)
      ∈ Set.Ioo (1 / 2 : ℝ) (2 / 3) := by
  rw [generalizedEuler_one_div_eq_eulerMascheroniConstant]
  exact ⟨Real.one_half_lt_eulerMascheroniConstant, Real.eulerMascheroniConstant_lt_two_thirds⟩

end AntitoneIntegralSumComparisonOQ01OQ02OQ02OQ01

#print axioms
  AntitoneIntegralSumComparisonOQ01OQ02OQ02OQ01.generalizedEuler_one_div_eq_eulerMascheroniConstant
#print axioms AntitoneIntegralSumComparisonOQ01OQ02OQ02OQ01.generalizedEuler_one_div_mem_Ioo
