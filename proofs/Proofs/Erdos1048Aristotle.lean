/-
  Aristotle targets for Erdős Problem #1048
  Routine supporting lemmas for automated proof search.
  See Erdos1048Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjecture (EHP disproved) or deep counterexample analysis
  - Routine complex analysis facts: continuity, openness, polynomial properties
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

/-- v4.31 migration compat: `Complex.abs` was removed from Mathlib in favor of `‖·‖`. -/
noncomputable def Complex.abs (z : ℂ) : ℝ := ‖z‖

namespace Erdos1048Aristotle

open Complex Polynomial Set Metric

-- Routine: Polynomial evaluation is continuous
theorem polynomial_eval_continuous (f : ℂ[X]) : Continuous f.eval :=
  Polynomial.continuous f

-- Routine: Sublevel set of |f(z)| is open (preimage of open set under continuous map)
theorem polynomial_sublevel_isOpen (f : ℂ[X]) (c : ℝ) (hc : c > 0) :
    IsOpen { z : ℂ | Complex.abs (f.eval z) < c } :=
  isOpen_lt (continuous_norm.comp (polynomial_eval_continuous f)) continuous_const

-- Routine: X^n - C a is monic for n ≥ 1
theorem xpow_sub_const_monic (a : ℂ) (n : ℕ) (hn : n ≥ 1) :
    (X ^ n - C a : ℂ[X]).leadingCoeff = 1 :=
  Polynomial.monic_X_pow_sub_C a (by omega : n ≠ 0)

-- Routine: Degree of X^n - C a is n for n ≥ 1
theorem xpow_sub_const_degree (a : ℂ) (n : ℕ) (hn : n ≥ 1) :
    (X ^ n - C a : ℂ[X]).degree = n :=
  Polynomial.degree_X_pow_sub_C hn a

-- Routine: |r * exp(iθ)| = |r| for r : ℝ
theorem abs_mul_exp (r : ℝ) (θ : ℝ) :
    Complex.abs (r * Complex.exp (θ * Complex.I)) = |r| := by
  show ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = |r|
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

-- Routine: If z^n = r^n for r > 0, then |z| = r
theorem abs_root_of_pow_eq (z : ℂ) (r : ℝ) (n : ℕ) (hr : r > 0) (hn : n ≥ 1)
    (h : z ^ n = (r : ℂ) ^ n) : Complex.abs z = r := by
  have h_abs : Complex.abs z ^ n = r ^ n := by
    show ‖z‖ ^ n = r ^ n
    rw [← norm_pow, h, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · exact absurd h_abs (ne_of_lt (pow_lt_pow_left₀ h_lt (norm_nonneg z) (by omega)))
  · exact absurd h_abs (ne_of_gt (pow_lt_pow_left₀ h_gt (le_of_lt hr) (by omega)))

-- Routine: The golden ratio satisfies φ² = φ + 1
-- Proof: ((√5+1)/2)² = (5+2√5+1)/4 = (6+2√5)/4 = (3+√5)/2 = (√5+1)/2 + 1
theorem golden_ratio_sq :
    let φ := (Real.sqrt 5 + 1) / 2
    φ ^ 2 = φ + 1 := by
  simp only
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  ring_nf
  nlinarith [hsq]

-- Routine: (√5 - 1)/2 is positive and less than 1
-- √5 > 2 (since 5 > 4) gives > 0; √5 < 3 (since 5 < 9) gives < 1
theorem golden_minus_one_bounds :
    (Real.sqrt 5 - 1) / 2 > 0 ∧ (Real.sqrt 5 - 1) / 2 < 1 := by
  constructor
  · have : (2 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith
  · have : Real.sqrt 5 < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith

end Erdos1048Aristotle
