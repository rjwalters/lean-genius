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

namespace Erdos1048Aristotle

open Complex Polynomial Set Metric

-- Routine: Sublevel set of |f(z)| is open (preimage of open set under continuous map)
theorem polynomial_sublevel_isOpen (f : ℂ[X]) (c : ℝ) (hc : c > 0) :
    IsOpen { z : ℂ | Complex.abs (f.eval z) < c } :=
  isOpen_lt (Complex.continuous_abs.comp (polynomial_eval_continuous f)) continuous_const

-- Routine: X^n - C a is monic for n ≥ 1
theorem xpow_sub_const_monic (a : ℂ) (n : ℕ) (hn : n ≥ 1) :
    (X ^ n - C a : ℂ[X]).leadingCoeff = 1 := by
  rw [show X ^ n - C a = X ^ n + C (-a) from by ring]
  exact Polynomial.monic_X_pow_add_C (by omega : n ≠ 0)

-- Routine: Degree of X^n - C a is n for n ≥ 1
theorem xpow_sub_const_degree (a : ℂ) (n : ℕ) (hn : n ≥ 1) :
    (X ^ n - C a : ℂ[X]).degree = n := by
  rw [show X ^ n - C a = X ^ n + C (-a) from by ring]
  exact Polynomial.degree_X_pow_add_C (by omega : n ≠ 0) (-a)

-- Routine: |r * exp(iθ)| = |r| for r : ℝ
theorem abs_mul_exp (r : ℝ) (θ : ℝ) :
    Complex.abs (r * Complex.exp (θ * Complex.I)) = |r| := by
  rw [map_mul, Complex.abs_exp_ofReal_mul_I, mul_one, Complex.abs_ofReal]

-- Routine: If z^n = r^n for r > 0, then |z| = r
theorem abs_root_of_pow_eq (z : ℂ) (r : ℝ) (n : ℕ) (hr : r > 0) (hn : n ≥ 1)
    (h : z ^ n = (r : ℂ) ^ n) : Complex.abs z = r := by
  have h_abs : Complex.abs z ^ n = r ^ n := by
    rw [← map_pow, h, map_pow, Complex.abs_ofReal, abs_of_pos hr]
  by_contra h_ne
  rcases Ne.lt_or_lt h_ne with h_lt | h_gt
  · exact absurd h_abs (ne_of_lt (pow_lt_pow_left h_lt (Complex.abs.nonneg z) (by omega)))
  · exact absurd h_abs (ne_of_gt (pow_lt_pow_left h_gt (le_of_lt hr) (by omega)))

-- Routine: Polynomial evaluation is continuous
theorem polynomial_eval_continuous (f : ℂ[X]) : Continuous f.eval :=
  Polynomial.continuous_eval

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
  · have : (2 : ℝ) < Real.sqrt 5 := by
      rw [show (2 : ℝ) = Real.sqrt 4 from (Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  · have : Real.sqrt 5 < 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 from (Real.sqrt_sq (by norm_num : (3:ℝ) ≥ 0)).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith

end Erdos1048Aristotle
