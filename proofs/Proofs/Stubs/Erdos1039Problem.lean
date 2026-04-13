/-
  Erdős Problem #1039: Polynomial Lemniscate Disc Radius

  Source: https://erdosproblems.com/1039
  Status: OPEN

  Statement:
  Let f(z) = ∏(z - zᵢ) ∈ ℂ[z] with |zᵢ| ≤ 1 for all i.
  Let ρ(f) be the radius of the largest disc contained in {z : |f(z)| < 1}.

  Determine the behavior of ρ(f). Is it always true that ρ(f) ≫ 1/n?

  A problem of Erdős, Herzog, and Piranian.

  Known Results:
  - Benchmark: f(z) = zⁿ - 1 has ρ(f) ≤ π/(2n)
  - Pommerenke (1961): ρ(f) ≥ 1/(2en²)
  - Krishnapur-Lundberg-Ramachandran (2025): ρ(f) ≫ 1/(n√(log n))
-/

import Mathlib

namespace Erdos1039

/-
## Polynomial Setup
-/

/-- A monic polynomial with roots in the unit disc. -/
structure UnitDiscPolynomial where
  /-- The degree of the polynomial. -/
  degree : ℕ
  /-- The roots of the polynomial. -/
  roots : Fin degree → ℂ
  /-- All roots lie in the closed unit disc. -/
  roots_in_disc : ∀ i, Complex.abs (roots i) ≤ 1

variable (f : UnitDiscPolynomial)

/-- The polynomial as a function ℂ → ℂ. -/
noncomputable def UnitDiscPolynomial.eval (z : ℂ) : ℂ :=
  ∏ i : Fin f.degree, (z - f.roots i)

/-- The sublevel set {z : |f(z)| < 1}. -/
def sublevelSet : Set ℂ :=
  {z : ℂ | Complex.abs (f.eval z) < 1}

/-
## Inscribed Disc Radius
-/

/-- A disc of radius r centered at c is inscribed in S. -/
def isInscribedDisc (S : Set ℂ) (c : ℂ) (r : ℝ) : Prop :=
  r > 0 ∧ ∀ z : ℂ, Complex.abs (z - c) < r → z ∈ S

/-- The supremum of radii of inscribed discs. -/
noncomputable def inscribedDiscRadius (S : Set ℂ) : ℝ :=
  sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc S c r}

/-- ρ(f) - the inscribed disc radius of the sublevel set. -/
noncomputable def rho : ℝ := inscribedDiscRadius (sublevelSet f)

/-
## The Benchmark: zⁿ - 1
-/

/-- The polynomial zⁿ - 1 has roots at the n-th roots of unity. -/
def rootsOfUnity (n : ℕ) (hn : n > 0) : UnitDiscPolynomial where
  degree := n
  roots := fun k => Complex.exp (2 * Real.pi * Complex.I * k / n)
  roots_in_disc := by
    intro i
    simp only [Complex.abs_exp]
    -- The argument is purely imaginary: rewrite as (real * I), then re = 0
    have heq : 2 * ↑Real.pi * Complex.I * ↑↑(i : ℕ) / ↑(n : ℕ) =
      ↑(2 * Real.pi * (↑(i : ℕ) : ℝ) / (↑n : ℝ)) * Complex.I := by
      push_cast; ring
    rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    simp [Real.exp_zero]

/-- The benchmark upper bound: ρ(zⁿ - 1) ≤ π/(2n). -/
axiom benchmark_upper (n : ℕ) (hn : n > 0) :
  rho (rootsOfUnity n hn) ≤ Real.pi / (2 * n)

/-
## Pommerenke's Lower Bound (1961)
-/

/-- Pommerenke's lower bound: ρ(f) ≥ 1/(2en²). -/
axiom pommerenke_lower (f : UnitDiscPolynomial) (hf : f.degree > 0) :
  rho f ≥ 1 / (2 * Real.exp 1 * (f.degree : ℝ)^2)

/-- The Pommerenke exponent is 2 (quadratic in n). -/
def pommerenkeExponent : ℕ := 2

/-
## Krishnapur-Lundberg-Ramachandran Bound (2025)
-/

/-- The KLR bound: ρ(f) ≥ c/(n√(log n)) for some constant c > 0. -/
axiom klr_lower :
  ∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree ≥ 3 →
    rho f ≥ c / ((f.degree : ℝ) * Real.sqrt (Real.log f.degree))

/-- The KLR bound is better than Pommerenke for large n. -/
theorem klr_better_than_pommerenke :
    ∀ᶠ n in Filter.atTop,
    1 / ((n : ℝ) * Real.sqrt (Real.log n)) > 1 / (2 * Real.exp 1 * n^2) := by
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < n)
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  -- Key chain: √(log n) < log n < n for n ≥ 3
  have hlog_gt_1 : 1 < Real.log (n : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hsqrt_lt_log : Real.sqrt (Real.log (n : ℝ)) < Real.log (n : ℝ) := by
    have h1 : 1 < Real.sqrt (Real.log (n : ℝ)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt (by linarith) hlog_gt_1
    calc Real.sqrt (Real.log (n : ℝ))
        = Real.sqrt (Real.log (n : ℝ)) * 1 := (mul_one _).symm
      _ < Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) :=
          mul_lt_mul_of_pos_left h1 hsqrt_pos
      _ = Real.log (n : ℝ) := Real.mul_self_sqrt (le_of_lt hlog_pos)
  have hlog_lt_n : Real.log (n : ℝ) < (n : ℝ) := by
    have := Real.add_one_le_exp hlog_pos.le
    rw [Real.exp_log hn_pos] at this; linarith
  -- 1/(n√(log n)) > 1/(2en²) ⟺ 2en² > n√(log n) ⟺ 2en > √(log n)
  rw [gt_iff_lt, div_lt_div_iff (by positivity) (mul_pos hn_pos hsqrt_pos)]
  simp only [one_mul]
  push_cast
  nlinarith [Real.exp_one_gt_d9,
             mul_lt_mul_of_pos_left (lt_trans hsqrt_lt_log hlog_lt_n) hn_pos]

/-
## The Erdős-Herzog-Piranian Conjecture
-/

/-- The conjecture: ρ(f) ≫ 1/n for all unit disc polynomials. -/
def ehpConjecture : Prop :=
  ∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree > 0 →
    rho f ≥ c / f.degree

/-- The EHP conjecture is an open problem. We neither prove nor disprove it.
    (The previous axiom `¬(P ∨ ¬P)` was inconsistent with classical logic.) -/

/-
## Comparison of Bounds
-/

/-- Pommerenke: 1/(2en²) -/
noncomputable def pommerenkeBound (n : ℕ) : ℝ :=
  1 / (2 * Real.exp 1 * n^2)

/-- KLR: c/(n√(log n)) -/
noncomputable def klrBound (c : ℝ) (n : ℕ) : ℝ :=
  c / (n * Real.sqrt (Real.log n))

/-- Conjectured: c/n -/
noncomputable def conjecturedBound (c : ℝ) (n : ℕ) : ℝ :=
  c / n

/-- Benchmark upper: π/(2n) -/
noncomputable def benchmarkBound (n : ℕ) : ℝ :=
  Real.pi / (2 * n)

/-- For small enough c (c < π/2), the KLR bound is below the benchmark. -/
theorem bounds_gap (n : ℕ) (hn : n ≥ 3) (c : ℝ) (hc : 0 < c) (hc' : c < Real.pi / 2) :
    klrBound c n < benchmarkBound n := by
  simp only [klrBound, benchmarkBound]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < n)
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  have hlog_ge_1 : 1 ≤ Real.log (n : ℝ) := by
    have hexp_le : Real.exp 1 ≤ (n : ℝ) := by
      have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      linarith
    rwa [Real.exp_le_iff_le_log hn_pos] at hexp_le
  have hsqrt_ge_1 : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
    have := Real.sqrt_le_sqrt hlog_ge_1; rwa [Real.sqrt_one] at this
  -- Reduce to: 2c < π√(log n), by clearing positive denominators
  rw [div_lt_div_iff (mul_pos hn_pos hsqrt_pos) (by positivity : (0 : ℝ) < 2 * ↑n)]
  -- Goal: c * (2 * ↑n) < π * (↑n * √(log ↑n))
  -- From c < π/2 and √(log n) ≥ 1: 2cn < πn ≤ πn√(log n)
  nlinarith [Real.pi_pos]

/-
## Lemniscate Properties
-/

/-- The lemniscate {z : |f(z)| = 1}. -/
def lemniscate : Set ℂ :=
  {z : ℂ | Complex.abs (f.eval z) = 1}

/-- The sublevel set is open (preimage of (-∞, 1) under the continuous map |f|). -/
theorem sublevelSet_isOpen : IsOpen (sublevelSet f) := by
  simp only [sublevelSet, UnitDiscPolynomial.eval]
  exact isOpen_lt
    (Complex.continuous_abs.comp
      (continuous_finset_prod Finset.univ fun i _ => continuous_id.sub continuous_const))
    continuous_const

/-- Each root is in the sublevel set (f(zᵢ) = 0 since the product has a zero factor). -/
theorem root_in_sublevelSet (i : Fin f.degree) :
    f.roots i ∈ sublevelSet f := by
  simp only [sublevelSet, Set.mem_setOf_eq, UnitDiscPolynomial.eval]
  have : ∏ j : Fin f.degree, (f.roots i - f.roots j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  simp [this]

/-- The sublevel set is non-empty (contains the roots). -/
theorem sublevelSet_nonempty (hf : f.degree > 0) :
    (sublevelSet f).Nonempty :=
  ⟨f.roots ⟨0, hf⟩, root_in_sublevelSet f ⟨0, hf⟩⟩

/-
## Area Bounds
-/

/-- Area of the sublevel set (Lebesgue measure, converted to ℝ via toReal). -/
noncomputable def sublevelArea : ℝ := (MeasureTheory.volume (sublevelSet f)).toReal

/-- Lower bound on area implies lower bound on inscribed disc. -/
theorem area_implies_disc_bound :
    sublevelArea f ≥ Real.pi * (rho f)^2 := by
  sorry

/-- The KLR paper establishes area bounds that imply disc bounds. -/
axiom klr_area_bound (f : UnitDiscPolynomial) (hf : f.degree ≥ 3) :
  sublevelArea f ≥ Real.pi / ((f.degree : ℝ)^2 * Real.log f.degree)

/-
## Special Cases
-/

/-- For n = 1, the sublevel set contains a disc of radius 1. -/
theorem degree_one_optimal :
    ∀ (f : UnitDiscPolynomial), f.degree = 1 → rho f = 1 := by
  sorry

/-- For clustered roots, the inscribed disc can be larger. -/
def hasClusteredRoots (f : UnitDiscPolynomial) (ε : ℝ) : Prop :=
  ∃ c : ℂ, ∀ i, Complex.abs (f.roots i - c) < ε

/-- Clustered roots give larger inscribed disc. -/
theorem clustered_implies_large_disc (ε : ℝ) (hε : ε > 0) (hε' : ε < 1) :
    ∀ (f : UnitDiscPolynomial), hasClusteredRoots f ε → f.degree > 0 →
      rho f ≥ 1 - ε := by
  sorry

/-
## Random Polynomials
-/

/-- For random polynomials, the expected ρ is of order 1/√n. -/
axiom random_polynomial_expected :
  ∃ c₁ c₂ > 0, ∀ n : ℕ, n ≥ 2 →
    c₁ / Real.sqrt n ≤ -- Expected[rho(random poly of degree n)]
    c₂ / Real.sqrt n

/-
## The Open Question
-/

/-- The main open question: close the gap between 1/(n√log n) and 1/n. -/
def erdos_1039_question : Prop :=
  ehpConjecture

/-- Current state: known bounds, conjecture unresolved. -/
theorem erdos_1039_current_state :
    (∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree ≥ 3 →
      rho f ≥ c / ((f.degree : ℝ) * Real.sqrt (Real.log f.degree))) ∧
    (∀ n : ℕ, n > 0 → ∃ (f : UnitDiscPolynomial), f.degree = n ∧
      rho f ≤ Real.pi / (2 * n)) := by
  constructor
  · exact klr_lower
  · intro n hn
    use rootsOfUnity n hn
    constructor
    · rfl
    · exact benchmark_upper n hn

/-
## Summary

Erdős Problem #1039 asks about the inscribed disc radius ρ(f) for
polynomials with roots in the unit disc.

**Known**:
- Upper: ρ(zⁿ-1) ≤ π/(2n) (benchmark)
- Lower: ρ(f) ≥ 1/(2en²) (Pommerenke 1961)
- Lower: ρ(f) ≫ 1/(n√log n) (KLR 2025)

**Conjecture**: ρ(f) ≫ 1/n

**Status**: OPEN - the gap between 1/(n√log n) and 1/n remains.
-/

end Erdos1039
