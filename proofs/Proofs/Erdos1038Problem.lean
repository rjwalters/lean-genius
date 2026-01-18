/-
Erdős Problem #1038: Sublevel Sets of Monic Polynomials

Determine the infimum and supremum of |{x ∈ ℝ : |f(x)| < 1}| as f ranges over all
non-constant monic polynomials whose roots are all real and contained in [-1,1].

**Answer**:
  - Supremum = 2√2 ≈ 2.828 (proved by Tao, 2025)
  - Infimum: 2^(4/3) - 1 ≈ 1.519 ≤ inf ≤ 1.835 (bounds known, exact value open)

This problem was posed by Erdős, Herzog, and Piranian in 1958. They proved the
supremum bound under the restriction that roots lie in {-1, 1}, conjecturing it
is optimal for roots in [-1, 1]. Terence Tao confirmed this in December 2025.

References:
  - https://erdosproblems.com/1038
  - Erdős, Herzog, Piranian. Metric properties of polynomials. J. Analyse Math. (1958)
  - Tao. Sublevel Sets of Logarithmic Potentials. Terry Tao's Blog (Dec 2025)
-/

import Mathlib

open scoped Real ENNReal
open MeasureTheory Polynomial

namespace Erdos1038

/-!
## Definitions

We study the Lebesgue measure of the sublevel set {x ∈ ℝ : |f(x)| < 1} for monic
polynomials with real roots in [-1, 1].
-/

/-- A monic polynomial with all roots real and in [-1, 1]. -/
def MonicRealRootedIn01 (f : Polynomial ℝ) : Prop :=
  f.Monic ∧ (∀ r ∈ f.roots, r ∈ Set.Icc (-1 : ℝ) 1)

/-- The sublevel set {x ∈ ℝ : |f(x)| < 1}. -/
def sublevelSet (f : Polynomial ℝ) : Set ℝ :=
  {x | |f.eval x| < 1}

/-- Measure of the sublevel set. -/
noncomputable def sublevelMeasure (f : Polynomial ℝ) : ℝ≥0∞ :=
  volume (sublevelSet f)

/-!
## Supremum Result

The supremum equals 2√2, achieved in the limit by polynomials approaching
(x - 1)(x + 1). This was conjectured by Erdős-Herzog-Piranian (1958) and
proved by Terence Tao in December 2025.
-/

/-- The supremum of sublevel set measures for monic polynomials with roots in [-1,1]
    equals 2√2 ≈ 2.828. Proved by Tao (2025). -/
axiom erdos_1038_supremum :
    (⨆ f : {f : Polynomial ℝ // f.Monic ∧
      (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
      volume {x | |f.1.eval x| < 1}) = 2 * Real.sqrt 2
-- Proof requires potential theory and analysis beyond current Mathlib.
-- See: Tao, "Sublevel Sets of Logarithmic Potentials" (2025)

/-!
## Infimum Bounds

The exact infimum remains an open problem. Current best bounds:
  - Lower bound: 2^(4/3) - 1 ≈ 1.519
  - Upper bound: 1.835 (witnessed by specific polynomial constructions)
-/

/-- Lower bound on the infimum: at least 2^(4/3) - 1 ≈ 1.519. -/
axiom erdos_1038_inf_lowerBound :
    2 ^ (4 / 3 : ℝ) - 1 ≤
      ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
        (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
        volume {x | |f.1.eval x| < 1}
-- Proof uses logarithmic potential theory

/-- Upper bound on the infimum: less than 1.835. -/
axiom erdos_1038_inf_upperBound :
    ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
      (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
      volume {x | |f.1.eval x| < 1} < 1.835
-- Witnessed by explicit polynomial constructions

/-!
## Concrete Examples

Erdős-Herzog-Piranian noted that specific polynomials give small sublevel sets.
-/

/-- The polynomial (x+1)(x-1)^m for m ≥ 3 witnesses that the infimum is < 2.
    This is explicitly noted in the original 1958 paper. -/
theorem infimum_less_than_two :
    ∃ f : Polynomial ℝ, f.Monic ∧ f ≠ 1 ∧
      (∀ r ∈ f.roots, r ∈ Set.Icc (-1 : ℝ) 1) ∧
      volume {x | |f.eval x| < 1} < 2 := by
  -- The polynomial (x+1)(x-1)³ = x⁴ - 2x³ + 2x - 1 witnesses this
  use (X + 1) * (X - 1) ^ 3
  constructor
  · -- Monic
    apply Polynomial.Monic.mul
    · exact monic_X_add_C 1
    · exact (monic_X_sub_C 1).pow 3
  constructor
  · -- Not equal to 1
    intro h
    have : ((X : Polynomial ℝ) + 1).natDegree = 0 := by
      calc ((X : Polynomial ℝ) + 1).natDegree
          ≤ ((X + 1) * (X - 1) ^ 3).natDegree := Polynomial.natDegree_le_of_dvd (dvd_mul_right _ _) (by simp [h])
        _ = (1 : Polynomial ℝ).natDegree := by rw [h]
        _ = 0 := Polynomial.natDegree_one
    simp at this
  constructor
  · -- All roots in [-1, 1]
    intro r hr
    simp only [Polynomial.roots_mul, Polynomial.roots_pow, Multiset.mem_add,
      Multiset.mem_nsmul] at hr
    · rcases hr with hr | ⟨_, hr⟩
      · simp only [roots_X_add_C, Multiset.mem_singleton] at hr
        simp [hr]
      · simp only [roots_X_sub_C, Multiset.mem_singleton] at hr
        simp [hr]
    · simp
    · exact pow_ne_zero 3 (X_sub_C_ne_zero 1)
  · -- Measure < 2 (this requires numerical computation)
    sorry -- Numerical analysis beyond Mathlib automation

/-- The quadratic polynomial (x-1)(x+1) = x² - 1 has sublevel measure approaching 2√2
    as coefficients are perturbed. The exact value for x² - 1 itself is 2√2. -/
theorem quadratic_example :
    volume {x : ℝ | |x^2 - 1| < 1} = 2 * Real.sqrt 2 := by
  -- The set is {x : -1 < x² - 1 < 1} = {x : 0 < x² < 2}
  -- which equals (-√2, -0) ∪ (0, √2) with measure 2√2
  sorry -- Requires interval measure computation

/-!
## Historical Context

This problem connects to several areas:
1. **Potential theory**: The measure relates to logarithmic capacity
2. **Chebyshev polynomials**: Optimal approximation theory
3. **Random matrix theory**: Spectral measure connections
-/

end Erdos1038
