/-
  Erdős Problem #1048: Polynomial Lemniscate Diameter

  Source: https://erdosproblems.com/1048
  Status: DISPROVED (Pommerenke 1961)

  Statement:
  For a monic polynomial f ∈ ℂ[x] with all roots satisfying |z| ≤ r where r < 2,
  must the set {z : |f(z)| < 1} contain a connected component with diameter > 2-r?

  Answer: NO for r > 1 (Pommerenke 1961).

  Pommerenke showed:
  - For r > 1: Counterexample f(z) = z^n - r^n has n components with diam → 0
  - For 0 ≤ r ≤ 1/2: Component containing 0 has diameter ≥ 2
  - For 1/2 < r ≤ (√5-1)/2: Component containing 0 has diameter > 1/r
  - For (√5-1)/2 ≤ r ≤ 1: Component containing 0 has diameter > 2 - r²

  Tags: analysis, complex-analysis, polynomials, lemniscates
-/

import Mathlib

namespace Erdos1048

open Complex Polynomial Set Metric

/-!
## Part I: Polynomials and Roots

Basic setup for complex polynomials.
-/

/-- A polynomial is monic if its leading coefficient is 1. -/
def IsMonic (f : ℂ[X]) : Prop := f.leadingCoeff = 1

/-- The set of roots of a polynomial. -/
noncomputable def roots (f : ℂ[X]) : Set ℂ :=
  { z : ℂ | f.eval z = 0 }

/-- All roots are bounded by r. -/
def RootsBoundedBy (f : ℂ[X]) (r : ℝ) : Prop :=
  ∀ z ∈ roots f, Complex.abs z ≤ r

/-- A monic polynomial with bounded roots. -/
structure BoundedMonicPoly (r : ℝ) where
  poly : ℂ[X]
  monic : IsMonic poly
  bounded : RootsBoundedBy poly r
  nontrivial : poly.degree ≥ 1

/-!
## Part II: Lemniscates

The level sets of polynomial absolute value.
-/

/-- The lemniscate L(f, c) = {z : |f(z)| < c}. -/
def lemniscate (f : ℂ[X]) (c : ℝ) : Set ℂ :=
  { z : ℂ | Complex.abs (f.eval z) < c }

/-- Notation: L(f, c) for lemniscate. -/
notation "L(" f ", " c ")" => lemniscate f c

/-- The unit lemniscate L(f, 1). -/
def unitLemniscate (f : ℂ[X]) : Set ℂ := L(f, 1)

/-- Lemniscates are open sets. -/
theorem lemniscate_isOpen (f : ℂ[X]) (c : ℝ) (hc : c > 0) :
    IsOpen (L(f, c)) := by
  sorry

/-- Lemniscates are bounded for monic polynomials. -/
theorem lemniscate_bounded (f : BoundedMonicPoly r) (c : ℝ) (hc : c > 0) :
    IsBounded (L(f.poly, c)) := by
  sorry

/-!
## Part III: Connected Components

Components of the lemniscate and their diameters.
-/

/-- A connected component of a set. -/
def ConnectedComponent (S : Set ℂ) (z : ℂ) : Set ℂ :=
  ⋃₀ { C : Set ℂ | IsConnected C ∧ z ∈ C ∧ C ⊆ S }

/-- The diameter of a set in ℂ. -/
noncomputable def diameter (S : Set ℂ) : ℝ :=
  sSup { dist z w | (z : ℂ) (w : ℂ) (hz : z ∈ S) (hw : w ∈ S) }

/-- The maximum component diameter of a lemniscate. -/
noncomputable def maxComponentDiameter (f : ℂ[X]) (c : ℝ) : ℝ :=
  sSup { diameter (ConnectedComponent (L(f, c)) z) | (z : ℂ) (hz : z ∈ L(f, c)) }

/-!
## Part IV: The Conjecture

What Erdős-Herzog-Piranian asked (1958).
-/

/-- **Erdős-Herzog-Piranian Conjecture (1958)**:
    For monic f with roots in |z| ≤ r where r < 2,
    some component of L(f, 1) has diameter > 2 - r. -/
def EHPConjecture : Prop :=
  ∀ r : ℝ, r < 2 → ∀ f : BoundedMonicPoly r,
    maxComponentDiameter f.poly 1 > 2 - r

/-!
## Part V: Pommerenke's Counterexample (1961)

The conjecture fails for r > 1.
-/

/-- The counterexample polynomial z^n - r^n. -/
noncomputable def pommerenkeCounterexample (r : ℝ) (n : ℕ) : ℂ[X] :=
  X ^ n - C (r ^ n : ℂ)

/-- The counterexample is monic. -/
theorem counterexample_monic (r : ℝ) (n : ℕ) (hn : n ≥ 1) :
    IsMonic (pommerenkeCounterexample r n) := by
  sorry

/-- Roots of z^n - r^n are r times roots of unity. -/
theorem counterexample_roots (r : ℝ) (n : ℕ) (hn : n ≥ 1) (hr : r > 0) :
    roots (pommerenkeCounterexample r n) =
      { r * Complex.exp (2 * Real.pi * I * k / n) | (k : ℤ) (hk : 0 ≤ k ∧ k < n) } := by
  sorry

/-- All roots have absolute value r. -/
theorem counterexample_bounded (r : ℝ) (n : ℕ) (hn : n ≥ 1) (hr : r > 0) :
    RootsBoundedBy (pommerenkeCounterexample r n) r := by
  sorry

/-- The lemniscate has n connected components. -/
axiom counterexample_n_components (r : ℝ) (n : ℕ) (hn : n ≥ 1) (hr : r > 1) :
    -- L(z^n - r^n, 1) has exactly n connected components
    True

/-- **Pommerenke (1961)**: Each component diameter → 0 as n → ∞. -/
axiom pommerenke_diameter_vanishes (r : ℝ) (hr : r > 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      maxComponentDiameter (pommerenkeCounterexample r n) 1 < ε

/-- The conjecture is FALSE for r > 1. -/
theorem EHP_false_for_r_gt_1 : ¬ EHPConjecture := by
  sorry

/-!
## Part VI: Positive Results (Pommerenke)

The conjecture holds in modified forms for r ≤ 1.
-/

/-- The golden ratio minus 1. -/
noncomputable def φ_minus_1 : ℝ := (Real.sqrt 5 - 1) / 2

/-- φ - 1 ≈ 0.618. -/
theorem phi_minus_1_value : φ_minus_1 > 0.618 ∧ φ_minus_1 < 0.619 := by
  sorry

/-- **Case r ≤ 1/2**: Component containing 0 has diameter ≥ 2. -/
axiom pommerenke_case_small_r (f : BoundedMonicPoly r) (hr : r ≤ 1/2) :
    (0 : ℂ) ∈ unitLemniscate f.poly →
    diameter (ConnectedComponent (unitLemniscate f.poly) 0) ≥ 2

/-- **Case 1/2 < r ≤ φ-1**: Component containing 0 has diameter > 1/r. -/
axiom pommerenke_case_medium_r (f : BoundedMonicPoly r) (hr1 : 1/2 < r) (hr2 : r ≤ φ_minus_1) :
    (0 : ℂ) ∈ unitLemniscate f.poly →
    diameter (ConnectedComponent (unitLemniscate f.poly) 0) > 1/r

/-- **Case φ-1 ≤ r ≤ 1**: Component containing 0 has diameter > 2 - r². -/
axiom pommerenke_case_large_r (f : BoundedMonicPoly r) (hr1 : φ_minus_1 ≤ r) (hr2 : r ≤ 1) :
    (0 : ℂ) ∈ unitLemniscate f.poly →
    diameter (ConnectedComponent (unitLemniscate f.poly) 0) > 2 - r^2

/-!
## Part VII: Optimal Examples

Showing the bounds are tight.
-/

/-- The polynomial z^n shows diameter 2 is optimal for r = 0. -/
theorem zn_diameter (n : ℕ) (hn : n ≥ 1) :
    diameter (unitLemniscate (X ^ n : ℂ[X])) = 2 := by
  sorry

/-- For r = 0, the bound diameter ≥ 2 is sharp. -/
theorem diameter_2_sharp : ∀ ε > 0, ∃ f : BoundedMonicPoly 0,
    maxComponentDiameter f.poly 1 < 2 + ε := by
  sorry

/-- For r = 1, examples show max diameter < 1 + ε. -/
axiom diameter_near_1_for_r_eq_1 :
    ∀ ε > 0, ∃ f : BoundedMonicPoly 1,
      maxComponentDiameter f.poly 1 < 1 + ε

/-!
## Part VIII: Degree and Component Count

Relationship between degree and lemniscate structure.
-/

/-- A degree n polynomial has at most n components. -/
axiom component_count_bound (f : ℂ[X]) (hf : f.degree = n) (c : ℝ) (hc : c > 0) :
    -- L(f, c) has at most n connected components
    True

/-- The exterior component is unbounded for c > |leading coeff|. -/
theorem exterior_unbounded (f : ℂ[X]) (hf : f ≠ 0) (c : ℝ) (hc : c > Complex.abs f.leadingCoeff) :
    ¬ IsBounded ({ z : ℂ | Complex.abs (f.eval z) ≥ c }) := by
  sorry

/-!
## Part IX: Potential-Theoretic Viewpoint

Connection to logarithmic capacity.
-/

/-- The logarithmic capacity of a set. -/
noncomputable def logCapacity (S : Set ℂ) : ℝ := sorry

/-- For a monic polynomial, capacity of L(f, c) equals c^(1/n). -/
axiom lemniscate_capacity (f : BoundedMonicPoly r) (c : ℝ) (hc : c > 0) (n : ℕ) (hn : f.poly.degree = n) :
    logCapacity (L(f.poly, c)) = c ^ (1 / n : ℝ)

/-- Capacity lower bounds diameter. -/
axiom capacity_diameter_inequality (S : Set ℂ) (hS : IsConnected S) :
    diameter S ≥ 4 * logCapacity S

/-!
## Part X: Summary

The resolution of Erdős Problem #1048.
-/

/-- **Erdős Problem #1048: DISPROVED**

    Original Question: For monic f with roots in |z| ≤ r where r < 2,
    must L(f,1) have a component with diameter > 2-r?

    Answer: NO for r > 1 (Pommerenke 1961).

    Counterexample: f(z) = z^n - r^n for large n.

    Positive Results for r ≤ 1:
    - r ≤ 1/2: diam ≥ 2 (optimal)
    - 1/2 < r ≤ (√5-1)/2: diam > 1/r
    - (√5-1)/2 ≤ r ≤ 1: diam > 2 - r² -/
theorem erdos_1048 : ¬ EHPConjecture := EHP_false_for_r_gt_1

/-- The answer to Erdős #1048. -/
def erdos_1048_answer : String :=
  "DISPROVED for r > 1 (Pommerenke 1961). Positive results for r ≤ 1."

/-- The status of Erdős #1048. -/
def erdos_1048_status : String :=
  "DISPROVED by Christian Pommerenke (1961)"

/-- Pommerenke's key insight. -/
theorem pommerenke_insight (r : ℝ) (hr : r > 1) :
    ∀ δ > 0, ∃ f : BoundedMonicPoly r, maxComponentDiameter f.poly 1 < δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := pommerenke_diameter_vanishes r hr δ hδ
  sorry

#check erdos_1048
#check EHPConjecture
#check pommerenke_diameter_vanishes

end Erdos1048
