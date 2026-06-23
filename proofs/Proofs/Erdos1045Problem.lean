/-
  Erdős Problem #1045: Maximum Product of Distances

  Source: https://erdosproblems.com/1045
  Status: OPEN (partially resolved)

  Statement:
  Let z₁,...,zₙ ∈ ℂ with |zᵢ - zⱼ| ≤ 2 for all i,j. Define
  Δ(z₁,...,zₙ) = ∏_{i≠j} |zᵢ - zⱼ|.
  What is the maximum possible value of Δ?
  Is it maximized when the zᵢ are vertices of a regular polygon?

  Answer:
  - Regular polygon is NOT optimal for even n ≥ 4 (Hu-Tang, Cambie)
  - For even n: liminf(max Δ/n^n) ≥ C ≈ 1.304 (Cambie-Dong-Tang)
  - Regular polygon may still be optimal for odd n (open)

  References:
  - Erdős-Herzog-Piranian (1958), Pommerenke (1961)
  - Hu-Tang (counterexamples), Cambie (generalization)
  - Sothanaphan (2025), Cambie-Dong-Tang (2025)

  Tags: complex-analysis, optimization, polynomial, geometry
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos1045

open Complex Real

/- ## Part I: Basic Definitions -/

/-- A configuration of n complex points -/
def Configuration (n : ℕ) := Fin n → ℂ

/-- The diameter constraint: all pairwise distances are at most 2 -/
def DiameterAtMost2 (z : Configuration n) : Prop :=
  ∀ i j : Fin n, Complex.abs (z i - z j) ≤ 2

/-- The product of pairwise distances Δ(z₁,...,zₙ) over all ordered pairs -/
noncomputable def Delta (z : Configuration n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i ≠ j then Complex.abs (z i - z j) else 1

/-- Product over unordered pairs (gives Δ^{1/2}) -/
noncomputable def DeltaSqrt (z : Configuration n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then Complex.abs (z i - z j) else 1

/- ## Part II: Regular Polygon Configuration -/

/-- The n-th roots of unity, scaled to diameter 2 -/
noncomputable def RegularPolygon (n : ℕ) (hn : n > 0) : Configuration n :=
  fun k => Complex.exp (2 * Real.pi * Complex.I * k / n)

/- ## Part III: Erdős-Herzog-Piranian Bound (1958) -/

/-- Polynomial with roots z₁,...,zₙ -/
noncomputable def polynomialFromRoots (z : Configuration n) : ℂ → ℂ :=
  fun w => ∏ i : Fin n, (w - z i)

/-- The sublevel set {w : |f(w)| < 1} is connected.
Axiomatized since full topological connectivity is complex in Lean. -/
axiom ConnectedSublevelSet (f : ℂ → ℂ) : Prop

/- ## Part IV: Pommerenke's Upper Bound (1961) -/

/- ## Part V: Counterexamples for Even n -/

/-- Cambie: Regular polygon not optimal for ALL even n ≥ 4 -/
axiom cambie_even_not_optimal (n : ℕ) (hn : n ≥ 4) (heven : Even n) :
  ∃ z : Configuration n, DiameterAtMost2 z ∧
    Delta z > Delta (RegularPolygon n (by omega))

/- ## Part VI: Lower Bounds for Even n -/

/-- The maximum Δ over all valid configurations -/
noncomputable def MaxDelta (n : ℕ) : ℝ :=
  sSup { Delta z | z : Configuration n ∧ DiameterAtMost2 z }

/-- Cambie-Dong-Tang: C ≈ 1.269 for all even n -/
axiom cambie_dong_tang_even :
  ∃ C : ℝ, C ≥ 1.269 ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Even n → MaxDelta n / n ^ n ≥ C - ε

/- ## Part VII: Odd n and Small Cases -/

/-- Conjecture: Regular polygon is optimal for odd n (OPEN) -/
def RegularPolygonOptimalOdd : Prop :=
  ∀ n : ℕ, n ≥ 3 → Odd n → ∀ z : Configuration n, DiameterAtMost2 z →
    Delta z ≤ Delta (RegularPolygon n (by omega))

/- ## Part VIII: Summary -/

/--
**Erdős Problem #1045: Summary**

For even n ≥ 4, the regular polygon is NOT optimal for maximizing Δ.
The maximum exceeds n^n by a factor of at least 1.269.
For odd n, the regular polygon may still be optimal (open).
-/
theorem erdos_1045_summary :
    -- For even n: regular polygon is NOT optimal
    (∀ n : ℕ, n ≥ 4 → Even n →
      ∃ z : Configuration n, DiameterAtMost2 z ∧
        Delta z > Delta (RegularPolygon n (by omega))) ∧
    -- Lower bound: max Δ / n^n ≥ 1.269 for even n
    (∃ C : ℝ, C > 1 ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Even n →
      MaxDelta n / n ^ n ≥ C - ε) :=
  ⟨cambie_even_not_optimal,
   let ⟨C, hC, h⟩ := cambie_dong_tang_even; ⟨C, by linarith, h⟩⟩

end Erdos1045
