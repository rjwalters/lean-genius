/-
Erdős Problem #465: Points with Distances Avoiding Integers

Source: https://erdosproblems.com/465
Status: SOLVED (Konyagin, 2001)

Statement:
Let N(X,δ) denote the maximum number of points P₁,...,Pₙ which can be chosen
in a circle of radius X such that
  ‖|Pᵢ - Pⱼ|‖ ≥ δ
for all 1 ≤ i < j ≤ n, where ‖x‖ is the distance from x to the nearest integer.

Questions:
1. Is N(X,δ) = o(X) for any 0 < δ < 1/2?
2. Is N(X,δ) < X^{1/2+o(1)} for any fixed δ > 0?

Answer: YES to both (Sárközy 1976, Konyagin 2001)
- Sárközy (1976): N(X,δ) ≪ δ⁻³ · X / log log X
- Konyagin (2001): N(X,δ) ≪_δ X^{1/2}

Key Insight:
The constraint that pairwise distances avoid integers severely restricts
how many points can be packed. The exponent 1/2 is optimal (see #466).

References:
- [Sa76] Sárközy, "On distances near integers I, II" (1976)
- [Ko01] Konyagin, "On the distances between points on the plane" (2001)
- Related: Problem #466 (lower bounds), Problem #953 (similar)

Tags: number-theory, combinatorics, diophantine-approximation, solved
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

open Real

namespace Erdos465

/-
## Part 1: Basic Definitions
-/

/-- Distance to the nearest integer: ‖x‖ = min{|x - n| : n ∈ ℤ} -/
noncomputable def distToInt (x : ℝ) : ℝ :=
  |x - round x|

/-- Alternative: ‖x‖ = min(x - ⌊x⌋, ⌈x⌉ - x) -/
noncomputable def distToInt' (x : ℝ) : ℝ :=
  min (x - ⌊x⌋) (⌈x⌉ - x)

/-
## Part 2: Point Configurations in Disks
-/

/-- A point configuration in a disk of radius X -/
structure PointConfig (n : ℕ) where
  points : Fin n → ℂ
  radius : ℝ
  radius_pos : radius > 0
  in_disk : ∀ i, Complex.abs (points i) ≤ radius

/-- Pairwise distances avoid integers by at least δ -/
def DistancesAvoidIntegers (P : PointConfig n) (δ : ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    distToInt (Complex.abs (P.points i - P.points j)) ≥ δ

/-- N(X, δ): Maximum n such that there exists a valid configuration -/
noncomputable def maxPoints (X δ : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ P : PointConfig n, P.radius = X ∧ DistancesAvoidIntegers P δ}

/-
## Part 3: The First Conjecture (Sublinear Growth)
-/

/-- First Conjecture: N(X, δ) = o(X) -/
def FirstConjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/2 →
    ∀ ε > 0, ∃ X₀ : ℝ, ∀ X ≥ X₀, (maxPoints X δ : ℝ) < ε * X

/-- Sárközy's stronger bound (1976) -/
def SarkozyBound : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/2 →
    ∃ C : ℝ, C > 0 ∧ ∀ X : ℝ, X ≥ 3 →
      (maxPoints X δ : ℝ) ≤ C * δ⁻¹^3 * X / Real.log (Real.log X)

/-- Sárközy's Theorem (1976): Proved the first conjecture with explicit bound -/
axiom sarkozy_1976 : SarkozyBound

/-- Corollary: The first conjecture holds -/
theorem first_conjecture_holds : FirstConjecture := by
  intro δ hδ_pos _ ε hε
  obtain ⟨C, hC, hbound⟩ := sarkozy_1976 δ hδ_pos (by linarith)
  -- Choose X₀ so that log(log X) > C·δ⁻³/ε for X ≥ X₀
  use max 3 (Real.exp (Real.exp (C * δ⁻¹ ^ 3 / ε)) + 1)
  intro X hX
  have hX3 : X ≥ 3 := le_trans (le_max_left _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXgt : X > Real.exp (Real.exp (C * δ⁻¹ ^ 3 / ε)) := by
    linarith [le_trans (le_max_right _ _) hX]
  -- Chain: X > exp(exp(K)) → log X > exp(K) → log(log X) > K where K = C·δ⁻³/ε
  have hlogX : Real.log X > Real.exp (C * δ⁻¹ ^ 3 / ε) := by
    have := Real.log_lt_log (Real.exp_pos _) hXgt
    rwa [Real.log_exp] at this
  have hloglogX : Real.log (Real.log X) > C * δ⁻¹ ^ 3 / ε := by
    have := Real.log_lt_log (Real.exp_pos _) hlogX
    rwa [Real.log_exp] at this
  have hloglogX_pos : (0 : ℝ) < Real.log (Real.log X) :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg hC.le (pow_nonneg (inv_nonneg.mpr hδ_pos.le) _)) hε.le)
      hloglogX
  -- Main: maxPoints ≤ C·δ⁻³·X/log(log X) < ε·X
  calc (↑(maxPoints X δ) : ℝ)
      ≤ C * δ⁻¹ ^ 3 * X / Real.log (Real.log X) := hbound X hX3
    _ < ε * X := by
        rw [div_lt_iff hloglogX_pos]
        have hkey : C * δ⁻¹ ^ 3 < ε * Real.log (Real.log X) := by
          have h := mul_lt_mul_of_pos_left hloglogX hε
          rwa [mul_comm ε, div_mul_cancel₀ _ hε.ne'] at h
        nlinarith

/-
## Part 4: The Second Conjecture (Square Root Growth)
-/

/-- Second Conjecture: N(X, δ) < X^{1/2+o(1)} -/
def SecondConjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/2 →
    ∀ ε > 0, ∃ X₀ : ℝ, ∀ X ≥ X₀,
      (maxPoints X δ : ℝ) < X ^ ((1:ℝ)/2 + ε)

/-- Konyagin's stronger bound (2001): N(X, δ) ≤ C_δ · X^{1/2} -/
def KonyaginBound : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/2 →
    ∃ C : ℝ, C > 0 ∧ ∀ X : ℝ, X ≥ 1 →
      (maxPoints X δ : ℝ) ≤ C * X ^ ((1:ℝ)/2)

/-- Konyagin's Theorem (2001): Proved the optimal X^{1/2} bound -/
axiom konyagin_2001 : KonyaginBound

/-- Corollary: The second conjecture holds -/
theorem second_conjecture_holds : SecondConjecture := by
  intro δ hδ_pos hδ_lt ε hε
  obtain ⟨C, hC, hbound⟩ := konyagin_2001 δ hδ_pos hδ_lt
  -- Choose X₀ so that C < X^ε for X ≥ X₀
  have hC1nn : (0 : ℝ) ≤ C + 1 := by linarith
  use max 1 ((C + 1) ^ ((1 : ℝ) / ε))
  intro X hX
  have hX1 : X ≥ 1 := le_trans (le_max_left _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXge : X ≥ (C + 1) ^ ((1 : ℝ) / ε) := le_trans (le_max_right _ _) hX
  have h1 := hbound X hX1
  -- Key: C < X^ε (via (C+1)^(1/ε) ≤ X so (C+1) ≤ X^ε)
  have hCltXε : C < X ^ ε := by
    have : C + 1 ≤ X ^ ε := calc
      C + 1 = ((C + 1) ^ ((1 : ℝ) / ε)) ^ ε := by
            rw [← rpow_mul hC1nn]; congr 1; field_simp
        _ ≤ X ^ ε := rpow_le_rpow (rpow_nonneg hC1nn _) hXge hε.le
    linarith
  -- C·X^(1/2) < X^ε · X^(1/2) = X^(1/2+ε)
  calc (↑(maxPoints X δ) : ℝ)
      ≤ C * X ^ ((1 : ℝ) / 2) := h1
    _ < X ^ ε * X ^ ((1 : ℝ) / 2) :=
        mul_lt_mul_of_pos_right hCltXε (rpow_pos_of_pos hXpos _)
    _ = X ^ ((1 : ℝ) / 2 + ε) := by
        rw [mul_comm, ← rpow_add hXpos]

/-
## Part 5: Comparison of Bounds
-/

/-
## Part 6: Lower Bounds (Problem #466)
-/

/-- There exist configurations with N(X, δ) ≫_δ X^{1/2} -/
def LowerBound : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/2 →
    ∃ c : ℝ, c > 0 ∧ ∀ X : ℝ, X ≥ 1 →
      (maxPoints X δ : ℝ) ≥ c * X ^ ((1:ℝ)/2)

/-- Problem #466: Lower bounds for N(X, δ) -/
axiom problem_466_lower_bound : LowerBound

/-
## Part 7: Related Techniques
-/

/-
## Part 8: Generalizations
-/

/-- Higher dimensions: points in ℝ^d -/
def HigherDimAnalogue (d : ℕ) : Prop :=
  -- Similar questions can be asked in higher dimensions
  -- The answers depend on d
  True

/-
## Part 9: Why X^{1/2}?
-/

/-
## Part 10: Summary
-/

/-- Erdős Problem #465 is SOLVED -/
theorem erdos_465_solved :
    FirstConjecture ∧ SecondConjecture := by
  constructor
  · exact first_conjecture_holds
  · exact second_conjecture_holds

/-- The optimal bound is N(X, δ) ≍ X^{1/2} -/
theorem optimal_growth :
    KonyaginBound ∧ LowerBound := by
  constructor
  · exact konyagin_2001
  · exact problem_466_lower_bound

/-- **Erdős Problem #465: SOLVED**

QUESTION: For points in a circle of radius X with pairwise
distances ‖d‖ ≥ δ (avoiding integers by δ),

1. Is N(X, δ) = o(X)?
2. Is N(X, δ) < X^{1/2+o(1)}?

ANSWER: YES to both!

RESULTS:
- Sárközy (1976): N(X, δ) ≪ δ⁻³ · X / log log X
- Konyagin (2001): N(X, δ) ≪_δ X^{1/2} [OPTIMAL]
- Lower bound (Problem #466): N(X, δ) ≫_δ X^{1/2}

CONCLUSION: N(X, δ) ≈ X^{1/2} up to δ-dependent constants.
-/
theorem erdos_465_summary :
    -- Both conjectures proved
    FirstConjecture ∧ SecondConjecture ∧
    -- Optimal exponent is 1/2
    KonyaginBound ∧ LowerBound := by
  constructor
  · exact first_conjecture_holds
  constructor
  · exact second_conjecture_holds
  exact optimal_growth

/-- Problem status -/
def erdos_465_status : String :=
  "SOLVED (Konyagin 2001) - N(X, δ) ≍ X^{1/2}"

end Erdos465
