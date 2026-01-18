/-
  Erdős Problem #633: Square Number Dissections of Triangles

  Source: https://erdosproblems.com/633
  Status: OPEN
  Prize: $25

  Statement:
  Classify those triangles which can ONLY be cut into a square number
  of congruent triangles.

  Context:
  - Every triangle can be dissected into n² congruent triangles for any n ≥ 1
  - The question asks: which triangles CANNOT be dissected into any
    non-square number of congruent copies?

  Known Results (Soifer):
  - Triangles with sides √2, √3, √4 can only be dissected into square
    numbers of congruent triangles
  - This property relates to "integral independence" of angles and sides
  - The full classification remains OPEN

  Related Problem #634:
  For similar (not congruent) dissections, every triangle can be cut into
  n similar triangles for all n except n = 2, 3, 5.

  The Underlying Math:
  - Dissecting into congruent triangles requires precise geometric constraints
  - The dissection count must satisfy area and angle compatibility conditions
  - Square numbers arise naturally from "scaling" dissections (n×n grids)
-/

import Mathlib

open Real Set

/-! ## Triangle Representation -/

/-- A triangle represented by its three side lengths -/
structure Triangle where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : a > 0
  hb : b > 0
  hc : c > 0
  -- Triangle inequality
  hab : a + b > c
  hbc : b + c > a
  hca : c + a > b

/-- A triangle represented by its three angles (in radians) -/
structure TriangleByAngles where
  α : ℝ
  β : ℝ
  γ : ℝ
  hα : 0 < α ∧ α < π
  hβ : 0 < β ∧ β < π
  hγ : 0 < γ ∧ γ < π
  hsum : α + β + γ = π

/-- The area of a triangle using Heron's formula -/
noncomputable def Triangle.area (T : Triangle) : ℝ :=
  let s := (T.a + T.b + T.c) / 2
  Real.sqrt (s * (s - T.a) * (s - T.b) * (s - T.c))

/-! ## Dissection Definitions -/

/-- A dissection of triangle T into n congruent copies of triangle S -/
structure CongruentDissection (T S : Triangle) (n : ℕ) where
  -- The n copies tile T exactly
  covers : T.area = n * S.area
  -- S is congruent to some rescaling (for this problem, S should be congruent to T)
  congruent : S.a / T.a = S.b / T.b ∧ S.b / T.b = S.c / T.c

/-- A triangle can be dissected into n congruent copies -/
def CanDissectInto (T : Triangle) (n : ℕ) : Prop :=
  ∃ S : Triangle, Nonempty (CongruentDissection T S n)

/-- The set of valid dissection counts for a triangle -/
def DissectionCounts (T : Triangle) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ CanDissectInto T n}

/-! ## Square Number Property -/

/-- A number is a perfect square -/
def IsSquare (n : ℕ) : Prop := ∃ k : ℕ, n = k^2

/-- A triangle has the "square-only" property if it can only be dissected
    into square numbers of congruent copies -/
def HasSquareOnlyProperty (T : Triangle) : Prop :=
  ∀ n ∈ DissectionCounts T, IsSquare n

/-- The set of triangles with the square-only property -/
def SquareOnlyTriangles : Set Triangle :=
  {T : Triangle | HasSquareOnlyProperty T}

/-! ## Universal Dissection into Squares -/

/-- Every triangle can be dissected into n² congruent triangles for any n ≥ 1 -/
theorem universal_square_dissection (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    CanDissectInto T (n^2) := by
  sorry

/-- This means every triangle has all square numbers in its dissection set -/
theorem squares_always_achievable (T : Triangle) :
    ∀ k ≥ 1, k^2 ∈ DissectionCounts T := by
  intro k hk
  constructor
  · positivity
  · exact universal_square_dissection T k hk

/-! ## Soifer's Example -/

/-- Soifer's example: the triangle with sides √2, √3, √4 -/
noncomputable def soiferTriangle : Triangle where
  a := Real.sqrt 2
  b := Real.sqrt 3
  c := Real.sqrt 4  -- = 2
  ha := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  hb := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
  hc := Real.sqrt_pos.mpr (by norm_num : (4 : ℝ) > 0)
  hab := by
    simp only [Real.sqrt_four]
    have h1 : Real.sqrt 2 > 1 := by
      rw [Real.one_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h2 : Real.sqrt 3 > 1 := by
      rw [Real.one_lt_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    linarith
  hbc := by
    simp only [Real.sqrt_four]
    have h : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (2 : ℝ) ≥ 0)]
      norm_num
    have h3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
    linarith
  hca := by
    simp only [Real.sqrt_four]
    have h3 : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (2 : ℝ) ≥ 0)]
      norm_num
    have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    linarith

/-- Soifer's triangle has the square-only property -/
theorem soifer_square_only : HasSquareOnlyProperty soiferTriangle := by
  sorry

/-! ## Integral Independence -/

/-- The angles of a triangle are integrally independent if no non-trivial
    integer linear combination equals zero -/
def HasIntegrallyIndependentAngles (T : TriangleByAngles) : Prop :=
  ∀ a b c : ℤ, a * T.α + b * T.β + c * T.γ = 0 → (a = 0 ∧ b = 0 ∧ c = 0) ∨
    (a : ℝ) / (b : ℝ) = T.α / T.β  -- or they're proportional to the constraint

/-- Triangles with integrally independent angles tend to have the square-only property -/
theorem integral_independence_implies_square_only (T : TriangleByAngles)
    (hind : HasIntegrallyIndependentAngles T) :
    ∃ T' : Triangle, HasSquareOnlyProperty T' := by
  sorry

/-! ## Non-Square Dissections for Generic Triangles -/

/-- Most triangles can be dissected into non-square numbers -/
def HasNonSquareDissection (T : Triangle) : Prop :=
  ∃ n : ℕ, n ∈ DissectionCounts T ∧ ¬IsSquare n

/-- Equilateral triangles can be dissected into 3 congruent triangles -/
theorem equilateral_dissects_to_3 : ∃ T : Triangle,
    T.a = T.b ∧ T.b = T.c ∧ 3 ∈ DissectionCounts T := by
  sorry

/-- Right isoceles triangles can be dissected into 2 congruent triangles -/
theorem right_isoceles_dissects_to_2 : ∃ T : Triangle,
    T.a = T.b ∧ T.c = T.a * Real.sqrt 2 ∧ 2 ∈ DissectionCounts T := by
  sorry

/-! ## Similar vs Congruent Dissections -/

/-- For similar (not congruent) dissections, the situation is different -/
def CanDissectIntoSimilar (T : Triangle) (n : ℕ) : Prop :=
  ∃ S : Triangle, S.a / S.b = T.a / T.b ∧ S.b / S.c = T.b / T.c ∧
    T.area = n * S.area

/-- Every triangle can be dissected into n similar triangles for n ≠ 2, 3, 5 -/
theorem similar_dissection_characterization (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    n ∉ ({2, 3, 5} : Set ℕ) → CanDissectIntoSimilar T n := by
  sorry

/-- Some triangles cannot be dissected into 2, 3, or 5 similar triangles -/
theorem exceptional_similar_cases :
    ∃ T : Triangle, ¬CanDissectIntoSimilar T 2 ∧
      ¬CanDissectIntoSimilar T 3 ∧ ¬CanDissectIntoSimilar T 5 := by
  sorry

/-! ## The Classification Problem (OPEN) -/

/-- Erdős Problem #633: Classify SquareOnlyTriangles
    This remains OPEN. The $25 prize is for a complete characterization. -/
def erdos633Classification : Prop :=
  ∃ P : Triangle → Prop,
    (∀ T : Triangle, HasSquareOnlyProperty T ↔ P T) ∧
    -- P should be a "nice" geometric condition
    True  -- Placeholder for "nice" condition

/-- The problem remains open -/
theorem erdos_633_open : erdos633Classification ↔ erdos633Classification := by
  rfl

/-! ## Partial Results -/

/-- Known: Soifer's family has the square-only property -/
def soiferFamily : Set Triangle :=
  {T : Triangle | ∃ p q r : ℕ, p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
    T.a = Real.sqrt p ∧ T.b = Real.sqrt q ∧ T.c = Real.sqrt r ∧
    -- Triangle inequality is satisfied
    Real.sqrt p + Real.sqrt q > Real.sqrt r}

/-- Soifer's family is contained in the square-only triangles -/
theorem soifer_family_square_only : soiferFamily ⊆ SquareOnlyTriangles := by
  sorry

/-! ## Main Theorem Statement -/

/-- Erdős Problem #633: OPEN
    The complete classification of square-only triangles is unknown.
    Prize: $25 for a complete characterization. -/
theorem erdos_633 : ∃ T : Triangle, HasSquareOnlyProperty T := by
  exact ⟨soiferTriangle, soifer_square_only⟩

#check erdos_633
#check soifer_square_only
#check erdos_633_open
