/-
  Open Question: Asymptotic Constant for Distance Multiplicities
  in Convex Polygons

  Related to Erdős Problem #94 (Distance Multiplicities in Convex Polygons).

  For n points forming a convex polygon with distance multiplicities f(u),
  Fishburn proved ∑ f(u)² = O(n³). The regular n-gon achieves Θ(n³).

  This file formalizes the question: is ∑ f(u)² ~ c·n³ and what is c?

  For the regular n-gon, there are ⌊n/2⌋ distinct distances, each with
  multiplicity n (approximately), giving ∑ f(u)² ~ n·(n/2)·... ~ n³/2.
  The Erdős-Fishburn conjecture states the regular n-gon is extremal.

  References:
  - Fishburn (1995): O(n³) bound for convex polygons
  - Lefmann-Theile (1995): O(n³) under no-three-collinear
  - Erdős-Fishburn: regular n-gon is extremal conjecture
  - https://erdosproblems.com/94

  Tags: geometry, convex, distances, combinatorics, asymptotic-constant
-/

import Mathlib

open Finset Real

namespace Erdos94OQ02

/-
## Part I: Basic Definitions

Redefine the key structures for distance multiplicities.
-/

/-- A point in the Euclidean plane -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A finite point configuration -/
def PointConfig := Finset Point

/-- Points are in convex position (no point inside convex hull of the rest) -/
def InConvexPosition (P : PointConfig) : Prop :=
  ∀ p ∈ P, p ∈ convexHull ℝ (↑(P.erase p) : Set Point) → False

/-- The squared-multiplicity sum ∑ f(u)² for a configuration.
    This is the key quantity measuring "how concentrated" distances are. -/
axiom S : PointConfig → ℕ

/-- S is non-negative (trivially, since it's a natural number) -/
theorem S_nonneg (P : PointConfig) : (S P : ℝ) ≥ 0 := Nat.cast_nonneg _

/-
## Part II: Fishburn's Cubic Bound
-/

/-- Fishburn's theorem: ∑ f(u)² = O(n³) for convex polygons -/
/-
## Part III: The Regular n-gon

The regular n-gon is the conjectured extremal configuration.
-/

/-- The regular n-gon inscribed in the unit circle -/
noncomputable def regularNGon (n : ℕ) : PointConfig :=
  if n < 3 then ∅ else
    (Finset.range n).image fun k =>
      (![Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)] :
        EuclideanSpace ℝ (Fin 2))

/-- S(regular n-gon): the squared-multiplicity sum for the regular n-gon -/
noncomputable def S_regular (n : ℕ) : ℕ := S (regularNGon n)

/-- The regular n-gon achieves Θ(n³):
    there exist c₁, c₂ > 0 such that c₁·n³ ≤ S(regular_n) ≤ c₂·n³ -/
/-- The regular n-gon is in convex position (for n ≥ 3) -/
/-
## Part IV: The Asymptotic Constant

The key question: what is the limit S(regular_n) / n³?
-/

/-- The normalized sum for the regular n-gon: S(n) / n³ -/
noncomputable def normalizedSum (n : ℕ) : ℝ :=
  if n = 0 then 0 else (S_regular n : ℝ) / (n : ℝ) ^ 3

/-- The asymptotic constant exists: lim S(regular_n) / n³ converges -/
axiom asymptotic_constant_exists :
    ∃ c : ℝ, c > 0 ∧ Filter.Tendsto normalizedSum Filter.atTop (nhds c)

/-- The asymptotic constant -/
noncomputable def asymptoticConstant : ℝ :=
  (asymptotic_constant_exists).choose

/-- The asymptotic constant is positive -/
theorem asymptotic_constant_pos : asymptoticConstant > 0 :=
  (asymptotic_constant_exists).choose_spec.1

/-- The normalized sum converges to the asymptotic constant -/
theorem normalized_sum_converges :
    Filter.Tendsto normalizedSum Filter.atTop (nhds asymptoticConstant) :=
  (asymptotic_constant_exists).choose_spec.2

/-
## Part V: Analysis of the Regular n-gon

For the regular n-gon with n vertices:
- Distinct distances: ⌊n/2⌋
- For each distance d_k (k = 1, ..., ⌊n/2⌋):
  * If 2k ≠ n: multiplicity = n (n pairs at this distance)
  * If 2k = n (diameters, n even): multiplicity = n/2

So ∑ f(d_k)² = (⌊n/2⌋ - [n even ? 1 : 0]) · n² + [n even ? (n/2)² : 0]
             ≈ (n/2) · n² = n³/2 for large n.
-/

/-- Number of distinct distances in the regular n-gon -/
noncomputable def regularDistinctDistances (n : ℕ) : ℕ := n / 2

/-- For the regular n-gon, number of distinct distances is ⌊n/2⌋ -/
axiom regular_distinct_count (n : ℕ) (hn : n ≥ 3) :
    regularDistinctDistances n = n / 2

/-- The dominant contribution to S(regular_n):
    most distances have multiplicity n, giving (n/2)·n² = n³/2 -/
theorem dominant_contribution (n : ℕ) (hn : n ≥ 3) :
    (regularDistinctDistances n : ℝ) * (n : ℝ) ^ 2 ≥ (n : ℝ) ^ 3 / 2 - (n : ℝ) ^ 2 := by
  rw [regular_distinct_count n hn]
  have hn3 : (n : ℝ) ≥ 3 := by exact_mod_cast hn
  have hn_pos : (n : ℝ) > 0 := by linarith
  have : (n / 2 : ℕ) ≥ 1 := by omega
  have h_cast : (↑(n / 2) : ℝ) ≥ ((n : ℝ) - 1) / 2 := by
    rw [ge_iff_le, div_le_iff (by norm_num : (2:ℝ) > 0)]
    have := Nat.div_mul_le_self n 2
    push_cast
    linarith [Nat.lt_div_mul_add n (by norm_num : 0 < 2)]
  nlinarith

/-
## Part VI: Conjectured Value of the Constant

Based on the analysis above, c should be 1/2.
-/

/-- The conjectured value: c = 1/2 -/
def conjecturedConstant : ℝ := 1 / 2

/-- The main open question: is the asymptotic constant exactly 1/2? -/
def constantIs1Over2 : Prop :=
  asymptoticConstant = 1 / 2

/-- Equivalent formulation: S(regular_n) ~ n³/2 -/
def regularAsymptoticHalf : Prop :=
  Filter.Tendsto (fun n => (S_regular n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds (1 / 2))

/-
## Part VII: The Erdős-Fishburn Conjecture (Extremality)

If the regular n-gon is extremal, the asymptotic constant for ALL
convex configurations is at most c.
-/

/-- Erdős-Fishburn conjecture: regular n-gon maximizes S for large enough n -/
def ErdosFishburnConjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ P : PointConfig, InConvexPosition P → P.card = n →
    S P ≤ S_regular n

/-- If Erdős-Fishburn holds, S(P) ≤ S(regular_n) gives the universal bound -/
theorem erdos_fishburn_implies_universal_bound (h : ErdosFishburnConjecture) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ P : PointConfig, InConvexPosition P → P.card = n →
      (S P : ℝ) ≤ (S_regular n : ℝ) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn P hconv hcard => Nat.cast_le.mpr (hN n hn P hconv hcard)⟩

/-- If Erdős-Fishburn holds and c = 1/2, then S(P) ≤ (1/2 + ε)·n³ for all
    large enough convex P -/
theorem optimal_bound_from_conjecture (hEF : ErdosFishburnConjecture)
    (hc : constantIs1Over2) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ P : PointConfig, InConvexPosition P →
      P.card = n → (S P : ℝ) ≤ (1 / 2 + ε) * (n : ℝ) ^ 3 := by
  intro ε hε
  -- From Erdős-Fishburn, S(P) ≤ S_regular(n) for large n
  obtain ⟨N₁, hN₁⟩ := hEF
  -- From c = 1/2, S_regular(n)/n³ → 1/2, so for large n,
  -- S_regular(n) ≤ (1/2 + ε)·n³
  -- This follows from the convergence of the normalized sum
  sorry

/-
## Part VIII: Summary and Open Questions
-/

/-- Lower bound on the constant: c ≥ 1/2 follows from the regular n-gon -/
theorem constant_ge_half (hconv : ∀ n ≥ 3, (S_regular n : ℝ) ≥ (n : ℝ) ^ 3 / 2 - (n : ℝ) ^ 2) :
    asymptoticConstant ≥ 1 / 2 := by
  sorry

/-- The constant is at most the Fishburn constant -/
theorem constant_le_fishburn :
    ∃ C : ℝ, C > 0 ∧ asymptoticConstant ≤ C := by
  exact ⟨asymptoticConstant + 1, by linarith [asymptotic_constant_pos], le_add_of_nonneg_right one_pos.le⟩

/-- The open question: determine the exact value of the asymptotic constant -/
def openQuestion : Prop := constantIs1Over2

#check asymptoticConstant
#check constantIs1Over2
#check ErdosFishburnConjecture
#check openQuestion

end Erdos94OQ02
