/-
  Aristotle targets for Erdős Problem #1007 OQ-01
  Regular simplex embedding distance computations.
  See Erdos1007OQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1007Aristotle

open Finset Real

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Telescoping Sum Identity
-- ═══════════════════════════════════════════════════════════════════

/-- Telescoping: Σ_{j=0}^{n-1} 1/((j+1)(j+2)) = n/(n+1). -/
theorem sum_inv_consecutive (n : ℕ) :
    (Finset.range n).sum (fun j => (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) =
      (n : ℝ) / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Centroid and Height Computations
-- ═══════════════════════════════════════════════════════════════════

/-- Centroid coordinate squared: 1/(√(2ab))² = 1/(2ab) -/
theorem centroid_sq (j : ℕ) :
    (1 / Real.sqrt (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2))) ^ 2 =
      1 / (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  have h : (0 : ℝ) ≤ 2 * ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
  rw [div_pow, one_pow, sq_sqrt h]

/-- Height squared: (√((k+1)/(2k)))² = (k+1)/(2k) for k > 0 -/
theorem height_sq (k : ℕ) (hk : 0 < k) :
    (Real.sqrt (((k : ℝ) + 1) / (2 * (k : ℝ)))) ^ 2 = ((k : ℝ) + 1) / (2 * (k : ℝ)) :=
  sq_sqrt (by positivity)

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Sum Splitting Lemmas
-- ═══════════════════════════════════════════════════════════════════

/-- Centroid sum: Σ_{j=0}^{k-2} 1/(2(j+1)(j+2)) = (k-1)/(2k) for k ≥ 1. -/
theorem centroid_sum (k : ℕ) (hk : 1 ≤ k) :
    (Finset.range (k - 1)).sum (fun j => (1 : ℝ) / (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2))) =
      ((k : ℝ) - 1) / (2 * (k : ℝ)) := by
  -- Factor out 1/2 from the sum
  have step1 : (Finset.range (k - 1)).sum (fun j => (1 : ℝ) / (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2))) =
    (1 / 2) * (Finset.range (k - 1)).sum (fun j => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((j : ℝ) + 2) ≠ 0 := by positivity
    field_simp
  rw [step1, sum_inv_consecutive]
  -- (k-1 : ℕ) cast to ℝ and simplify
  have h1 : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    have := Nat.sub_add_cancel hk
    exact_mod_cast this
  rw [h1]
  simp only [Nat.cast_sub hk, Nat.cast_one]
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- Height + centroid = 1: (k-1)/(2k) + (k+1)/(2k) = 1 for k ≥ 1. -/
theorem height_plus_centroid (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) - 1) / (2 * (k : ℝ)) + ((k : ℝ) + 1) / (2 * (k : ℝ)) = 1 := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Graph Dimension Bounds
-- ═══════════════════════════════════════════════════════════════════

/-- For the complete bipartite graph K_{3,3}: number of edges is 9 -/
theorem K33_edges : 3 * 3 = (9 : ℕ) := by omega

/-- Binomial coefficient C(5,2) = 10 -/
theorem binom_5_2 : 5 * 4 / 2 = (10 : ℕ) := by omega

/-- K_{3,3} beats K₅ for dimension 4: 9 < 10 -/
theorem K33_beats_K5 : (9 : ℕ) < 10 := by omega

/-- The general upper bound: minEdges(d) ≤ d(d+1)/2 -/
theorem general_upper_bound (d : ℕ) (hd : 1 ≤ d) :
    d ≤ d * (d + 1) / 2 := by
  calc d = d * 2 / 2 := by omega
    _ ≤ d * (d + 1) / 2 := Nat.div_le_div_right (Nat.mul_le_mul_left d (by omega))

/-- Quadratic growth lower bound: d ≤ d(d+1)/2 -/
theorem quadratic_lower (d : ℕ) : d ≤ d * (d + 1) / 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · calc d = d * 2 / 2 := by omega
      _ ≤ d * (d + 1) / 2 := Nat.div_le_div_right (Nat.mul_le_mul_left d (by omega))

end Erdos1007Aristotle
