/-
  Aristotle targets for Erdős Problem #613: Graph Decomposition and Size Ramsey Numbers
  Routine supporting lemmas for automated proof search.
  See Erdos613Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main Pikhurko disproof results (too deep)
  - NOT the n3_holds / n4_holds graph-theoretic results (require graph constructions)
  - Elementary arithmetic about criticalEdgeCount and conjecturedSizeRamsey
  - Concrete numerical verifications
  - Positivity and monotonicity lemmas provable by omega/norm_num/simp
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections (use /- instead)
-/
import Mathlib

namespace Erdos613Aristotle

open Nat

/-
## Section 1: The Critical Edge Count Function

criticalEdgeCount n = C(2n+1, 2) - C(n, 2) - 1

This is the number of edges in the graph-decomposition problem.
-/

/-- The critical edge count from the problem -/
def criticalEdgeCount (n : ℕ) : ℕ :=
  (2*n + 1).choose 2 - n.choose 2 - 1

/-- The conjectured size Ramsey value -/
def conjecturedSizeRamsey (n : ℕ) : ℕ :=
  (2*n + 1).choose 2 - n.choose 2

/-- criticalEdgeCount = conjecturedSizeRamsey - 1 -/
theorem criticalEdgeCount_eq_conjectured_sub_one (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n + 1 = conjecturedSizeRamsey n := by
  simp [criticalEdgeCount, conjecturedSizeRamsey]

/-- C(2n+1, 2) = n * (2*n+1) -/
theorem choose_2n1_2 (n : ℕ) : (2*n + 1).choose 2 = n * (2*n + 1) := by
  sorry

/-- C(n, 2) = n * (n-1) / 2 -/
theorem choose_n_2 (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := by
  sorry

/-- Concrete value: criticalEdgeCount 1 = 2 -/
theorem criticalEdgeCount_1 : criticalEdgeCount 1 = 2 := by native_decide

/-- Concrete value: criticalEdgeCount 2 = 8 -/
theorem criticalEdgeCount_2 : criticalEdgeCount 2 = 8 := by native_decide

/-- Concrete value: criticalEdgeCount 3 = 17 -/
theorem criticalEdgeCount_3 : criticalEdgeCount 3 = 17 := by native_decide

/-- Concrete value: criticalEdgeCount 4 = 29 -/
theorem criticalEdgeCount_4 : criticalEdgeCount 4 = 29 := by native_decide

/-- Concrete value: criticalEdgeCount 5 = 44 -/
theorem criticalEdgeCount_5 : criticalEdgeCount 5 = 44 := by native_decide

/-- Concrete value: criticalEdgeCount 6 = 62 -/
theorem criticalEdgeCount_6 : criticalEdgeCount 6 = 62 := by native_decide

/-- Concrete value: criticalEdgeCount 10 = 164 -/
theorem criticalEdgeCount_10 : criticalEdgeCount 10 = 164 := by native_decide

/-
## Section 2: Arithmetic Properties of criticalEdgeCount
-/

/-- criticalEdgeCount is positive for n ≥ 1 -/
theorem criticalEdgeCount_pos (n : ℕ) (hn : n ≥ 1) : 0 < criticalEdgeCount n := by
  sorry

/-- criticalEdgeCount is monotone -/
theorem criticalEdgeCount_mono (n m : ℕ) (h : n ≤ m) :
    criticalEdgeCount n ≤ criticalEdgeCount m := by
  sorry

/-- criticalEdgeCount n < criticalEdgeCount (n+1) for n ≥ 1 -/
theorem criticalEdgeCount_strict_mono (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n < criticalEdgeCount (n + 1) := by
  sorry

/-- conjecturedSizeRamsey is positive for n ≥ 1 -/
theorem conjecturedSizeRamsey_pos (n : ℕ) (hn : n ≥ 1) :
    0 < conjecturedSizeRamsey n := by
  sorry

/-- criticalEdgeCount n < conjecturedSizeRamsey n for n ≥ 1 -/
theorem criticalEdgeCount_lt_conjectured (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n < conjecturedSizeRamsey n := by
  unfold criticalEdgeCount conjecturedSizeRamsey
  sorry

/-
## Section 3: The Gap Between Bounds

The Pikhurko bounds say:
  n² + 0.577 * n^{3/2} < r̂ < n² + √2 * n^{3/2} + n

The gap width is (√2 - 0.577) * n^{3/2} + n.
-/

/-- boundGap is positive for n ≥ 3 -/
theorem boundGap_pos (n : ℕ) (hn : n ≥ 3) :
    (0 : ℝ) < (Real.sqrt 2 - 0.577) * n^(3/2 : ℝ) + n := by
  sorry

/-- √2 - 0.577 > 0 (since √2 ≈ 1.41421 > 0.577) -/
theorem sqrt2_sub_pos : (0 : ℝ) < Real.sqrt 2 - 0.577 := by
  sorry

/-- n^(3/2) ≥ n for n ≥ 1 -/
theorem rpow_3_2_ge_self (n : ℕ) (hn : n ≥ 1) :
    (n : ℝ) ≤ (n : ℝ)^(3/2 : ℝ) := by
  sorry

/-
## Section 4: Binomial Coefficient Comparison
-/

/-- C(2n+1, 2) > C(n, 2) for n ≥ 1 -/
theorem choose_ineq (n : ℕ) (hn : n ≥ 1) :
    n.choose 2 + 1 ≤ (2*n + 1).choose 2 := by
  sorry

/-- conjecturedSizeRamsey n ≥ n^2 for n ≥ 1 -/
theorem conjecturedSizeRamsey_ge_sq (n : ℕ) (hn : n ≥ 1) :
    n * n ≤ conjecturedSizeRamsey n := by
  sorry

/-- criticalEdgeCount grows like 3n²/2 for large n -/
theorem criticalEdgeCount_lower_bound (n : ℕ) (hn : n ≥ 2) :
    n * n ≤ criticalEdgeCount n := by
  sorry

end Erdos613Aristotle
