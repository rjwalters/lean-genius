/-
  Aristotle targets for Erdős Problem #1034
  Routine supporting lemmas for automated proof search.
  See Erdos1034Problem.lean for the main formalization.

  Note: The main file has Aristotle parser issues with the Triangle structure.
  This companion file uses self-contained definitions to avoid those issues.

  Criteria for inclusion:
  - NOT the main Ma-Tang counterexample or deep extremal results
  - Basic graph/finset properties provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1034Aristotle

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Triangle Basics
-- ═══════════════════════════════════════════════════════════════════

/-- Three distinct vertices. -/
structure TripleDistinct (V : Type*) where
  v1 : V
  v2 : V
  v3 : V
  distinct12 : v1 ≠ v2
  distinct23 : v2 ≠ v3
  distinct13 : v1 ≠ v3

/-- The finset of vertices of a triple. -/
def TripleDistinct.toFinset (T : TripleDistinct V) : Finset V :=
  {T.v1, T.v2, T.v3}

/-- A triple of distinct elements has cardinality 3. -/
theorem triple_card (T : TripleDistinct V) : T.toFinset.card = 3 := by
  simp only [TripleDistinct.toFinset]
  rw [Finset.card_insert_of_not_mem (by simp [T.distinct12, T.distinct13]),
      Finset.card_insert_of_not_mem (by simp [T.distinct23]),
      Finset.card_singleton]

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Adjacency Counting
-- ═══════════════════════════════════════════════════════════════════

/-- Count how many elements of a finset S are adjacent to y. -/
def adjCount (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (y : V) : ℕ :=
  (S.filter (fun v => G.Adj y v)).card

/-- If y is adjacent to all elements of S, adjCount = |S|. -/
theorem adjCount_eq_card_of_all_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (y : V)
    (h : ∀ v ∈ S, G.Adj y v) : adjCount G S y = S.card := by
  simp only [adjCount]
  congr 1; ext v; simp [h v]

/-- adjCount is at most |S|. -/
theorem adjCount_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (y : V) : adjCount G S y ≤ S.card := by
  simp only [adjCount]; exact Finset.card_filter_le S _

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Numerical Constants
-- ═══════════════════════════════════════════════════════════════════

/-- The Ma-Tang constant: 2 - √(5/2). -/
noncomputable def maTangConstant : ℝ := 2 - Real.sqrt (5/2)

/-- The K₄-free constant: 2√3 - 3. -/
noncomputable def k4FreeConstant : ℝ := 2 * Real.sqrt 3 - 3

/-- Ma-Tang constant is positive. -/
theorem maTangConstant_pos : maTangConstant > 0 := by
  unfold maTangConstant
  -- Need sqrt(5/2) < 2, i.e., 5/2 < 4
  have hsq : Real.sqrt (5/2) ^ 2 = 5/2 := Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg (Real.sqrt (5/2) - 2)]

/-- K₄-free constant is positive. -/
theorem k4FreeConstant_pos : k4FreeConstant > 0 := by
  unfold k4FreeConstant
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by positivity)
  have hpos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by positivity)
  -- sqrt(3) > 3/2 since 3 > 9/4
  nlinarith [sq_nonneg (Real.sqrt 3 - 3/2)]

/-- K₄-free bound is worse (higher) than general bound. -/
theorem k4free_gt_maTang : k4FreeConstant > maTangConstant := by
  unfold k4FreeConstant maTangConstant
  -- Need 2*sqrt(3) - 3 > 2 - sqrt(5/2), i.e., 2*sqrt(3) + sqrt(5/2) > 5
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by positivity)
  have hsq52 : Real.sqrt (5/2) ^ 2 = 5/2 := Real.sq_sqrt (by positivity)
  have hpos3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by positivity)
  have hpos52 : Real.sqrt (5/2) > 0 := Real.sqrt_pos.mpr (by positivity)
  -- sqrt(3) > 1.7 and sqrt(5/2) > 1.5, so 2*1.7 + 1.5 = 4.9... hmm not quite > 5
  -- Actually: 2*sqrt(3) + sqrt(5/2) > 5?
  -- sqrt(3) ≈ 1.732, sqrt(5/2) ≈ 1.581, so 2*1.732 + 1.581 = 5.045 > 5. Yes.
  nlinarith [sq_nonneg (Real.sqrt 3 - 7/4), sq_nonneg (Real.sqrt (5/2) - 3/2)]

/-- Both constants are less than 1/2. -/
theorem maTangConstant_lt_half : maTangConstant < 1/2 := by
  unfold maTangConstant
  -- Need sqrt(5/2) > 3/2, i.e., 5/2 > 9/4
  have hsq : Real.sqrt (5/2) ^ 2 = 5/2 := Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg (Real.sqrt (5/2) - 3/2)]

/-- The gap between 1/6 and the Ma-Tang constant. -/
theorem gap_bounds : maTangConstant - 1/6 > 1/4 ∧ maTangConstant - 1/6 < 3/10 := by
  unfold maTangConstant
  have hsq : Real.sqrt (5/2) ^ 2 = 5/2 := Real.sq_sqrt (by positivity)
  constructor
  · -- 2 - sqrt(5/2) - 1/6 > 1/4, i.e., sqrt(5/2) < 2 - 1/6 - 1/4 = 19/12
    nlinarith [sq_nonneg (Real.sqrt (5/2) - 19/12)]
  · -- 2 - sqrt(5/2) - 1/6 < 3/10, i.e., sqrt(5/2) > 2 - 1/6 - 3/10 = 46/30 = 23/15
    nlinarith [sq_nonneg (Real.sqrt (5/2) - 23/15)]

end Erdos1034Aristotle
