/-
  Aristotle targets for Erdős Problem #642
  Routine supporting lemmas for automated proof search.
  See Erdos642Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (Hamburger-Szegedy: f(n) = o(n))
  - NOT the axiomatized bounds (chen_erdos_staton, dmms_2024)
  - Routine arithmetic and graph-theoretic facts supporting the sorry theorems
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections
-/
import Mathlib

namespace Erdos642Aristotle

open Finset Function SimpleGraph Real

/-
  ## Section 1: Binomial Coefficient Arithmetic

  f_le_complete needs: edgeFinset.card ≤ n*(n-1)/2.
  This follows from the standard bound edgeFinset.card ≤ n.choose 2 = n*(n-1)/2.
-/

-- Aristotle target: n.choose 2 = n*(n-1)/2 (from Nat.choose_two_right)
theorem nat_choose_two_eq (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := by sorry

-- Aristotle target: n*(n-1)/2 ≥ 0 (trivial in ℕ)
theorem n_mul_pred_div_two_nonneg (n : ℕ) : n * (n - 1) / 2 ≥ 0 := by sorry

-- Aristotle target: (Fintype.card (Fin n)).choose 2 = n.choose 2
theorem fintype_card_fin_choose (n : ℕ) :
    (Fintype.card (Fin n)).choose 2 = n.choose 2 := by sorry

/-
  ## Section 2: Simple Graph Edge Count Bounds

  A simple graph on n vertices has at most n.choose 2 = n*(n-1)/2 edges.
  This is the key fact for f_le_complete.
-/

-- Aristotle target: edge set of a simple graph on Fin n has at most n.choose 2 edges
theorem edgeFinset_card_le_choose {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ (Fintype.card (Fin n)).choose 2 := by sorry

-- Aristotle target: edgeFinset.card ≤ n*(n-1)/2 for G on Fin n
theorem edgeFinset_card_le_formula {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ n * (n - 1) / 2 := by sorry

/-
  ## Section 3: Iterated Logarithm Properties

  The logStar function grows extremely slowly.
  These support the DMMS bound n * logStar n.
-/

-- Local copy of logStar for standalone use
noncomputable def logStarAux : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => 1 + logStarAux (Nat.log2 (n + 2))

-- Aristotle target: logStarAux 0 = 0
theorem logStarAux_zero : logStarAux 0 = 0 := by sorry

-- Aristotle target: logStarAux 1 = 0
theorem logStarAux_one : logStarAux 1 = 0 := by sorry

-- Aristotle target: logStarAux 2 = 1
theorem logStarAux_two : logStarAux 2 = 1 := by sorry

-- Aristotle target: n * (logStarAux n + 1) ≥ n for all n (since logStarAux n + 1 ≥ 1)
theorem n_mul_logStar_plus_one_ge (n : ℕ) : n * (logStarAux n + 1) ≥ n := by sorry

/-
  ## Section 4: Cycle-Diagonal Arithmetic

  Basic numeric facts about the cycle-diagonal condition.
  The condition is: cycle.len > diagonal_count.
  For short cycles, this is always satisfied.
-/

-- Aristotle target: for k = 3, k > k*(k-3)/2 (= 0): 3 > 0
theorem three_gt_three_diag : (3 : ℕ) > 3 * (3 - 3) / 2 := by sorry

-- Aristotle target: for k = 4, k > k*(k-3)/2 (= 2): 4 > 2
theorem four_gt_four_diag : (4 : ℕ) > 4 * (4 - 3) / 2 := by sorry

-- Aristotle target: for k ≥ 5, k ≤ k*(k-3)/2 (critical transition)
-- k=5: 5 ≤ 5*2/2 = 5. k=6: 6 ≤ 6*3/2 = 9.
theorem k_le_k_diag_for_k_ge_5 (k : ℕ) (hk : k ≥ 5) :
    k ≤ k * (k - 3) / 2 := by sorry

end Erdos642Aristotle
