/-
  Aristotle targets for Erdos549Problem
  Routine supporting lemmas for automated proof search.
  See Erdos549Problem.lean for the main formalization.

  These lemmas provide building blocks for the bipartite tree Ramsey problem:
  - Star graph properties (adjacency, tree structure)
  - Double star vertex counts and bipartition
  - Path graph properties
  - Broom graph structure
  - Constant arithmetic (4.2, 4.21526, bounds gap)
  - Formula computations for burrErdos
-/
import Mathlib

open Finset Function Set SimpleGraph

namespace Erdos549.Aristotle

/-
  ## Section 1: Star Graph Properties
-/

def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := by intro u v; simp [or_comm, and_comm]
  loopless := by intro u; simp

-- Star graph vertex count
theorem star_vertex_count (n : ℕ) :
    Fintype.card (Fin (n + 1)) = n + 1 := by sorry

-- Star graph center (vertex 0) is adjacent to all non-center vertices
theorem star_center_adj (n : ℕ) (v : Fin (n + 1)) (hv : v ≠ 0) :
    (starGraph n).Adj 0 v := by sorry

-- No edges between non-center vertices in a star
theorem star_no_leaf_edges (n : ℕ) (u v : Fin (n + 1))
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ¬(starGraph n).Adj u v := by sorry

-- Star graph is connected for n ≥ 1
theorem star_connected (n : ℕ) (hn : n ≥ 1) :
    (starGraph n).Connected := by sorry

-- Star graph is acyclic
theorem star_acyclic (n : ℕ) :
    (starGraph n).IsAcyclic := by sorry

/-
  ## Section 2: Double Star Vertex Counts
-/

-- Double star has 3k + 2 vertices
theorem double_star_vertex_count (k : ℕ) :
    Fintype.card (Fin (3 * k + 2)) = 3 * k + 2 := by sorry

-- For k ≥ 1, 3k + 2 > 4k - 1 is false, i.e. 3k + 2 ≤ 4k - 1
-- (relevant: the bipartite tree has 3k vertices, not 3k + 2)
-- The tree has k vertices in partA and 2k in partB, total 3k
-- But the underlying Fin type has 3k + 2 (including 2 centers)

-- 3k + 2 ≥ 5 for k ≥ 1
theorem double_star_min_vertices (k : ℕ) (hk : k ≥ 1) :
    3 * k + 2 ≥ 5 := by sorry

-- 4k - 1 formula values
theorem formula_val_1 : 4 * 1 - 1 = 3 := by sorry

theorem formula_val_2 : 4 * 2 - 1 = 7 := by sorry

theorem formula_val_3 : 4 * 3 - 1 = 11 := by sorry

theorem formula_val_5 : 4 * 5 - 1 = 19 := by sorry

theorem formula_val_10 : 4 * 10 - 1 = 39 := by sorry

-- 4k - 1 is odd for all k
theorem formula_odd (k : ℕ) (hk : k ≥ 1) :
    ¬2 ∣ (4 * k - 1) := by sorry

-- 4k - 1 < 4.2 * k for large k
theorem formula_lt_constant_times_k (k : ℕ) (hk : k ≥ 100) :
    (4 * k - 1 : ℝ) < 4.2 * k := by sorry

/-
  ## Section 3: Path Graph Properties
-/

def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := by intro u v; simp [or_comm]
  loopless := by intro u; simp; omega

-- Path endpoints (first and last vertex)
theorem path_first_last_adj (n : ℕ) (hn : n ≥ 2) :
    (pathGraph n).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by sorry

-- Path graph has no cycles of length 3
theorem path_no_triangle (n : ℕ) (u v w : Fin n)
    (huv : (pathGraph n).Adj u v) (hvw : (pathGraph n).Adj v w)
    (hwu : (pathGraph n).Adj w u) : False := by sorry

/-
  ## Section 4: Broom Graph Properties
-/

def broomGraph (pathLen starSize : ℕ) : SimpleGraph (Fin (pathLen + starSize)) where
  Adj u v := by
    exact (u.val + 1 = v.val ∧ v.val < pathLen) ∨
          (v.val + 1 = u.val ∧ u.val < pathLen) ∨
          (u.val = pathLen - 1 ∧ v.val ≥ pathLen) ∨
          (v.val = pathLen - 1 ∧ u.val ≥ pathLen)
  symm := by intro u v; simp [or_comm, and_comm]
  loopless := by intro u; simp; omega

-- Broom vertex count
theorem broom_vertex_count (a b : ℕ) :
    Fintype.card (Fin (a + b)) = a + b := by sorry

-- Broom total vertices for bipartite (k, 2k) tree form
-- A broom with path length p and star size s has p + s vertices
-- For it to be a bipartite (k, 2k) tree, we need p + s = 3k

/-
  ## Section 5: Constant Arithmetic

  norinSunZhaoConstant = 4.2
  flagAlgebraConstant = 4.21526
-/

def norinSunZhaoConstant : ℝ := 4.2
def flagAlgebraConstant : ℝ := 4.21526

-- Basic bounds
theorem nsz_gt_four : norinSunZhaoConstant > 4 := by sorry

theorem flag_gt_four : flagAlgebraConstant > 4 := by sorry

theorem flag_gt_nsz : flagAlgebraConstant > norinSunZhaoConstant := by sorry

theorem bounds_gap_small : flagAlgebraConstant - norinSunZhaoConstant < 0.02 := by sorry

theorem bounds_gap_positive : flagAlgebraConstant - norinSunZhaoConstant > 0 := by sorry

-- The gap between 4.2k and (4k-1) grows linearly
theorem gap_grows (k : ℕ) (hk : k ≥ 1) :
    norinSunZhaoConstant * k - (4 * k - 1) = 0.2 * k + 1 := by sorry

-- For k = 5: 4.2 * 5 = 21, 4*5 - 1 = 19, gap = 2
theorem gap_at_5 : norinSunZhaoConstant * 5 = 21 := by sorry

-- For k = 10: 4.2 * 10 = 42, 4*10 - 1 = 39, gap = 3
theorem gap_at_10 : norinSunZhaoConstant * 10 = 42 := by sorry

/-
  ## Section 6: Burr-Erdős Formula

  burrErdosFormula H χ = (χ - 1)(|H| - 1) + 1
-/

def burrErdosFormula (n χ : ℕ) : ℕ := (χ - 1) * (n - 1) + 1

-- For trees (χ = 2), the formula gives |T| + (|T| - 2) + 1 = 2|T| - 1
theorem burr_erdos_tree (n : ℕ) (hn : n ≥ 1) :
    burrErdosFormula n 2 = 2 * n - 1 := by sorry

-- Formula values for small trees
theorem burr_erdos_val_3_2 : burrErdosFormula 3 2 = 5 := by sorry

theorem burr_erdos_val_4_2 : burrErdosFormula 4 2 = 7 := by sorry

theorem burr_erdos_val_5_2 : burrErdosFormula 5 2 = 9 := by sorry

-- For χ = 1, formula gives 1
theorem burr_erdos_chi_1 (n : ℕ) : burrErdosFormula n 1 = 1 := by sorry

-- Formula is monotone in n
theorem burr_erdos_mono_n (n₁ n₂ χ : ℕ) (hn : n₁ ≤ n₂) (hχ : χ ≥ 1) :
    burrErdosFormula n₁ χ ≤ burrErdosFormula n₂ χ := by sorry

-- Formula is monotone in χ
theorem burr_erdos_mono_chi (n χ₁ χ₂ : ℕ) (hχ : χ₁ ≤ χ₂) (hn : n ≥ 1) :
    burrErdosFormula n χ₁ ≤ burrErdosFormula n χ₂ := by sorry

end Erdos549.Aristotle
