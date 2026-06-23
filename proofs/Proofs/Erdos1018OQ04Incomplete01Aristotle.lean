/-
  Aristotle targets for Erdos1018OQ04Incomplete01
  Supporting lemmas for the K₃/K₄ planarity sorries and Euler formula bound.
  See Proofs/Erdos1018OQ04Incomplete01.lean for the main formalization.

  Sorries targeted:
  1. K3_planar / K4_planar — convex hull separation for specific planar embeddings
  2. planar_graphs_edge_bound — Euler formula: planar graphs have ≤ 3n - 6 edges

  Not included: r2_implies_main_r2 (structurally blocked by parent sorry in isEmbeddable).
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

namespace Erdos1018OQ04Incomplete01.Aristotle

/-
  ## Section 1: Planarity Arithmetic

  Supporting arithmetic for the Euler formula bound |E| ≤ 3n - 6.
-/

-- K₃ has exactly 3 edges (n.choose 2 for n=3)
theorem K3_edgecount : Nat.choose 3 2 = 3 := by decide

-- K₄ has exactly 6 edges
theorem K4_edgecount : Nat.choose 4 2 = 6 := by decide

-- K₅ has exactly 10 edges
theorem K5_edgecount : Nat.choose 5 2 = 10 := by decide

-- K₃ meets the planar bound with equality: |E(K₃)| = 3·3 - 6
theorem K3_at_planar_bound : Nat.choose 3 2 = 3 * 3 - 6 := by decide

-- K₄ meets the planar bound with equality: |E(K₄)| = 3·4 - 6
theorem K4_at_planar_bound : Nat.choose 4 2 = 3 * 4 - 6 := by decide

-- K₅ exceeds the planar bound: |E(K₅)| = 10 > 9 = 3·5 - 6
theorem K5_exceeds_planar_bound : Nat.choose 5 2 > 3 * 5 - 6 := by decide

-- Planar bound is monotone
theorem planar_bound_mono (n m : ℕ) (h : n ≤ m) : 3 * n - 6 ≤ 3 * m - 6 := by omega

-- Planar bound is at most 3n
theorem planar_bound_le_3n (n : ℕ) : 3 * n - 6 ≤ 3 * n := by omega

-- For n ≥ 3, 3n > 6
theorem three_n_gt_6 (n : ℕ) (hn : n ≥ 3) : 3 * n > 6 := by omega

-- For n ≥ 3, 3n - 6 ≥ n
theorem planar_bound_ge_n (n : ℕ) (hn : n ≥ 3) : 3 * n - 6 ≥ n := by omega

-- n.choose 2 = n * (n - 1) / 2 for n ≥ 1
theorem choose_2_formula (n : ℕ) (hn : n ≥ 1) : n.choose 2 * 2 = n * (n - 1) := by
  sorry

-- Planar graphs on n ≥ 6 vertices have < n² / 3 edges (from 3n - 6 < n²/3)
theorem planar_bound_lt_sq_div (n : ℕ) (hn : n ≥ 6) : 3 * (3 * n - 6) < n ^ 2 := by
  sorry

-- n² > 3n for n ≥ 4
theorem sq_gt_3n (n : ℕ) (hn : n ≥ 4) : n ^ 2 > 3 * n := by
  sorry

-- n² > 3n - 6 for n ≥ 3
theorem sq_gt_planar_bound (n : ℕ) (hn : n ≥ 3) : n ^ 2 > 3 * n - 6 := by
  sorry

/-
  ## Section 2: Convex Hull Basics in ℝ²

  Basic membership and inclusion facts about convex hulls of finite point sets.
-/

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

-- Singleton is contained in its convex hull
theorem singleton_subset_convexHull (p : E) :
    ({p} : Set E) ⊆ convexHull ℝ {p} := by
  exact subset_convexHull ℝ _

-- Every point is in the convex hull of a set containing it
theorem mem_convexHull_self {S : Set E} {p : E} (hp : p ∈ S) : p ∈ convexHull ℝ S := by
  exact subset_convexHull ℝ S hp

-- Convex hull is monotone: S ⊆ T → convexHull S ⊆ convexHull T
theorem convexHull_mono_subset {S T : Set E} (h : S ⊆ T) :
    convexHull ℝ S ⊆ convexHull ℝ T := convexHull_mono h

-- Intersection of convex hulls is contained in convex hull of the union
theorem convexHull_inter_subset_union {S T : Set E} :
    convexHull ℝ S ∩ convexHull ℝ T ⊆ convexHull ℝ (S ∪ T) := by
  sorry

-- If S ⊆ T, then convexHull S ∩ convexHull T = convexHull S
theorem convexHull_inter_of_subset {S T : Set E} (h : S ⊆ T) :
    convexHull ℝ S ∩ convexHull ℝ T = convexHull ℝ S := by
  sorry

-- Convex hull of a two-element set in ℝ² is a line segment
theorem convexHull_pair_eq_segment (p q : Fin 2 → ℝ) :
    convexHull ℝ ({p, q} : Set (Fin 2 → ℝ)) =
    {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (1 - t) • p + t • q} := by
  sorry

/-
  ## Section 3: Zero-Padding Linear Injection

  Supporting lemmas for the dimension-monotonicity proof (embeddable_mono).
-/

-- Zero-padding preserves vector at original coordinates
theorem zeropad_proj (d d' : ℕ) (hdd : d ≤ d') (x : Fin d → ℝ) (i : Fin d) :
    let ι : (Fin d → ℝ) → (Fin d' → ℝ) := fun a j => if h : j.val < d then a ⟨j.val, h⟩ else 0
    ι x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hdd⟩ = x i := by
  simp [i.isLt]

-- Zero-padding maps zero to zero
theorem zeropad_zero (d d' : ℕ) :
    let ι : (Fin d → ℝ) → (Fin d' → ℝ) := fun a j => if h : j.val < d then a ⟨j.val, h⟩ else 0
    ι 0 = 0 := by
  ext i; simp

-- Zero-padding maps addition to addition
theorem zeropad_add (d d' : ℕ) (x y : Fin d → ℝ) :
    let ι : (Fin d → ℝ) → (Fin d' → ℝ) := fun a j => if h : j.val < d then a ⟨j.val, h⟩ else 0
    ι (x + y) = ι x + ι y := by
  ext i; simp [Pi.add_apply]; split_ifs <;> simp

-- Zero-padding maps scalar multiplication to scalar multiplication
theorem zeropad_smul (d d' : ℕ) (r : ℝ) (x : Fin d → ℝ) :
    let ι : (Fin d → ℝ) → (Fin d' → ℝ) := fun a j => if h : j.val < d then a ⟨j.val, h⟩ else 0
    ι (r • x) = r • ι x := by
  ext i; simp [Pi.smul_apply]; split_ifs <;> simp [smul_zero]

end Erdos1018OQ04Incomplete01.Aristotle
