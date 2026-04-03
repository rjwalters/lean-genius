/-
  Aristotle targets for Erdős Problem #612
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos612Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the diameter bounds (diameter is def-sorry)
  - NOT theorems from axiomatized bounds
  - Routine facts about K_r-free graphs, triangles, and coefficient formulas
  - No definition sorries
  - No axioms

  Included targets (5):
  - isKFree_empty: empty graph is K_r-free for any r ≥ 3 (vacuously)
  - triangleFree_of_kFree: K_3-free implies triangle-free
  - isKFree_of_larger: K_{r+1}-free implies K_r-free (upward)
  - upper_coeff_pos: upperCoeff k > 0 for k ≥ 4
  - lower_coeff_pos: lowerCoeff k > 0 for k ≥ 4
-/
import Mathlib

namespace Erdos612Aristotle

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsKFree (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ S : Finset V, S.card = r → ¬(∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)

def IsTriangleFree (G : SimpleGraph V) : Prop := IsKFree G 3

noncomputable def upperCoeff (k : ℕ) : ℝ := 2 / Real.log (k - 2)

noncomputable def lowerCoeff (k : ℕ) : ℝ := 1 / (4 * Real.log k)

-- Routine: K_3-free is the same as triangle-free.
-- By definition, IsTriangleFree G = IsKFree G 3.
theorem triangleFree_iff_K3free (G : SimpleGraph V) :
    IsTriangleFree G ↔ IsKFree G 3 := by
  sorry

-- Routine: If G has no K_{r+1}, then it has no K_r+1 restricted to r+1 vertices.
-- This is just unfolding the definition.
theorem isKFree_subset (G : SimpleGraph V) (r : ℕ) (S T : Finset V)
    (hT : S ⊆ T) (hG : IsKFree G T.card) :
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v → False := by
  sorry

-- Routine: lowerCoeff k > 0 for k ≥ 4.
-- 1 / (4 * log k) > 0 since log k > 0 for k ≥ 4.
theorem lowerCoeff_pos (k : ℕ) (hk : k ≥ 4) : lowerCoeff k > 0 := by
  sorry

-- Routine: upperCoeff k > 0 for k ≥ 4.
-- 2 / log(k-2) > 0 since log(k-2) > 0 for k-2 ≥ 2.
theorem upperCoeff_pos (k : ℕ) (hk : k ≥ 4) : upperCoeff k > 0 := by
  sorry

-- Routine: lowerCoeff k ≤ upperCoeff k for k ≥ 4.
-- Since 1/(4 log k) ≤ 2/log(k-2) for large k.
theorem lowerCoeff_le_upperCoeff (k : ℕ) (hk : k ≥ 4) :
    lowerCoeff k ≤ upperCoeff k := by
  sorry

end Erdos612Aristotle
