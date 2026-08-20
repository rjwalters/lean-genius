import Proofs.Erdos85C4FreeRegularAdjacencyCube

/-! # Entrywise cubic adjacency values on a labeled eight-cycle -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def eightCycleCubeValue (i j : ZMod 8) : ℕ :=
  (({i - 1, i + 1} : Finset (ZMod 8)) ∩ {j - 2, j}).card +
    (({i - 1, i + 1} : Finset (ZMod 8)) ∩ {j, j + 2}).card

theorem eightCycleCubeValue_eq (i j : ZMod 8) :
    eightCycleCubeValue i j =
      if j = i - 1 ∨ j = i + 1 then 3
      else if j = i - 3 ∨ j = i + 3 then 1 else 0 := by
  revert i j
  native_decide

/-- A first entrywise reduction: a cubic walk ending at cycle coordinate `j`
must make its penultimate stop at `j-1` or `j+1`. -/
theorem eightCycle_adjMatrix_cube_apply_eq_two_commonCards
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (i j : ZMod 8) :
    (H.adjMatrix ℤ * H.adjMatrix ℤ * H.adjMatrix ℤ) (u i) (u j) =
      ((H.neighborFinset (u i) ∩ H.neighborFinset (u (j - 1))).card : ℤ) +
      ((H.neighborFinset (u i) ∩ H.neighborFinset (u (j + 1))).card : ℤ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [SimpleGraph.adjMatrix_apply, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun k => H.Adj k (u j)) =
      H.neighborFinset (u j) := by
    ext k
    simp [SimpleGraph.mem_neighborFinset, H.adj_comm]
  rw [hfilter, hu j]
  have hentry : ∀ k,
      (H.adjMatrix ℤ * H.adjMatrix ℤ) (u i) k =
        ((H.neighborFinset (u i) ∩ H.neighborFinset k).card : ℤ) := by
    intro k
    exact adjMatrix_sq_apply_eq_card_common H (u i) k
  have hcoord : j - 1 ≠ j + 1 := by
    intro hz
    have hz' : (-1 : ZMod 8) = 1 := by
      apply add_left_cancel (a := j)
      simpa [sub_eq_add_neg] using hz
    exact (by native_decide : (-1 : ZMod 8) ≠ 1) hz'
  have hne : u (j - 1) ≠ u (j + 1) := huinj.ne hcoord
  simp [hentry, hne]

theorem eightCycle_adjMatrix_cube_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (i j : ZMod 8) :
    (H.adjMatrix ℤ * H.adjMatrix ℤ * H.adjMatrix ℤ) (u i) (u j) =
      if j = i - 1 ∨ j = i + 1 then 3
      else if j = i - 3 ∨ j = i + 3 then 1 else 0 := by
  rw [eightCycle_adjMatrix_cube_apply_eq_two_commonCards H u huinj hu i j]
  rw [hu i, hu (j - 1), hu (j + 1)]
  have hpair (a b : ZMod 8) :
      ({u a, u b} : Finset V) = ({a, b} : Finset (ZMod 8)).image u := by
    ext x
    simp
  have hcardImageInter (s t : Finset (ZMod 8)) :
      (s.image u ∩ t.image u).card = (s ∩ t).card := by
    rw [← Finset.image_inter s t huinj,
      Finset.card_image_of_injective _ huinj]
  have hjm : j - 1 - 1 = j - 2 := by ring
  have hjp : j + 1 + 1 = j + 2 := by ring
  have hj0 : j - 1 + 1 = j := by ring
  have hj0' : j + 1 - 1 = j := by ring
  have hcoordinate :
      ((({u (i - 1), u (i + 1)} : Finset V) ∩
          {u (j - 1 - 1), u (j - 1 + 1)}).card : ℤ) +
        ((({u (i - 1), u (i + 1)} : Finset V) ∩
          {u (j + 1 - 1), u (j + 1 + 1)}).card : ℤ) =
        (eightCycleCubeValue i j : ℤ) := by
    rw [hjm, hjp, hj0, hj0']
    simp_rw [hpair]
    rw [hcardImageInter, hcardImageInter]
    rfl
  rw [hcoordinate, eightCycleCubeValue_eq]
  split_ifs <;> norm_num

end

end Erdos85

#print axioms Erdos85.eightCycle_adjMatrix_cube_apply_eq_two_commonCards
#print axioms Erdos85.eightCycle_adjMatrix_cube_apply
