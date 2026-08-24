import Proofs.Erdos85PureEndpointPrivateCollisionHalfOccupancy
import Proofs.Erdos85ExteriorDefectDecomposition

/-!
# Unused full-center owners are defect neighbors

If a center has its entire graph neighborhood on a shore `S`, then every
common neighbor that it shares with a vertex `w` lies on `S`.  Consequently
the center is a second-order defect neighbor of `w` exactly when it owns none
of the shore neighbors of `w`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- For a center whose whole neighborhood lies on `S`, absence from all owner
sets around `w` is equivalent to second-order defect adjacency to `w`. -/
theorem c4Free_fullCenter_defectAdj_iff_unusedOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (S : Finset V) {q : ℕ}
    {w i : V} (hwi : w ≠ i) (hiFull : i ∈ fullLineCenters G S q)
    (hregi : G.degree i = q) :
    (secondOrderDefectGraph G).Adj w i ↔
      ∀ y ∈ G.neighborFinset w ∩ S,
        i ∉ G.neighborFinset y := by
  classical
  have hiOcc : (G.neighborFinset i ∩ S).card = q :=
    (mem_fullLineCenters G S q i).mp hiFull
  have hiSubset : G.neighborFinset i ⊆ S := by
    have hiEq : G.neighborFinset i ∩ S = G.neighborFinset i := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hiOcc, G.card_neighborFinset_eq_degree, hregi]
    intro y hy
    have : y ∈ G.neighborFinset i ∩ S := by simpa [hiEq] using hy
    exact (Finset.mem_inter.mp this).2
  rw [secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree hwi]
  constructor
  · intro hzero y hyS hyi
    have hyw : y ∈ G.neighborFinset w := (Finset.mem_inter.mp hyS).1
    have hyi' : y ∈ G.neighborFinset i := by
      exact (G.mem_neighborFinset i y).mpr
        ((G.mem_neighborFinset y i).mp hyi).symm
    have hyCommon : y ∈ G.neighborFinset w ∩ G.neighborFinset i :=
      Finset.mem_inter.mpr ⟨hyw, hyi'⟩
    rw [Finset.card_eq_zero.mp hzero] at hyCommon
    simp at hyCommon
  · intro hunused
    apply Finset.card_eq_zero.mpr
    ext y
    constructor
    · intro hyCommon
      have hyw := (Finset.mem_inter.mp hyCommon).1
      have hyi := (Finset.mem_inter.mp hyCommon).2
      have hyS : y ∈ S := hiSubset hyi
      have hyOwner : i ∈ G.neighborFinset y :=
        (G.mem_neighborFinset y i).mpr
          ((G.mem_neighborFinset i y).mp hyi).symm
      exact (hunused y (Finset.mem_inter.mpr ⟨hyw, hyS⟩) hyOwner).elim
    · intro hyEmpty
      simp at hyEmpty

/-- The full-center defect neighbors of `w` are exactly the full centers
unused by every shore neighbor of `w`. -/
theorem c4Free_fullCenter_defectNeighbors_eq_unusedOwners
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (S : Finset V) {q : ℕ}
    (hreg : ∀ v, G.degree v = q) {w : V}
    (hwFull : w ∉ fullLineCenters G S q) :
    (secondOrderDefectGraph G).neighborFinset w ∩
        fullLineCenters G S q =
      (fullLineCenters G S q).filter fun i =>
        ∀ y ∈ G.neighborFinset w ∩ S,
          i ∉ G.neighborFinset y := by
  classical
  ext i
  constructor
  · intro hi
    have hiData := Finset.mem_inter.mp hi
    have hwiD := ((secondOrderDefectGraph G).mem_neighborFinset w i).mp hiData.1
    have hiFull := hiData.2
    apply Finset.mem_filter.mpr
    refine ⟨hiFull, ?_⟩
    have hne : w ≠ i := by
      intro h
      subst i
      exact hwFull hiFull
    exact (c4Free_fullCenter_defectAdj_iff_unusedOwner
      G hfree S hne hiFull (hreg i)).mp hwiD
  · intro hi
    have hiData := Finset.mem_filter.mp hi
    have hiFull := hiData.1
    have hiUnused := hiData.2
    apply Finset.mem_inter.mpr
    refine ⟨?_, hiFull⟩
    have hne : w ≠ i := by
      intro h
      subst i
      exact hwFull hiFull
    apply ((secondOrderDefectGraph G).mem_neighborFinset w i).mpr
    exact (c4Free_fullCenter_defectAdj_iff_unusedOwner
      G hfree S hne hiFull (hreg i)).mpr hiUnused

end

end Erdos85

#print axioms Erdos85.c4Free_fullCenter_defectAdj_iff_unusedOwner
#print axioms Erdos85.c4Free_fullCenter_defectNeighbors_eq_unusedOwners
