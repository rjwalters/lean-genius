import Proofs.Erdos85BinarySquareComponentAmbientSquareSpectrum
import Proofs.Erdos85ComponentSignFlipEigenvector
import Proofs.Erdos85SizeTwoMuNegOneRefinedSectorRouting
import Proofs.Erdos85SizeTwoMuNegThreeRefinedSectorRouting

/-! # Extending an induced signed joint eigenvector to its ambient component -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The ambient signed joint row identities expected by every size-two
signed-eigenvalue lane. -/
def IsAmbientSignedJoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (theta : ℤ) (s : V → ℤ) : Prop :=
  (∀ x, x ∉ c.supp → s x = 0) ∧
  (∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1) ∧
  (∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
    (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
      s y = -2 * s z) ∧
  (∀ z ∈ c.supp, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
    s y = theta * s z)

/-- A pointwise signed joint eigenvector for the ambient graph and defect
graph induced on one defect component extends by zero to exactly the ambient
row identities used by the neighboring signed-eigenvalue classifiers. -/
theorem exists_ambient_signedJoint_of_induced_signedJoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (t : c.supp → ℤ) (ht : ∀ x, t x = -1 ∨ t x = 1)
    (theta : ℤ)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec t = (-2 : ℤ) • t)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec t =
      theta • t) :
    ∃ s : V → ℤ,
      (∀ x, x ∉ c.supp → s x = 0) ∧
      (∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1) ∧
      (∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
        (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
          s y = -2 * s z) ∧
      (∀ z ∈ c.supp, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = theta * s z) := by
  classical
  let D := secondOrderDefectGraph G
  let s := connectedComponentExtend D c t
  have hrestrict : (fun x : c.supp ↦ s x.1) = t := by
    funext x
    simp [s, x.2]
  have hs_out : ∀ x, x ∉ c.supp → s x = 0 := by
    intro x hx
    simp [s, hx]
  have hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1 := by
    intro x hx
    simpa [s, hx] using ht ⟨x, hx⟩
  have hsH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ D.connectedComponentMk y = c), s y = -2 * s z := by
    intro z hz
    let zs : c.supp := ⟨z, hz⟩
    have hp := congrFun hH zs
    rw [← hrestrict] at hp
    rw [induce_adjMatrix_mulVec_restrict_apply G c.supp s zs] at hp
    simpa [D, s, hz, zs, ConnectedComponent.mem_supp_iff, smul_eq_mul] using hp
  have hsD : ∀ z ∈ c.supp, ∑ y ∈ D.neighborFinset z, s y = theta * s z := by
    intro z hz
    let zs : c.supp := ⟨z, hz⟩
    have hp := congrFun hD zs
    rw [← hrestrict] at hp
    change ((D.induce c.supp).adjMatrix ℤ).mulVec
      (fun x : c.supp ↦ s x.1) zs = _ at hp
    rw [induce_adjMatrix_mulVec_restrict_apply D c.supp s zs] at hp
    have hfilter : (D.neighborFinset z).filter (fun y ↦ y ∈ c.supp) =
        D.neighborFinset z := by
      apply Finset.filter_eq_self.mpr
      intro y hy
      exact c.mem_supp_of_adj_mem_supp hz ((D.mem_neighborFinset z y).mp hy)
    rw [hfilter] at hp
    simpa [s, hz, zs, smul_eq_mul] using hp
  exact ⟨s, hs_out, hs_in, by simpa [D] using hsH, by simpa [D] using hsD⟩

theorem exists_isAmbientSignedJoint_of_induced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (t : c.supp → ℤ) (ht : ∀ x, t x = -1 ∨ t x = 1)
    (theta : ℤ)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec t = (-2 : ℤ) • t)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec t =
      theta • t) :
    ∃ s, IsAmbientSignedJoint G c theta s := by
  simpa [IsAmbientSignedJoint] using
    exists_ambient_signedJoint_of_induced_signedJoint G c t ht theta hH hD

/-- A reduced μ=-1 switch is either its unique self cell, or already an
ambient signed witness in one of the three cross lanes. -/
theorem muNegOne_inducedSwitch_self_or_ambientCrossLane
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hcell : MuNegOnePostEndpointSectorCells N₁ N₂ k r)
    (t : c.supp → ℤ) (ht : ∀ x, t x = -1 ∨ t x = 1)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec t = (-2 : ℤ) • t)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec t =
      sizeTwoMuSwitchTarget (-1) k r • t) :
    (k = 1 ∧ r = 4) ∨
      (∃ s, IsAmbientSignedJoint G c (-5) s) ∨
      (∃ s, IsAmbientSignedJoint G c (-3) s) ∨
      (∃ s, IsAmbientSignedJoint G c 3 s) := by
  rcases muNegOne_postEndpoint_self_or_crossLane N₁ N₂ k r hcell with
    hself | h5 | h3 | hpos
  · exact Or.inl hself
  · right; left
    exact exists_isAmbientSignedJoint_of_induced G c t ht (-5) hH (by simpa [h5] using hD)
  · right; right; left
    exact exists_isAmbientSignedJoint_of_induced G c t ht (-3) hH (by simpa [h3] using hD)
  · right; right; right
    exact exists_isAmbientSignedJoint_of_induced G c t ht 3 hH (by simpa [hpos] using hD)

/-- The analogous cross-lane transport for the reduced μ=-3 table. -/
theorem muNegThree_inducedSwitch_self_or_ambientCrossLane
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hcell : MuNegThreePostMuOneSectorCells N₁ N₂ k r)
    (t : c.supp → ℤ) (ht : ∀ x, t x = -1 ∨ t x = 1)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec t = (-2 : ℤ) • t)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec t =
      sizeTwoMuSwitchTarget (-3) k r • t) :
    (k = 1 ∧ r = 2) ∨
      (∃ s, IsAmbientSignedJoint G c (-5) s) ∨
      (∃ s, IsAmbientSignedJoint G c (-1) s) ∨
      (∃ s, IsAmbientSignedJoint G c 3 s) := by
  rcases muNegThree_postMuOne_self_or_crossLane N₁ N₂ k r hcell with
    hself | h5 | h1 | hpos
  · exact Or.inl hself
  · right; left
    exact exists_isAmbientSignedJoint_of_induced G c t ht (-5) hH (by simpa [h5] using hD)
  · right; right; left
    exact exists_isAmbientSignedJoint_of_induced G c t ht (-1) hH (by simpa [h1] using hD)
  · right; right; right
    exact exists_isAmbientSignedJoint_of_induced G c t ht 3 hH (by simpa [hpos] using hD)

end

end Erdos85

#print axioms Erdos85.exists_ambient_signedJoint_of_induced_signedJoint
#print axioms Erdos85.exists_isAmbientSignedJoint_of_induced
#print axioms Erdos85.muNegOne_inducedSwitch_self_or_ambientCrossLane
#print axioms Erdos85.muNegThree_inducedSwitch_self_or_ambientCrossLane
