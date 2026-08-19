import Proofs.Erdos85BinarySquareSizeTwoJointEigenvectorMuOneExclusion
import Proofs.Erdos85BinarySquareSizeTwoMuNegativeSevenExclusion
import Proofs.Erdos85BinarySquareComponentAmbientSquareSpectrum
import Proofs.Erdos85ComponentSignFlipEigenvector

/-! # Excluding switched joint eigenvectors on a size-two component -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An integral signed joint eigenvector on the induced component with defect
eigenvalue `1` contradicts the order-64 size-two exclusion. -/
theorem orderSixtyFour_sizeTwoPart_inducedSignedJointEigenvector_muOne_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (t : c.supp → ℤ)
    (ht : ∀ x, t x = -1 ∨ t x = 1)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec t = (-2 : ℤ) • t)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec t =
      (1 : ℤ) • t) :
    False := by
  classical
  let D := secondOrderDefectGraph G
  let s := connectedComponentExtend D c t
  have hs_out : ∀ x, x ∉ c.supp → s x = 0 := by
    intro x hx
    simp [s, hx]
  have hs_in : ∀ x, x ∈ c.supp → s x = 1 ∨ s x = -1 := by
    intro x hx
    rw [show s x = t ⟨x, hx⟩ by simp [s, hx]]
    rcases ht ⟨x, hx⟩ with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hrestrict : (fun x : c.supp ↦ s x.1) = t := by
    funext x
    simp [s, x.2]
  have hsH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ D.connectedComponentMk y = c), s y = -2 * s z := by
    intro z hz
    let zs : c.supp := ⟨z, hz⟩
    have hp := congrFun hH zs
    rw [← hrestrict] at hp
    rw [induce_adjMatrix_mulVec_restrict_apply G c.supp s zs] at hp
    simpa [D, s, connectedComponentExtend, hz, zs,
      ConnectedComponent.mem_supp_iff, smul_eq_mul] using hp
  have hsD : ∀ z ∈ c.supp, ∑ y ∈ D.neighborFinset z, s y = s z := by
    intro z hz
    let zs : c.supp := ⟨z, hz⟩
    have hp := congrFun hD zs
    rw [← hrestrict] at hp
    change ((D.induce c.supp).adjMatrix ℤ).mulVec (fun x : c.supp ↦ s x.1) zs = _ at hp
    rw [induce_adjMatrix_mulVec_restrict_apply D c.supp s zs] at hp
    have hfilter : (D.neighborFinset z).filter (fun y ↦ y ∈ c.supp) =
        D.neighborFinset z := by
      apply Finset.filter_eq_self.mpr
      intro y hy
      exact c.mem_supp_of_adj_mem_supp hz ((D.mem_neighborFinset z y).mp hy)
    rw [hfilter] at hp
    simpa [s, connectedComponentExtend, hz, zs, smul_eq_mul] using hp
  exact orderSixtyFour_sizeTwoPart_signedJointEigenvector_muOne_false
    G hfree hreg hcard c hc s hs_out hs_in
      (by simpa [D] using hsH) (by simpa [D] using hsD)

/-- The analogous induced signed eigenvector at the negative defect endpoint
also contradicts the existing size-two bipartite exclusion. -/
theorem orderSixtyFour_sizeTwoPart_inducedSignedEigenvector_muNegativeSeven_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (hother : ∀ c' : (secondOrderDefectGraph G).ConnectedComponent,
      c' ≠ c → c'.supp.ncard ≠ 8)
    (t : c.supp → ℤ) (ht : ∀ x, t x = -1 ∨ t x = 1)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec t =
      (-7 : ℤ) • t) :
    False := by
  classical
  let D := secondOrderDefectGraph G
  let s := connectedComponentExtend D c t
  have hrestrict : (fun x : c.supp ↦ s x.1) = t := by
    funext x
    simp [s, x.2]
  have hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1 := by
    intro x hx
    simpa [s, hx] using ht ⟨x, hx⟩
  have hsD : ∀ z ∈ c.supp, ∑ y ∈ D.neighborFinset z, s y = -7 * s z := by
    intro z hz
    let zs : c.supp := ⟨z, hz⟩
    have hp := congrFun hD zs
    rw [← hrestrict] at hp
    change ((D.induce c.supp).adjMatrix ℤ).mulVec (fun x : c.supp ↦ s x.1) zs = _ at hp
    rw [induce_adjMatrix_mulVec_restrict_apply D c.supp s zs] at hp
    have hfilter : (D.neighborFinset z).filter (fun y ↦ y ∈ c.supp) =
        D.neighborFinset z := by
      apply Finset.filter_eq_self.mpr
      intro y hy
      exact c.mem_supp_of_adj_mem_supp hz ((D.mem_neighborFinset z y).mp hy)
    rw [hfilter] at hp
    simpa [s, hz, zs, smul_eq_mul] using hp
  exact orderSixtyFour_sizeTwoPart_signedJointEigenvector_muNegativeSeven_false
    G hfree hreg hcard c hc hother s hs_in (by simpa [D] using hsD)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwoPart_inducedSignedJointEigenvector_muOne_false
#print axioms Erdos85.orderSixtyFour_sizeTwoPart_inducedSignedEigenvector_muNegativeSeven_false
