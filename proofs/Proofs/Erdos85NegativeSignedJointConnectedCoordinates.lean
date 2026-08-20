import Proofs.Erdos85MuThreeAllTfSixteenCoordinates
import Proofs.Erdos85MuThreeAllTfCycleShapeClassification

/-! # Connected negative signed-joint coordinates

The connected internal branch of an order-64 size-two signed joint has a
coordinate layer independent of its defect eigenvalue.  This file packages
that reusable layer: the internal two-factor is a sign-aligned `C16`, with
the same positive/negative coordinate model used by the older `mu = 3`
branch.  Exterior owner semantics are deliberately absent.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Stable coordinate package for the future connected negative owner model. -/
structure NegativeSignedJointConnectedCoordinates
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : Fin 64 → ℤ) where
  label : SixteenCycleLabeling (G.induce c.supp)
  model : Mu3InternalCoordinateModel (G.induce c.supp)
    {x : c.supp // s x.1 = 1} {x : c.supp // s x.1 = -1}
    Subtype.val Subtype.val .c16

/-- A connected size-two signed joint canonically supplies its sign-aligned
`C16` coordinate package.  No defect eigenvalue or exterior hypothesis is
used. -/
theorem exists_negativeSignedJointConnectedCoordinates
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 16)
    (hconn : (G.induce c.supp).Connected)
    (s : Fin 64 → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z) :
    Nonempty (NegativeSignedJointConnectedCoordinates G c s) := by
  classical
  let H := G.induce c.supp
  let t : c.supp → ℤ := fun z ↦ s z.1
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by norm_num
  have hdeg : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) (by simpa using hc) z
  have hsign : ∀ z, t z = -1 ∨ t z = 1 := by
    intro z
    exact hs_in z.1 z.2
  have hA_in : ∀ z ∈ c.supp,
      ∑ y ∈ G.neighborFinset z, s y = -2 * s z := by
    intro z hz
    rw [← hH z hz]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y hy hyout
    have hyc : y ∉ c.supp := by
      intro hyin
      apply hyout
      exact Finset.mem_filter.mpr ⟨hy,
        (ConnectedComponent.mem_supp_iff c y).mp hyin⟩
    simp [hs_out y hyc]
  have hneighborSum : ∀ z, ∑ w ∈ H.neighborFinset z, t w = -2 * t z := by
    intro z
    rw [← SimpleGraph.adjMatrix_mulVec_apply]
    rw [← adjMatrix_mulVec_eq_induce_mulVec_of_support_int
      G c.supp s hs_out z]
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    exact hA_in z.1 z.2
  have hflip : ∀ (z w : c.supp), H.Adj z w → t z = -t w :=
    signedFlip_of_degree_two_neighborSum H hdeg t hsign hneighborSum
  obtain ⟨z, hz⟩ := c.nonempty_supp
  let zs : c.supp := ⟨z, hz⟩
  let a := H.connectedComponentMk zs
  have hspan : ∀ w : c.supp, w ∈ a.supp := by
    intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact ConnectedComponent.sound (hconn.preconnected w zs)
  have ha : a.supp.ncard = 16 := by
    rw [show a.supp = Set.univ by ext w; simp [hspan w]]
    calc
      Set.univ.ncard = Nat.card c.supp := Set.ncard_univ c.supp
      _ = c.supp.ncard := Nat.card_coe_set_eq c.supp
      _ = 16 := hc
  let label : SixteenCycleLabeling H :=
    Classical.choice
      (exists_sixteenCycleLabeling_of_spanning_component H hdeg a ha hspan)
  let model := sixteenInternalCoordinateModel H label t hsign hflip
  exact ⟨⟨label, model⟩⟩

end

end Erdos85

#print axioms Erdos85.exists_negativeSignedJointConnectedCoordinates
