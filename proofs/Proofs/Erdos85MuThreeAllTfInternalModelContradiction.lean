import Proofs.Erdos85MuThreeAllTfExteriorHitAssembly
import Proofs.Erdos85BinarySquareMuThreeExteriorGrid

/-! # Any order-64 all-TF internal coordinate model is impossible -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem false_of_orderSixtyFour_mu3AllTf_internalModel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
      s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (shape : Mu3AllTfShape)
    (model : Mu3InternalCoordinateModel (G.induce c.supp)
      {z : V // z ∈ c.supp ∧ s z = 1}
      {z : V // z ∈ c.supp ∧ s z = -1}
      (fun p => ⟨p.1, p.2.1⟩) (fun n => ⟨n.1, n.2.1⟩) shape)
    (houtExt : ∀ u : {u : V // u ∉ c.supp},
      (Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
        G.Adj u.1 v.1).card = 6)
    (hP : Fintype.card {z : V // z ∈ c.supp ∧ s z = 1} = 8)
    (hN : Fintype.card {z : V // z ∈ c.supp ∧ s z = -1} = 8)
    (hallTf : ∀ p : {z : V // z ∈ c.supp ∧ s z = 1},
      ∀ n : {z : V // z ∈ c.supp ∧ s z = -1},
        G.Adj p.1 n.1 → (triangleFreeEdgeGraph G).Adj p.1 n.1) : False := by
  classical
  obtain ⟨label, hlabel, hadj⟩ :=
    orderSixtyFour_signedSizeTwo_muThree_exterior_gridEmbedding
      G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
  have hcardExt : Fintype.card {u : V // u ∉ c.supp} = 48 :=
    orderSixtyFour_sizeTwoComponent_exterior_card G hcardV c hc
  let modelAmbient : Mu3InternalCoordinateModel G
      {z : V // z ∈ c.supp ∧ s z = 1}
      {z : V // z ∈ c.supp ∧ s z = -1}
      Subtype.val Subtype.val shape :=
    { row := model.row
      column := model.column
      hole_iff := fun p n => model.hole_iff p n }
  let e : Fin 48 ≃ {u : V // u ∉ c.supp} :=
    mu3ExteriorEquivOfInternalCoordinateModel
      G Subtype.val Subtype.val shape modelAmbient label hlabel
      (fun u => u.1) hadj hallTf hcardExt
  have hcoord : ∀ i,
      (model.row (label (e i)).1).val * 8 +
          (model.column (label (e i)).2).val =
        (mu3AllTfCells shape).getD i.val 0 := by
    intro i
    let coord := mu3ExteriorOccupiedCoord
      G Subtype.val Subtype.val shape modelAmbient label
      (fun u => u.1) hadj hallTf
    have hinj := mu3ExteriorOccupiedCoord_injective
      G Subtype.val Subtype.val shape modelAmbient label hlabel
      (fun u => u.1) hadj hallTf
    have hbij := mu3CoordinateBijection_of_injective shape hcardExt coord hinj
    have heq := mu3ExteriorEquivOfCoordinateBijection_coord shape coord hbij i
    change coord (e i) = mu3AllTfShapeCellEquiv shape i at heq
    have hval := congrArg (fun z => z.1) heq
    rw [mu3AllTfShapeCellEquiv_val shape i] at hval
    exact hval
  have hpositive : ∀ u,
      (Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
          G.Adj u.1 v.1).image (fun v => (label v).1) =
        Finset.univ.filter fun p : {z : V // z ∈ c.supp ∧ s z = 1} =>
          ¬ G.Adj p.1 (label u).2.1 := by
    intro u
    have hforbidden :=
      orderSixtyFour_signedSizeTwo_negative_positiveNeighborCard_two
        G hfree hreg hcardV c hc s hs_in hs_out hA_in
        (label u).2.1 (label u).2.2.1 (label u).2.2.2
    exact c4Free_exteriorGridLabel_positiveHit_image
      G hfree c s label hadj u (houtExt u) hP hforbidden
  have hnegative : ∀ u,
      (Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
          G.Adj u.1 v.1).image (fun v => (label v).2) =
        Finset.univ.filter fun n : {z : V // z ∈ c.supp ∧ s z = -1} =>
          ¬ G.Adj n.1 (label u).1.1 := by
    intro u
    have hforbidden :=
      orderSixtyFour_signedSizeTwo_positive_negativeNeighborCard_two
        G hfree hreg hcardV c hc s hs_in hs_out hA_in
        (label u).1.1 (label u).1.2.1 (label u).1.2.2
    exact c4Free_exteriorGridLabel_negativeHit_image
      G hfree c s label hadj u (houtExt u) hN hforbidden
  let hits := mu3ExteriorHitImages_of_ambient_signed_images
    G hfree c s shape label hadj model e hcoord hpositive hnegative
  exact false_of_c4Free_mu3AllTf_ambientHitImages G hfree c shape e hits

#print axioms false_of_orderSixtyFour_mu3AllTf_internalModel

end

end Erdos85
