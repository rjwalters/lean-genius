import Proofs.Erdos85MuThreeAllTfInternalModelContradiction
import Proofs.Erdos85BinarySquareMuThreeExteriorGrid

/-! # Order-64 subtype-cardinality wrappers for the all-TF capstone -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem orderSixtyFour_signedSizeTwo_positive_subtype_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0) :
    Fintype.card {z : V // z ∈ c.supp ∧ s z = 1} = 8 := by
  have h := (orderSixtyFour_signedSizeTwo_signClass_cards
    G c hc s hs_in hs_out hsum).1
  rw [Fintype.card_subtype]
  rw [show (Finset.univ.filter fun z : V => z ∈ c.supp ∧ s z = 1) =
      (Finset.univ.filter fun z : V => z ∈ c.supp).filter
        (fun z => s z = 1) by
    ext z
    simp]
  exact h

theorem orderSixtyFour_signedSizeTwo_negative_subtype_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0) :
    Fintype.card {z : V // z ∈ c.supp ∧ s z = -1} = 8 := by
  have h := (orderSixtyFour_signedSizeTwo_signClass_cards
    G c hc s hs_in hs_out hsum).2
  rw [Fintype.card_subtype]
  rw [show (Finset.univ.filter fun z : V => z ∈ c.supp ∧ s z = -1) =
      (Finset.univ.filter fun z : V => z ∈ c.supp).filter
        (fun z => s z = -1) by
    ext z
    simp]
  exact h

def outsideNeighborSubtypeEquiv
    {V : Type*} (G : SimpleGraph V) (S : Set V) (u : V) :
    {v : {v : V // v ∉ S} // G.Adj u v.1} ≃
      {v : V // G.Adj u v ∧ v ∉ S} where
  toFun v := ⟨v.1.1, v.2, v.1.2⟩
  invFun v := ⟨⟨v.1, v.2.2⟩, v.2.1⟩
  left_inv v := by rfl
  right_inv v := by rfl

theorem orderSixtyFour_sizeTwoComponent_outside_subtype_neighborCard_six
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
    (u : {u : V // u ∉ c.supp}) :
    (Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
      G.Adj u.1 v.1).card = 6 := by
  have hout := binarySquare_regular_sizeTwoComponent_outsideNeighborCard
    G hfree (q := 8) (by norm_num) hreg hcardV c hc u.1 u.2
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr
    (outsideNeighborSubtypeEquiv G c.supp u.1)]
  rw [Fintype.card_subtype]
  change (Finset.univ.filter fun v : V => G.Adj u.1 v ∧ v ∉ c.supp).card = 6
  rw [show (Finset.univ.filter fun v : V => G.Adj u.1 v ∧ v ∉ c.supp) =
      (G.neighborFinset u.1).filter (fun v => v ∉ c.supp) by
    ext v
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]]
  simpa using hout

#print axioms orderSixtyFour_sizeTwoComponent_outside_subtype_neighborCard_six

end

end Erdos85
