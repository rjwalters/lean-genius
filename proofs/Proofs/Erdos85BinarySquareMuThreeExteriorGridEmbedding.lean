import Proofs.Erdos85BinarySquareMuThreeExteriorGrid
import Proofs.Erdos85BinarySquareMuThreeExteriorSignedPair

/-! # The global exterior grid embedding in the `mu = 3` branch

The pointwise balanced-pair result canonically places each exterior vertex in
a positive-by-negative cell.  C4-freeness makes this placement injective.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A zero-sum finite family taking only the values `-1,1` has equally many
entries of each sign, and each sign class occupies half the family. -/
theorem signedFinset_zeroSum_filter_cards
    {V : Type*} [DecidableEq V] (S : Finset V) (s : V → ℤ)
    (hsign : ∀ x ∈ S, s x = -1 ∨ s x = 1)
    (hsum : ∑ x ∈ S, s x = 0) :
    (S.filter fun x => s x = 1).card =
        (S.filter fun x => s x = -1).card ∧
      S.card = 2 * (S.filter fun x => s x = 1).card := by
  let w : V → ℤ := fun x => 2 * s x
  have hlevels : ∀ x ∈ S, w x = -2 ∨ w x = 0 ∨ w x = 2 := by
    intro x hx
    rcases hsign x hx with h | h
    · left
      simp [w, h]
    · right; right
      simp [w, h]
  have hwsum : ∑ x ∈ S, w x = 0 := by
    calc
      ∑ x ∈ S, w x = 2 * ∑ x ∈ S, s x := by
        simp only [w, Finset.mul_sum]
      _ = 0 := by rw [hsum, mul_zero]
  obtain ⟨hbal, hsupp⟩ :=
    threeLevel_zeroSum_support_balance S w hlevels hwsum
  have hP : (S.filter fun x => w x = 2) = S.filter fun x => s x = 1 := by
    ext x
    by_cases hx : x ∈ S
    · rcases hsign x hx with h | h <;> simp [w, hx, h]
    · simp [hx]
  have hN : (S.filter fun x => w x = -2) = S.filter fun x => s x = -1 := by
    ext x
    by_cases hx : x ∈ S
    · rcases hsign x hx with h | h <;> simp [w, hx, h]
    · simp [hx]
  have hSupp : (S.filter fun x => w x ≠ 0) = S := by
    ext x
    by_cases hx : x ∈ S
    · rcases hsign x hx with h | h <;> simp [w, hx, h]
    · simp [hx]
  rw [hP, hN] at hbal
  rw [hSupp, hP] at hsupp
  exact ⟨hbal, hsupp⟩

/-- Every exterior vertex in the order-64 `mu = 3` branch embeds injectively
into the product of the positive and negative signed vertices of the size-two
component.  Both coordinates are actual ambient neighbours of the exterior
vertex. -/
theorem orderSixtyFour_signedSizeTwo_muThree_exterior_gridEmbedding
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
      (G.adjMatrix ℤ).mulVec s x = 2) :
    ∃ label : {u : V // u ∉ c.supp} →
        {z : V // z ∈ c.supp ∧ s z = 1} ×
          {z : V // z ∈ c.supp ∧ s z = -1},
      Function.Injective label ∧
      ∀ u, G.Adj u.1 (label u).1.1 ∧ G.Adj u.1 (label u).2.1 := by
  classical
  have hex : ∀ u : {u : V // u ∉ c.supp}, ∃ z z' : V,
      G.Adj u.1 z ∧ G.Adj u.1 z' ∧ z ∈ c.supp ∧ z' ∈ c.supp ∧
      s z = 1 ∧ s z' = -1 ∧ z ≠ z' ∧
      ∀ y, G.Adj u.1 y → y ∈ c.supp → y = z ∨ y = z' := by
    intro u
    exact orderSixtyFour_signedSizeTwo_muThree_exterior_signedPair
      G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out u.1 u.2
  choose zp zn huzp huzn hzpc hznc hsp hsn hpne hexhaust using hex
  let label : {u : V // u ∉ c.supp} →
      {z : V // z ∈ c.supp ∧ s z = 1} ×
        {z : V // z ∈ c.supp ∧ s z = -1} := fun u ↦
    (⟨zp u, hzpc u, hsp u⟩, ⟨zn u, hznc u, hsn u⟩)
  refine ⟨label, ?_, ?_⟩
  · intro u v huv
    have hp : zp u = zp v := by
      exact congrArg (fun w => w.1.1) huv
    have hn : zn u = zn v := by
      exact congrArg (fun w => w.2.1) huv
    apply Subtype.ext
    apply c4Free_commonNeighborPair_injective G hfree (hpne u)
    · exact (huzp u).symm
    · simpa [hp] using (huzp v).symm
    · exact (huzn u).symm
    · simpa [hn] using (huzn v).symm
  · intro u
    exact ⟨huzp u, huzn u⟩

/-- **Rook/partial-permutation law.**  For any exterior grid labeling whose
two coordinates are actual neighbours, the positive and negative coordinate
projections are each injective on the exterior neighbourhood of every cell.
This is the essential `C₄`-sensitive constraint: two different neighbours
cannot agree in a row or in a column. -/
theorem c4Free_exteriorGridLabel_neighbor_coordinate_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (label : {u : V // u ∉ c.supp} →
      {z : V // z ∈ c.supp ∧ s z = 1} ×
        {z : V // z ∈ c.supp ∧ s z = -1})
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (u : {u : V // u ∉ c.supp}) :
    Function.Injective (fun v : {v : {v : V // v ∉ c.supp} //
        G.Adj u.1 (v : V)} => (label v.1).1) ∧
      Function.Injective (fun v : {v : {v : V // v ∉ c.supp} //
        G.Adj u.1 (v : V)} => (label v.1).2) := by
  constructor
  · intro v w hvw
    change (label v.1).1 = (label w.1).1 at hvw
    let p := (label v.1).1
    have hpu : p.1 ≠ u.1 := by
      intro h
      exact u.2 (h ▸ p.2.1)
    have hpv : G.Adj p.1 v.1.1 := (hadj v.1).1.symm
    have hpw : G.Adj p.1 w.1.1 := by
      change G.Adj (label v.1).1.1 w.1.1
      rw [hvw]
      exact (hadj w.1).1.symm
    have huv : G.Adj u.1 v.1.1 := v.2
    have huw : G.Adj u.1 w.1.1 := w.2
    have hvwval := c4Free_commonNeighborPair_injective
      G hfree hpu hpv hpw huv huw
    apply Subtype.ext
    exact Subtype.ext hvwval
  · intro v w hvw
    change (label v.1).2 = (label w.1).2 at hvw
    let n := (label v.1).2
    have hnu : n.1 ≠ u.1 := by
      intro h
      exact u.2 (h ▸ n.2.1)
    have hnv : G.Adj n.1 v.1.1 := (hadj v.1).2.symm
    have hnw : G.Adj n.1 w.1.1 := by
      change G.Adj (label v.1).2.1 w.1.1
      rw [hvw]
      exact (hadj w.1).2.symm
    have huv : G.Adj u.1 v.1.1 := v.2
    have huw : G.Adj u.1 w.1.1 := w.2
    have hvwval := c4Free_commonNeighborPair_injective
      G hfree hnu hnv hnw huv huw
    apply Subtype.ext
    exact Subtype.ext hvwval

/-- The signed size-two component supplies exactly eight grid rows and eight
grid columns. -/
theorem orderSixtyFour_signedSizeTwo_signClass_cards
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0) :
    ((Finset.univ.filter fun x => x ∈ c.supp).filter fun x => s x = 1).card = 8 ∧
      ((Finset.univ.filter fun x => x ∈ c.supp).filter fun x => s x = -1).card = 8 := by
  let S := Finset.univ.filter fun x => x ∈ c.supp
  have hScard : S.card = 16 := by
    change (Finset.univ.filter fun x => x ∈ c.supp).card = 16
    rw [show (Finset.univ.filter fun x => x ∈ c.supp).card = c.supp.ncard by
      have heq : (Finset.univ.filter fun x => x ∈ c.supp) =
          c.supp.toFinite.toFinset := by
        ext x
        simp
      rw [heq, Set.ncard_eq_toFinset_card]]
    norm_num at hc ⊢
    exact hc
  have hSsum : ∑ x ∈ S, s x = 0 := by
    have hout : ∑ x ∈ Finset.univ.filter (fun x => x ∉ c.supp), s x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hs_out x (Finset.mem_filter.mp hx).2
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => x ∈ c.supp) s
    change (∑ x ∈ S, s x) +
      ∑ x ∈ Finset.univ.filter (fun x => x ∉ c.supp), s x = ∑ x, s x at hsplit
    rw [hout, add_zero, hsum] at hsplit
    exact hsplit
  have hsignS : ∀ x ∈ S, s x = -1 ∨ s x = 1 := by
    intro x hx
    exact hs_in x (Finset.mem_filter.mp hx).2
  obtain ⟨hbal, hhalf⟩ := signedFinset_zeroSum_filter_cards S s hsignS hSsum
  change (S.filter fun x => s x = 1).card = 8 ∧
    (S.filter fun x => s x = -1).card = 8
  omega

/-- A size-two component at order 64 has exactly 48 exterior vertices. -/
theorem orderSixtyFour_sizeTwoComponent_exterior_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) :
    Fintype.card {u : V // u ∉ c.supp} = 48 := by
  have hins : Fintype.card {u : V // u ∈ c.supp} = 16 := by
    rw [show Fintype.card {u : V // u ∈ c.supp} = c.supp.ncard by
      simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp]
    norm_num at hc ⊢
    exact hc
  have hsplit := Fintype.card_subtype_compl (fun u : V => u ∈ c.supp)
  rw [hins, hcardV] at hsplit
  omega

end


end Erdos85

#print axioms
  Erdos85.orderSixtyFour_signedSizeTwo_muThree_exterior_gridEmbedding
#print axioms
  Erdos85.c4Free_exteriorGridLabel_neighbor_coordinate_injective
#print axioms Erdos85.signedFinset_zeroSum_filter_cards
#print axioms Erdos85.orderSixtyFour_signedSizeTwo_signClass_cards
#print axioms Erdos85.orderSixtyFour_sizeTwoComponent_exterior_card
