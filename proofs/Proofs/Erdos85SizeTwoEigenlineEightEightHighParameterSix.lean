import Proofs.Erdos85SizeTwoEigenlineEightEightHighSectorSaturation

/-!
# The high eight-plus-eight parameter is six

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The high quotient parameter cannot be seven.  The finite input is that an
alternating sign on an eight-cycle has only four vertices of either sign;
if the diagonal defect degree vanished, the global five same-sign defect
neighbours would all have to fit in the opposite cycle.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An alternating `±1` labeling of `ZMod 8` has four entries of each sign. -/
theorem zmodEight_alternating_sign_filter_cards
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i) :
    ((Finset.univ : Finset (ZMod 8)).filter (fun i => f i = f 0)).card = 4 ∧
      ((Finset.univ : Finset (ZMod 8)).filter
        (fun i => f i = -f 0)).card = 4 := by
  have h1 : f 1 = -f 0 := by simpa using hflip 0
  have h2 : f 2 = f 0 := by
    calc
      f 2 = -f 1 := by
        simpa only [show (1 : ZMod 8) + 1 = 2 by decide] using hflip 1
      _ = f 0 := by rw [h1]; ring
  have h3 : f 3 = -f 0 := by
    calc
      f 3 = -f 2 := by
        simpa only [show (2 : ZMod 8) + 1 = 3 by decide] using hflip 2
      _ = -f 0 := by rw [h2]
  have h4 : f 4 = f 0 := by
    calc
      f 4 = -f 3 := by
        simpa only [show (3 : ZMod 8) + 1 = 4 by decide] using hflip 3
      _ = f 0 := by rw [h3]; ring
  have h5 : f 5 = -f 0 := by
    calc
      f 5 = -f 4 := by
        simpa only [show (4 : ZMod 8) + 1 = 5 by decide] using hflip 4
      _ = -f 0 := by rw [h4]
  have h6 : f 6 = f 0 := by
    calc
      f 6 = -f 5 := by
        simpa only [show (5 : ZMod 8) + 1 = 6 by decide] using hflip 5
      _ = f 0 := by rw [h5]; ring
  have h7 : f 7 = -f 0 := by
    calc
      f 7 = -f 6 := by
        simpa only [show (6 : ZMod 8) + 1 = 7 by decide] using hflip 6
      _ = -f 0 := by rw [h6]
  have hne : f 0 ≠ -f 0 := by
    rcases hsign 0 with hneg | hpos <;> omega
  have hne' : -f 0 ≠ f 0 := Ne.symm hne
  have hsame : (Finset.univ : Finset (ZMod 8)).filter
      (fun i => f i = f 0) = {0, 2, 4, 6} := by
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 := by
      revert i
      decide
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [h1, h2, h3, h4, h5, h6, h7, hne'] <;> decide
  have hopp : (Finset.univ : Finset (ZMod 8)).filter
      (fun i => f i = -f 0) = {1, 3, 5, 7} := by
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 := by
      revert i
      decide
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [h1, h2, h3, h4, h5, h6, h7, hne] <;> decide
  rw [hsame, hopp]
  decide

/-- In cyclic coordinates on an `8+8` component, the cross quotient cannot
be seven: seven cross neighbours would exhaust the defect neighbourhood, but
five same-sign neighbours cannot fit in the four-vertex sign class of the
opposite alternating eight-cycle. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_crossQuotient_ne_seven_of_coordinates
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b ≠ 7 := by
  classical
  let H := G.induce c.supp
  let D := secondOrderDefectGraph G
  let K := D.induce c.supp
  intro hab7
  let x : c.supp := u 0
  let B := componentNeighborFinset K H b x
  have hxA : x ∈ a.supp := by
    rw [← hurange]
    exact ⟨0, rfl⟩
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G D hglobal c).symm
  have hBcard : B.card = 7 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a b hxA]
    exact hab7
  have hKcard : (K.neighborFinset x).card = 7 := by
    rw [K.card_neighborFinset_eq_degree, degree_induce_connectedComponent_supp]
    exact defect_degree G hfree (by omega) hreg hcard x.1
  have hBeq : B = K.neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.filter_subset _ _
    · omega
  let KVals : Finset V := (K.neighborFinset x).image Subtype.val
  have hKValsSub : KVals ⊆ D.neighborFinset x.1 := by
    intro z hz
    simp only [KVals, Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (D.mem_neighborFinset x.1 w.1).mpr
      ((K.mem_neighborFinset x w).mp hw)
  have hKValsCard : KVals.card = 7 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hKcard]
  have hDcard : (D.neighborFinset x.1).card = 7 := by
    rw [D.card_neighborFinset_eq_degree]
    exact defect_degree G hfree (by omega) hreg hcard x.1
  have hKValsEq : KVals = D.neighborFinset x.1 :=
    Finset.eq_of_subset_of_card_le hKValsSub (by omega)
  have hBsame : (B.filter fun z => s z.1 = s x.1).card = 5 := by
    have himage : (((K.neighborFinset x).filter fun z => s z.1 = s x.1).image
        Subtype.val) = (D.neighborFinset x.1).filter fun z => s z = s x.1 := by
      ext z
      constructor
      · simp only [Finset.mem_image, Finset.mem_filter]
        rintro ⟨w, ⟨hw, hsign⟩, rfl⟩
        exact ⟨hKValsSub (Finset.mem_image.mpr ⟨w, hw, rfl⟩), hsign⟩
      · intro hz
        have hzD := (Finset.mem_filter.mp hz).1
        have hzSign := (Finset.mem_filter.mp hz).2
        rw [← hKValsEq] at hzD
        simp only [KVals, Finset.mem_image] at hzD
        obtain ⟨w, hw, rfl⟩ := hzD
        exact Finset.mem_image.mpr
          ⟨w, Finset.mem_filter.mpr ⟨hw, hzSign⟩, rfl⟩
    rw [hBeq, ← Finset.card_image_of_injective _ Subtype.val_injective, himage]
    simpa [D] using
      (sameSide_defect_degree G hfree (q := 8) (by omega) hreg hcard c s
        hs_in hDs x.2).1
  have hvflip : ∀ j : ZMod 8, s (v (j + 1)).1 = -s (v j).1 := by
    intro j
    have hH : H.Adj (v j) (v (j + 1)) := by
      rw [← H.mem_neighborFinset, hv]
      simp
    have hmem : (v (j + 1)).1 ∈
        componentNeighborFinset G D c (v j).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (v (j + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (v j).2).2 _ hmem
  obtain ⟨hvSame, hvOpp⟩ := zmodEight_alternating_sign_filter_cards
    (fun j => s (v j).1) (fun j => hs_in _ (v j).2) hvflip
  let S : Finset c.supp := (Finset.univ.image v).filter fun z => s z.1 = s x.1
  have hBsubS : B.filter (fun z => s z.1 = s x.1) ⊆ S := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    have hzSign := (Finset.mem_filter.mp hz).2
    have hzb : z ∈ b.supp := (Finset.mem_filter.mp hzB).2
    rw [← hvrange] at hzb
    obtain ⟨j, rfl⟩ := hzb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hzSign⟩
  have hScard : S.card = 4 := by
    have hfilterImage : S =
        ((Finset.univ : Finset (ZMod 8)).filter
          fun j => s (v j).1 = s x.1).image v := by
      ext z
      simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨⟨j, _, rfl⟩, hj⟩
        exact ⟨j, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, rfl⟩, hj⟩
    rw [hfilterImage, Finset.card_image_of_injective _ hvinj]
    rcases hs_in x.1 x.2 with hxNeg | hxPos <;>
      rcases hs_in (v 0).1 (v 0).2 with hvNeg | hvPos <;>
      simp_all
  have := Finset.card_le_card hBsubS
  omega

end

end Erdos85

#print axioms Erdos85.zmodEight_alternating_sign_filter_cards
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_crossQuotient_ne_seven_of_coordinates
