import Proofs.Erdos85SizeTwoMuNegOneSixTenSignedDefectSplit

/-! # Cross-defect census in the `mu=-1` six-plus-ten stratum -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The short-to-long defect block has eighteen same-sign and twelve
opposite-sign directed incidences. Viewed from the long cycle, every column
has total degree three. -/
theorem orderSixtyFour_sizeTwo_muNegOne_sixTen_crossDefect_census
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
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
    let cross := fun x ↦ (K.neighborFinset x).filter fun y ↦ y ∉ a.supp
    let Esame := A.sigma fun x ↦ (cross x).filter fun y ↦ s y.1 = s x.1
    let Eopp := A.sigma fun x ↦ (cross x).filter fun y ↦ s y.1 = -s x.1
    Esame.card = 18 ∧ Eopp.card = 12 ∧
      ∀ y : c.supp, y ∈ b.supp →
        (componentNeighborFinset K H a y).card = 3 := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let cross := fun x : c.supp ↦
    (K.neighborFinset x).filter fun y ↦ y ∉ a.supp
  let Esame := A.sigma fun x ↦ (cross x).filter fun y ↦ s y.1 = s x.1
  let Eopp := A.sigma fun x ↦ (cross x).filter fun y ↦ s y.1 = -s x.1
  have hsplit := orderSixtyFour_sizeTwo_muNegOne_sixTen_short_signedDefectSplit
    G hfree hreg hcard c hc s hs_out hs_in hH hD a b ha hb
  have hAcard : A.card = 6 := by
    have heq : A = a.supp.toFinite.toFinset := by
      ext x
      simp [A]
    rw [heq, ← Set.ncard_eq_toFinset_card, ha]
  have hsame : Esame.card = 18 := by
    dsimp [Esame]
    rw [Finset.card_sigma]
    calc
      (∑ x ∈ A, ((cross x).filter fun y ↦ s y.1 = s x.1).card) =
          ∑ _x ∈ A, 3 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxa : x ∈ a.supp := (Finset.mem_filter.mp hx).2
        exact (hsplit x hxa).2.2.1
      _ = 18 := by simp [hAcard]
  have hopp : Eopp.card = 12 := by
    dsimp [Eopp]
    rw [Finset.card_sigma]
    calc
      (∑ x ∈ A, ((cross x).filter fun y ↦ s y.1 = -s x.1).card) =
          ∑ _x ∈ A, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxa : x ∈ a.supp := (Finset.mem_filter.mp hx).2
        exact (hsplit x hxa).2.2.2
      _ = 12 := by simp [hAcard]
  refine ⟨hsame, hopp, ?_⟩
  intro y hy
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hquot := binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
    G hfree hreg hcard c hc s hs_in hs_out hAfull a b ha hb
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal b a hy]
  exact hquot.2.2.1

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_sixTen_crossDefect_census
