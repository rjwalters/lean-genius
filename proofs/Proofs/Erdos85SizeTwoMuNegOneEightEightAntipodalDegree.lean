import Proofs.Erdos85SizeTwoMuNegOneEightEightCrossAntipodal
import Proofs.Erdos85SizeTwoMuNegOneEightEightSignedParameterConsumer
import Proofs.Erdos85AntipodalCycleReservoir

/-! # Antipodal degree pressure in the `mu=-1` C8+C8 branch -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Lightweight local form of the order-64 size-two antipodal degree
dichotomy, avoiding any dependence on terminal certificate modules. -/
theorem orderSixtyFour_sizeTwo_antipodal_degree_eq_five_or_seven_local
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
    (hc : c.supp.ncard = 8 * 2) (x : c.supp) :
    (antipodalGraph G).degree x.1 = 5 ∨
      (antipodalGraph G).degree x.1 = 7 := by
  have htf := binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
    G hfree (q := 8) (by omega) (by decide) hreg hcard c hc x
  have hcard64 : Fintype.card V = 8 * (8 - 1) + 3 + 5 := by
    norm_num at hcard ⊢
    exact hcard
  have hanti := antipodalGraph_degree_eq_excess_add_two_sub_triangleFree
    G hfree (d := 8) (e := 5) (by omega) hreg hcard64 x.1
  have htfcard : (triangleFreeNeighbors G x.1).card =
      (triangleFreeEdgeGraph G).degree x.1 := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
  rw [htfcard] at hanti
  rcases htf with hzero | htwo
  · right; omega
  · left; omega

/-- Equal-sign defect adjacency inside a size-two component is antipodal. -/
theorem sizeTwo_equalSign_secondOrderDefect_iff_antipodal_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (x y : c.supp) (hsame : s y.1 = s x.1) :
    (secondOrderDefectGraph G).Adj x.1 y.1 ↔
      (antipodalGraph G).Adj x.1 y.1 := by
  constructor
  · intro hD
    change ((antipodalGraph G) ⊔ triangleFreeEdgeGraph G).Adj x.1 y.1 at hD
    rcases hD with hanti | htf
    · exact hanti
    · exfalso
      have hG : G.Adj x.1 y.1 :=
        ((mem_triangleFreeNeighbors G x.1 y.1).mp
          ((triangleFreeEdgeGraph_adj G x.1 y.1).mp htf)).1
      have hymem : y.1 ∈ componentNeighborFinset G
          (secondOrderDefectGraph G) c x.1 := by
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset _ _).mpr hG,
          (ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
      have hflip := (internal_alternation G hfree (by omega) hreg hcard
        c hc s hs_in hs_out hA_in x.2).2 y.1 hymem
      rcases hs_in x.1 x.2 with hxneg | hxpos <;> omega
  · intro hanti
    exact Or.inl hanti

set_option maxHeartbeats 1200000 in
/-- The cross-antipodal `r` edges and the diagonal same-sign `k` edges are
disjoint antipodal neighbors in the `mu=-1` branch. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_signed_antipodal_subdegree
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
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    ∃ k r : ℕ, k ≤ 3 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      ∀ x : c.supp, x ∈ a.supp →
        r + k ≤ (antipodalGraph G).degree x.1 ∧
        ((antipodalGraph G).degree x.1 = 5 ∨
          (antipodalGraph G).degree x.1 = 7) := by
  classical
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨k, hk, hA, _hB, _hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨r, hr2, hr7, hcrossAnti, _hcrossAnti'⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_crossAntipodal_degree
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  refine ⟨k, r, hk, hr2, hr7, ?_⟩
  intro x hxa
  let X := B.filter fun y ↦ (antipodalGraph G).Adj x.1 y.1
  let Y := A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1
  have hXcard : X.card = r := hcrossAnti x hxa
  have hxA : x ∈ A := by simpa [A] using hxa
  have hYcard : Y.card = k := hA x hxA
  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro y hyX hyY
    have hyb := (Finset.mem_filter.mp (Finset.mem_filter.mp hyX).1).2
    have hya := (Finset.mem_filter.mp (Finset.mem_filter.mp hyY).1).2
    exact hab <| (ConnectedComponent.mem_supp_iff a y).mp hya |>.symm.trans
      ((ConnectedComponent.mem_supp_iff b y).mp hyb)
  let Z : Finset V := (X ∪ Y).image Subtype.val
  have hZcard : Z.card = r + k := by
    rw [show Z.card = (X ∪ Y).card by
      exact Finset.card_image_of_injective _ Subtype.val_injective]
    rw [Finset.card_union_of_disjoint hdisj, hXcard, hYcard]
  have hZsub : Z ⊆ (antipodalGraph G).neighborFinset x.1 := by
    intro z hz
    simp only [Z, Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rcases Finset.mem_union.mp hy with hyX | hyY
    · exact ((antipodalGraph G).mem_neighborFinset _ _).mpr
        (Finset.mem_filter.mp hyX).2
    · have hy' := Finset.mem_filter.mp hyY
      have hsame := hy'.2.2
      have hK := hy'.2.1
      exact ((antipodalGraph G).mem_neighborFinset _ _).mpr <|
        (sizeTwo_equalSign_secondOrderDefect_iff_antipodal_local
          G hfree hreg hcard c hc s hs_in hs_out hAfull x y hsame).1 hK
  constructor
  · rw [← hZcard, ← (antipodalGraph G).card_neighborFinset_eq_degree]
    exact Finset.card_le_card hZsub
  · exact orderSixtyFour_sizeTwo_antipodal_degree_eq_five_or_seven_local
      G hfree hreg hcard c hc x

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_signed_antipodal_subdegree
