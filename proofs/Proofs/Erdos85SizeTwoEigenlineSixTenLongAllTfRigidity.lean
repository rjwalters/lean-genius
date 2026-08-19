import Proofs.Erdos85SizeTwoEigenlineSixTenCrossSign

/-!
# Conditional rigidity of the long all-TF cycle in the q=8 6+10 stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The long diagonal defect block has exactly two opposite-sign neighbors at
every vertex.  If the long ambient cycle is all triangle-free, its two cycle
neighbors are defect neighbors and alternate sign, so they exhaust that
opposite-sign diagonal neighborhood.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_opposite_defectAdj_iff
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
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (hbtf : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (x y : c.supp) (hx : x ∈ b.supp) (hy : y ∈ b.supp) :
    (((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
        s y.1 = -s x.1) ↔
      (G.induce c.supp).Adj x y := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let oppositeB := (componentNeighborFinset K H b x).filter
    fun z => s z.1 = -s x.1
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hoppCard : oppositeB.card = 2 := by
    simpa [oppositeB, K, H] using
      (binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb x hx).2
  have hcycleSub : H.neighborFinset x ⊆ oppositeB := by
    intro z hz
    have hxz : H.Adj x z := (H.mem_neighborFinset x z).mp hz
    have hzmem : z ∈ b.supp := (b.mem_supp_congr_adj hxz).mp hx
    have htfEdge : (triangleFreeEdgeGraph G).Adj x.1 z.1 :=
      sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree x z hxz (hbtf x hx)
    have hK : K.Adj x z := Or.inr htfEdge
    have hflip : s z.1 = -s x.1 := by
      have hzComp : z.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x.1 := by
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset _ _).mpr hxz, z.2⟩
      exact (internal_alternation G hfree (by omega) hreg hcard c hc s
        hs_in hs_out hA_in x.2).2 z.1 hzComp
    simp only [oppositeB, Finset.mem_filter, componentNeighborFinset]
    exact ⟨⟨(K.mem_neighborFinset x z).mpr hK,
      (ConnectedComponent.mem_supp_iff b z).mp hzmem⟩, hflip⟩
  have hcycleCard : (H.neighborFinset x).card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hHdegree]
  have hcycleEq : H.neighborFinset x = oppositeB :=
    Finset.eq_of_subset_of_card_le hcycleSub (by omega)
  constructor
  · rintro ⟨hK, hsign⟩
    have hyOpp : y ∈ oppositeB := by
      simp only [oppositeB, Finset.mem_filter, componentNeighborFinset]
      exact ⟨⟨(K.mem_neighborFinset x y).mpr hK,
        (ConnectedComponent.mem_supp_iff b y).mp hy⟩, hsign⟩
    rw [← hcycleEq] at hyOpp
    exact (H.mem_neighborFinset x y).mp hyOpp
  · intro hH
    have hyCycle : y ∈ H.neighborFinset x := (H.mem_neighborFinset x y).mpr hH
    rw [hcycleEq] at hyCycle
    exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hyCycle).1).1 |>
      (K.mem_neighborFinset x y).mp,
      (Finset.mem_filter.mp hyCycle).2⟩

/-- Equivalently, every non-cycle edge of the long diagonal defect block
preserves sign in the all-TF branch. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_noncycle_defect_preserves_sign
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
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (hbtf : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (x y : c.supp) (hx : x ∈ b.supp) (hy : y ∈ b.supp)
    (hK : ((secondOrderDefectGraph G).induce c.supp).Adj x y)
    (hnotH : ¬ (G.induce c.supp).Adj x y) :
    s y.1 = s x.1 := by
  by_contra hsign
  have hopp : s y.1 = -s x.1 := by
    rcases hs_in y.1 y.2 with hyNeg | hyPos <;>
      rcases hs_in x.1 x.2 with hxNeg | hxPos <;> simp_all
  exact hnotH
    ((binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_opposite_defectAdj_iff
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hbtf
        x y hx hy).mp ⟨hK, hopp⟩)

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_opposite_defectAdj_iff
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_noncycle_defect_preserves_sign
