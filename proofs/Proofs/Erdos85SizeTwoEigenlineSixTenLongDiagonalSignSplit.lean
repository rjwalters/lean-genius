import Proofs.Erdos85SizeTwoEigenlineSixTenCrossSign

/-!
# Exact sign split on the long diagonal block in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

Each ten-cycle vertex has three same-sign defect neighbors in the six-cycle.
Globally it has five same-sign and two opposite-sign defect neighbors, while
its diagonal quotient degree is four.  Hence its four ten-cycle defect
neighbors split exactly as two same-sign and two opposite-sign neighbors.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
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
    (y : c.supp) (hy : y ∈ b.supp) :
    (((componentNeighborFinset
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
      fun z => s z.1 = s y.1).card = 2) ∧
    (((componentNeighborFinset
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
      fun z => s z.1 = -(s y.1)).card = 2) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let sameAll := (K.neighborFinset y).filter fun z => s z.1 = s y.1
  let sameA := (componentNeighborFinset K H a y).filter fun z => s z.1 = s y.1
  let sameB := (componentNeighborFinset K H b y).filter fun z => s z.1 = s y.1
  let oppB := (componentNeighborFinset K H b y).filter fun z => s z.1 = -(s y.1)
  have hab : a ≠ b := by
    intro h
    rw [h] at ha
    omega
  have hcycle (d : H.ConnectedComponent) : 6 ≤ d.supp.ncard :=
    (binarySquare_regular_sizeTwoPart_internalCycle_even_six_le
      G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in d).2
  obtain ⟨_hrows, _hbalance, htotal⟩ :=
    binarySquare_regular_sizeTwoPart_cycleQuotient
      G hfree (by omega) hreg hcard c hc
  have hcardComp : Fintype.card H.ConnectedComponent ≤ 2 := by
    have hlower : 6 * Fintype.card H.ConnectedComponent ≤
        ∑ d : H.ConnectedComponent, d.supp.ncard := by
      calc
        6 * Fintype.card H.ConnectedComponent =
            ∑ _d : H.ConnectedComponent, 6 := by simp [Nat.mul_comm]
        _ ≤ ∑ d : H.ConnectedComponent, d.supp.ncard := by
          apply Finset.sum_le_sum
          intro d _
          exact hcycle d
    rw [htotal] at hlower
    omega
  have hcases (d : H.ConnectedComponent) : d = a ∨ d = b := by
    by_contra hd
    push Not at hd
    have hthree : 3 ≤ Fintype.card H.ConnectedComponent := by
      calc
        3 = ({a, b, d} : Finset H.ConnectedComponent).card := by
          simp [hab, hd.1.symm, hd.2.symm]
        _ ≤ (Finset.univ : Finset H.ConnectedComponent).card :=
          Finset.card_le_card (by simp)
        _ = Fintype.card H.ConnectedComponent := Finset.card_univ
    omega
  have hpartition : sameAll = sameA ∪ sameB := by
    ext z
    simp only [sameAll, sameA, sameB, Finset.mem_filter,
      componentNeighborFinset, Finset.mem_union]
    constructor
    · rintro ⟨hzK, hzsign⟩
      have hzAdj : K.Adj y z := (K.mem_neighborFinset y z).mp hzK
      rcases hcases (H.connectedComponentMk z) with hza | hzb
      · exact Or.inl ⟨⟨hzK, hza⟩, hzsign⟩
      · exact Or.inr ⟨⟨hzK, hzb⟩, hzsign⟩
    · rintro (⟨⟨hzK, _⟩, hzsign⟩ | ⟨⟨hzK, _⟩, hzsign⟩) <;>
        exact ⟨hzK, hzsign⟩
  have hdisj : Disjoint sameA sameB := by
    rw [Finset.disjoint_left]
    intro z hza hzb
    have hca := (Finset.mem_filter.mp hza).1
    have hcb := (Finset.mem_filter.mp hzb).1
    have hzaComp := (Finset.mem_filter.mp hca).2
    have hzbComp := (Finset.mem_filter.mp hcb).2
    exact hab (hzaComp.symm.trans hzbComp)
  have hsameAllCard : sameAll.card = 5 := by
    let ambientSame := ((secondOrderDefectGraph G).neighborFinset y.1).filter
      fun z => s z = s y.1
    have himage : sameAll.image Subtype.val = ambientSame := by
      ext z
      simp only [sameAll, ambientSame, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨w, ⟨hwK, hws⟩, rfl⟩
        exact ⟨((secondOrderDefectGraph G).mem_neighborFinset y.1 w.1).mpr
          ((K.mem_neighborFinset y w).mp hwK), hws⟩
      · rintro ⟨hzD, hzs⟩
        have hzSupp : z ∈ c.supp := defect_neighbor_mem_supp G c y.2
          (((secondOrderDefectGraph G).mem_neighborFinset y.1 z).mp hzD)
        refine ⟨⟨z, hzSupp⟩, ?_, rfl⟩
        exact ⟨(K.mem_neighborFinset y ⟨z, hzSupp⟩).mpr
          (((secondOrderDefectGraph G).mem_neighborFinset y.1 z).mp hzD), hzs⟩
    calc
      sameAll.card = (sameAll.image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = ambientSame.card := congrArg Finset.card himage
      _ = 5 := by
        simpa [ambientSame] using
          (sameSide_defect_degree G hfree (q := 8) (by omega) hreg hcard c s
            hs_in hDs y.2).1
  have hsameACard : sameA.card = 3 := by
    simpa [sameA, K, H] using
      binarySquare_regular_sizeTwoPart_eight_sixTen_longVertex_three_sameSign_cross
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb y hy
  have hsameBCard : sameB.card = 2 := by
    have hadd : sameAll.card = sameA.card + sameB.card := by
      rw [hpartition, Finset.card_union_of_disjoint hdisj]
    omega
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
  have hdiagCard : (componentNeighborFinset K H b y).card = 4 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal b b hy]
    exact (binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb).2.2.2
  have hdiagPartition : componentNeighborFinset K H b y = sameB ∪ oppB := by
    ext z
    simp only [sameB, oppB, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hz
      have hzSupp : z.1 ∈ c.supp := z.2
      rcases hs_in z.1 hzSupp with hzNeg | hzPos <;>
        rcases hs_in y.1 y.2 with hyNeg | hyPos <;> simp_all
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
  have hdiagDisj : Disjoint sameB oppB := by
    rw [Finset.disjoint_left]
    intro z hzs hzo
    have hs := (Finset.mem_filter.mp hzs).2
    have ho := (Finset.mem_filter.mp hzo).2
    have hne : s y.1 ≠ -(s y.1) := by
      rcases hs_in y.1 y.2 with hyNeg | hyPos <;> omega
    exact hne (hs.symm.trans ho)
  have hoppBCard : oppB.card = 2 := by
    have hadd : (componentNeighborFinset K H b y).card = sameB.card + oppB.card := by
      rw [hdiagPartition, Finset.card_union_of_disjoint hdiagDisj]
    omega
  simpa [sameB, oppB, K, H] using And.intro hsameBCard hoppBCard

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
