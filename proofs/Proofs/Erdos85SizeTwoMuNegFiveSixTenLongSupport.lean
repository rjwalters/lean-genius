import Proofs.Erdos85SizeTwoMuNegFiveSixTenSameSignCross

/-! # Long-side support identity in the `mu=-5`, `6+10` sector -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- In normalized short-cycle coordinates, a long positive vertex has a
neutral edge to the short negative shore iff its same-sign defect mate lies
on the short positive shore. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_long_positive_support_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (coord : SizeTwoCycleGridCoordinates (G.induce c.supp) a.supp
      (fun z => s z.1) 3)
    (fp : Equiv.Perm (MuNegFivePositiveShore (secondOrderDefectGraph G) c s))
    (hfp : ∀ x y, (secondOrderDefectGraph G).Adj x.1 y.1 ↔ fp x = y)
    (x : MuNegFivePositiveShore (secondOrderDefectGraph G) c s)
    (hxb : (⟨x.1, x.2.1⟩ : c.supp) ∈ b.supp) :
    ((⟨(fp x).1, (fp x).2.1⟩ : c.supp) ∈ a.supp) ↔
      ∃ j : ZMod 3,
        MuNegFiveNeutralProjection G c s x
          ⟨(coord.nval j).1, (coord.nval j).2, (coord.n_mem_sign j).2⟩ := by
  classical
  let D := secondOrderDefectGraph G
  let H := G.induce c.supp
  let K := D.induce c.supp
  let N := MuNegFiveNeutralProjection G c s
  have hA := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hg := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G D hg c).symm
  let C := componentNeighborFinset K H a (⟨x.1, x.2.1⟩ : c.supp)
  have hCcard : C.card = 3 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm b a hxb]
    exact (binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA a b ha hb).2.2.1
  have hNiff := orderSixtyFour_sizeTwo_muNegFive_neutralProjection_iff_not_defect
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  let NS : Finset c.supp := Finset.univ.image coord.nval
  have hNScard : NS.card = 3 := by
    rw [Finset.card_image_of_injective _ coord.n_injective, Finset.card_univ]
    decide
  constructor
  · intro hfa
    by_contra hn
    push Not at hn
    let fx : c.supp := ⟨(fp x).1, (fp x).2.1⟩
    have hfxnot : fx ∉ NS := by
      intro hm
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
      have hsEq := congrArg (fun z : c.supp => s z.1) hj
      rw [(fp x).2.2, (coord.n_mem_sign j).2] at hsEq
      omega
    have hinscard : (insert fx NS).card = 4 := by
      rw [Finset.card_insert_of_notMem hfxnot, hNScard]
    have hsub : insert fx NS ⊆ C := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · change fx ∈ componentNeighborFinset K H a (⟨x.1, x.2.1⟩ : c.supp)
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(K.mem_neighborFinset _ _).mpr ((hfp x (fp x)).2 rfl),
          (ConnectedComponent.mem_supp_iff a _).mp hfa⟩
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
        let y : MuNegFiveNegativeShore D c s :=
          ⟨(coord.nval j).1, (coord.nval j).2, (coord.n_mem_sign j).2⟩
        have hDxy : D.Adj x.1 y.1 := by
          by_contra hd
          exact hn j ((hNiff x y).2 hd)
        change coord.nval j ∈
          componentNeighborFinset K H a (⟨x.1, x.2.1⟩ : c.supp)
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(K.mem_neighborFinset _ _).mpr hDxy,
          (ConnectedComponent.mem_supp_iff a _).mp (coord.n_mem_sign j).1⟩
    have := Finset.card_le_card hsub
    omega
  · rintro ⟨j, hNj⟩
    by_contra hfa
    let yj : MuNegFiveNegativeShore D c s :=
      ⟨(coord.nval j).1, (coord.nval j).2, (coord.n_mem_sign j).2⟩
    have hyjNS : coord.nval j ∈ NS := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have hsub : C ⊆ NS.erase (coord.nval j) := by
      intro z hz
      have hzK := (Finset.mem_filter.mp hz).1
      have hKadj := (K.mem_neighborFinset _ _).mp hzK
      change D.Adj x.1 z.1 at hKadj
      have hza := (ConnectedComponent.mem_supp_iff a z).mpr
        (Finset.mem_filter.mp hz).2
      have hzneg : s z.1 = -1 := by
        rcases hs_in z.1 z.2 with hzneg | hzpos
        · exact hzneg
        · let zp : MuNegFivePositiveShore D c s := ⟨z.1, z.2, hzpos⟩
          have hDxz : D.Adj x.1 zp.1 := hKadj
          have heq : fp x = zp := (hfp x zp).1 hDxz
          exfalso
          apply hfa
          simpa [heq, zp] using hza
      obtain ⟨k, hk⟩ := coord.n_surjective z hza hzneg
      apply Finset.mem_erase.mpr
      constructor
      · intro hEq
        have hDxz : D.Adj x.1 yj.1 := by
          change D.Adj x.1 (coord.nval j).1
          rw [← hEq]
          exact hKadj
        exact (hNiff x yj).1 hNj hDxz
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
    have herase : (NS.erase (coord.nval j)).card = 2 := by
      rw [Finset.card_erase_of_mem hyjNS, hNScard]
    have hle : C.card ≤ (NS.erase (coord.nval j)).card :=
      Finset.card_le_card hsub
    rw [hCcard, herase] at hle
    omega

/-- Negative-shore mirror of the long support identity. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_long_negative_support_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (coord : SizeTwoCycleGridCoordinates (G.induce c.supp) a.supp
      (fun z => s z.1) 3)
    (fm : Equiv.Perm (MuNegFiveNegativeShore (secondOrderDefectGraph G) c s))
    (hfm : ∀ x y, (secondOrderDefectGraph G).Adj x.1 y.1 ↔ fm x = y)
    (y : MuNegFiveNegativeShore (secondOrderDefectGraph G) c s)
    (hyb : (⟨y.1, y.2.1⟩ : c.supp) ∈ b.supp) :
    ((⟨(fm y).1, (fm y).2.1⟩ : c.supp) ∈ a.supp) ↔
      ∃ i : ZMod 3,
        MuNegFiveNeutralProjection G c s
          ⟨(coord.pval i).1, (coord.pval i).2, (coord.p_mem_sign i).2⟩ y := by
  classical
  let D := secondOrderDefectGraph G
  let H := G.induce c.supp
  let K := D.induce c.supp
  have hA := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hg := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G D hg c).symm
  let C := componentNeighborFinset K H a (⟨y.1, y.2.1⟩ : c.supp)
  have hCcard : C.card = 3 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm b a hyb]
    exact (binarySquare_regular_sizeTwoPart_eight_sixTen_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA a b ha hb).2.2.1
  have hNiff := orderSixtyFour_sizeTwo_muNegFive_neutralProjection_iff_not_defect
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  let PS : Finset c.supp := Finset.univ.image coord.pval
  have hPScard : PS.card = 3 := by
    rw [Finset.card_image_of_injective _ coord.p_injective, Finset.card_univ]
    decide
  constructor
  · intro hfa
    by_contra hn
    push Not at hn
    let fy : c.supp := ⟨(fm y).1, (fm y).2.1⟩
    have hfynot : fy ∉ PS := by
      intro hm
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      have hsEq := congrArg (fun z : c.supp => s z.1) hi
      rw [(fm y).2.2, (coord.p_mem_sign i).2] at hsEq
      omega
    have hinscard : (insert fy PS).card = 4 := by
      rw [Finset.card_insert_of_notMem hfynot, hPScard]
    have hsub : insert fy PS ⊆ C := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · change fy ∈ componentNeighborFinset K H a (⟨y.1, y.2.1⟩ : c.supp)
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(K.mem_neighborFinset _ _).mpr ((hfm y (fm y)).2 rfl),
          (ConnectedComponent.mem_supp_iff a _).mp hfa⟩
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        let x : MuNegFivePositiveShore D c s :=
          ⟨(coord.pval i).1, (coord.pval i).2, (coord.p_mem_sign i).2⟩
        have hDxy : D.Adj x.1 y.1 := by
          by_contra hd
          exact hn i ((hNiff x y).2 hd)
        change coord.pval i ∈
          componentNeighborFinset K H a (⟨y.1, y.2.1⟩ : c.supp)
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(K.mem_neighborFinset _ _).mpr hDxy.symm,
          (ConnectedComponent.mem_supp_iff a _).mp (coord.p_mem_sign i).1⟩
    have hle := Finset.card_le_card hsub
    omega
  · rintro ⟨i, hNi⟩
    by_contra hfa
    let xi : MuNegFivePositiveShore D c s :=
      ⟨(coord.pval i).1, (coord.pval i).2, (coord.p_mem_sign i).2⟩
    have hxiPS : coord.pval i ∈ PS := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hsub : C ⊆ PS.erase (coord.pval i) := by
      intro z hz
      have hzK := (Finset.mem_filter.mp hz).1
      have hKadj := (K.mem_neighborFinset _ _).mp hzK
      change D.Adj y.1 z.1 at hKadj
      have hza := (ConnectedComponent.mem_supp_iff a z).mpr
        (Finset.mem_filter.mp hz).2
      have hzpos : s z.1 = 1 := by
        rcases hs_in z.1 z.2 with hzneg | hzpos
        · let zm : MuNegFiveNegativeShore D c s := ⟨z.1, z.2, hzneg⟩
          have hDyz : D.Adj y.1 zm.1 := hKadj
          have heq : fm y = zm := (hfm y zm).1 hDyz
          exfalso
          apply hfa
          simpa [heq, zm] using hza
        · exact hzpos
      obtain ⟨k, hk⟩ := coord.p_surjective z hza hzpos
      apply Finset.mem_erase.mpr
      constructor
      · intro hEq
        have hDxy : D.Adj xi.1 y.1 := by
          change D.Adj (coord.pval i).1 y.1
          rw [← hEq]
          exact hKadj.symm
        exact (hNiff xi y).1 hNi hDxy
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
    have herase : (PS.erase (coord.pval i)).card = 2 := by
      rw [Finset.card_erase_of_mem hxiPS, hPScard]
    have hle : C.card ≤ (PS.erase (coord.pval i)).card :=
      Finset.card_le_card hsub
    rw [hCcard, herase] at hle
    omega
end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_long_positive_support_iff
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_long_negative_support_iff
