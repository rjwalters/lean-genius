import Proofs.Erdos85SizeTwoMuNegThreeSelfCellZeroFourConsumer
import Proofs.Erdos85SizeTwoMuNegThreeSectorSwitchRouting

/-! # Quotient router for the `mu=-3`, `(k,r)=(0,4)` self cell -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A normalized cycle defect entry equal to one rules out the all-triangle
branch of the internal-cycle dichotomy, hence forces triangle-free degree
two on the entire shore. -/
theorem binarySquare_regular_sizeTwoPart_eight_cycleEntriesOne_forces_allTriangleFree
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
    (hc : c.supp.ncard = 8 * 2)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hone : C8CycleEntriesOne (fun i j ↦
      ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ (u i) (u j))) :
    ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2 := by
  classical
  rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
    G hfree (q := 8) (by omega) (by decide) hreg hcard c hc a with hall0 | hall2
  · exfalso
    have hK : ((secondOrderDefectGraph G).induce c.supp).Adj
        (u 0) (u 1) := by
      have hM := hone.2
      simpa [C8CycleEntriesOne, SimpleGraph.adjMatrix_apply] using hM
    have hH : (G.induce c.supp).Adj (u 0) (u 1) := by
      rw [← (G.induce c.supp).mem_neighborFinset, hu]
      simp
    have htf : (triangleFreeEdgeGraph G).Adj (u 0).1 (u 1).1 := by
      rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
      exact ⟨hH, hK⟩
    have hpos : 0 < (triangleFreeEdgeGraph G).degree (u 0).1 := by
      rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨(u 1).1,
        ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf⟩
    have hu0a : u 0 ∈ a.supp := by
      rw [← hurange]
      exact ⟨0, rfl⟩
    rw [hall0 (u 0) hu0a] at hpos
    omega
  · exact hall2

/-- The graph-level ledger socket for the `(0,4)` contradiction. -/
theorem orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_ledger
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
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hsame0 : ∀ x ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp)).filter fun y ↦
          ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
            s y.1 = s x.1).card = 0)
    (htf2 : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2) : False := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc z
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ :=
    (adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c).symm
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hua (i : ZMod 8) : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hrow3 : ∀ i, ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      K.Adj (u i) (u j)).card = 3 := by
    intro i
    let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
      K.Adj (u i) (u j)
    let B := componentNeighborFinset K H a (u i)
    have himage : T.image u = B := by
      ext z
      simp only [T, B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, componentNeighborFinset]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨(K.mem_neighborFinset _ _).mpr hj,
          (ConnectedComponent.mem_supp_iff a (u j)).mp (hua j)⟩
      · rintro ⟨hzK, hza⟩
        have hzA : z ∈ a.supp :=
          (ConnectedComponent.mem_supp_iff a z).mpr hza
        rw [← hurange] at hzA
        obtain ⟨j, rfl⟩ := hzA
        exact ⟨j, (K.mem_neighborFinset _ _).mp hzK, rfl⟩
    change T.card = 3
    rw [← Finset.card_image_of_injective T huinj, himage]
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal
      a a (hua i)]
    exact haa3
  have hsame0coord : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u i).1 ∧ K.Adj (u i) (u j)).card = 0 := by
    intro i
    rw [coordinate_sameSign_adj_card_eq_support K A u huinj hurangeA
      (fun x : c.supp ↦ s x.1) i]
    have huiA : u i ∈ A := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hua i⟩
    simpa [A, K, and_comm] using hsame0 (u i) huiA
  have hcyc : ∀ i, K.Adj (u i) (u (i + 1)) := by
    intro i
    let T := (Finset.univ : Finset c.supp).filter fun y ↦
      (triangleFreeEdgeGraph G).Adj (u i).1 y.1
    have himage : Finset.image Subtype.val T =
        (triangleFreeEdgeGraph G).neighborFinset (u i).1 := by
      ext y
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro htf
        have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u i).1 y := by
          rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
          exact htf
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c y]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj
            hpair.2).symm.trans
              ((ConnectedComponent.mem_supp_iff c (u i).1).mp (u i).2)
        exact ⟨⟨y, hyc⟩, htf, rfl⟩
    have hTcard : T.card = 2 := by
      rw [← Finset.card_image_of_injective T Subtype.val_injective,
        himage, (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
      exact htf2 (u i) (hua i)
    have hTsub : T ⊆ H.neighborFinset (u i) := by
      intro y hy
      have htf := (Finset.mem_filter.mp hy).2
      have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u i).1 y.1 := by
        rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact htf
      exact (H.mem_neighborFinset (u i) y).mpr hpair.1
    have hTeq : T = H.neighborFinset (u i) := by
      apply Finset.eq_of_subset_of_card_le hTsub
      rw [hTcard, H.card_neighborFinset_eq_degree, hHdegree]
    have hHi : H.Adj (u i) (u (i + 1)) := by
      rw [← H.mem_neighborFinset, hu]
      simp
    have huiT : u (i + 1) ∈ T := by
      rw [hTeq]
      exact (H.mem_neighborFinset _ _).mpr hHi
    have htf := (Finset.mem_filter.mp huiT).2
    have hpair : (G ⊓ secondOrderDefectGraph G).Adj
        (u i).1 (u (i + 1)).1 := by
      rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
      exact htf
    exact hpair.2
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hflip : ∀ i, s (u (i + 1)).1 = -s (u i).1 := by
    intro i
    have hadj : H.Adj (u i) (u (i + 1)) := by
      rw [← H.mem_neighborFinset, hu]
      simp
    have hmem : (u (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (u i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (u (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull (u i).2).2 _ hmem
  exact graph_zmodEight_selfCell_zeroFour_false H K u huinj hu
    (fun x : c.supp ↦ s x.1) (fun i ↦ hs_in _ (u i).2) hflip hcomm
      hrow3 hsame0coord hcyc

/-- Version of the `(0,4)` router consuming the normalized sector output
`C8CycleEntriesOne` directly. -/
theorem orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_cycleEntriesOne
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
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hsame0 : ∀ x ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp)).filter fun y ↦
          ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
            s y.1 = s x.1).card = 0)
    (hone : C8CycleEntriesOne (fun i j ↦
      ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ (u i) (u j))) :
    False := by
  exact orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_ledger
    G hfree hreg hcard c hc s hs_out hs_in hH a u huinj hurange hu
      haa3 hsame0
      (binarySquare_regular_sizeTwoPart_eight_cycleEntriesOne_forces_allTriangleFree
        G hfree hreg hcard c hc a u hurange hu hone)

/-- Literal aligned-ledger closure of the `(μ,k,r)=(-3,0,4)` cell. -/
theorem orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_parameters
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
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (k r : ℕ) (hk : k = 0) (hr : r = 4)
    (haa : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a =
        7 - r)
    (hsame : ∀ x ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp)).filter fun y ↦
          ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
            s y.1 = s x.1).card = k)
    (hone : C8CycleEntriesOne (fun i j ↦
      ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ (u i) (u j))) :
    False := by
  have haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3 := by
    simpa [hr] using haa
  have hsame0 : ∀ x ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp)).filter fun y ↦
          ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
            s y.1 = s x.1).card = 0 := by
    intro x hx
    simpa [hk] using hsame x hx
  exact orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_cycleEntriesOne
    G hfree hreg hcard c hc s hs_out hs_in hH a u huinj hurange hu
      haa3 hsame0 hone

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_ledger
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_cycleEntriesOne_forces_allTriangleFree
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_cycleEntriesOne
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_parameters
