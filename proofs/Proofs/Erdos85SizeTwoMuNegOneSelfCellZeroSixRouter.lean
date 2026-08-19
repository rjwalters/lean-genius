import Proofs.Erdos85SizeTwoMuNegOneSelfCellZeroSix

/-! # Quotient router for the `mu=-1`, `(k,r)=(0,6)` self cell -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The graph-level ledger socket for the `(0,6)` contradiction. -/
theorem orderSixtyFour_sizeTwo_muNegOne_zeroSix_false_of_ledger
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
    (haa1 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 1)
    (hsame0 : ∀ x ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp)).filter fun y ↦
          ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
            s y.1 = s x.1).card = 0)
    (htf0 : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0) : False := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  have hdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc z
  have hcommInt : K.adjMatrix ℤ * H.adjMatrix ℤ =
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
  have hsame0coord : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u i).1 ∧ K.Adj (u i) (u j)).card = 0 := by
    intro i
    rw [coordinate_sameSign_adj_card_eq_support K A u huinj hurangeA
      (fun x : c.supp ↦ s x.1) i]
    have huiA : u i ∈ A :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hua i⟩
    simpa [A, K, and_comm] using hsame0 (u i) huiA
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
  have havoid : ∀ i, ¬ K.Adj (u i) (u (i - 1)) ∧
      ¬ K.Adj (u i) (u (i + 1)) := by
    intro i
    constructor
    · intro hK
      have hHi : H.Adj (u i) (u (i - 1)) := by
        rw [← H.mem_neighborFinset, hu]
        simp
      have htf : (triangleFreeEdgeGraph G).Adj
          (u i).1 (u (i - 1)).1 := by
        rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact ⟨hHi, hK⟩
      have hpos : 0 < (triangleFreeEdgeGraph G).degree (u i).1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨(u (i - 1)).1,
          ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf⟩
      rw [htf0 (u i) (hua i)] at hpos
      omega
    · intro hK
      have hHi : H.Adj (u i) (u (i + 1)) := by
        rw [← H.mem_neighborFinset, hu]
        simp
      have htf : (triangleFreeEdgeGraph G).Adj
          (u i).1 (u (i + 1)).1 := by
        rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact ⟨hHi, hK⟩
      have hpos : 0 < (triangleFreeEdgeGraph G).degree (u i).1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨(u (i + 1)).1,
          ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf⟩
      rw [htf0 (u i) (hua i)] at hpos
      omega
  exact graph_zmodEight_selfCell_zeroSix_false H K a u huinj hurange hu
    hdegree hcommInt hcommReal haa1 (fun x : c.supp ↦ s x.1)
      (fun i ↦ hs_in _ (u i).2) hflip hsame0coord havoid

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_zeroSix_false_of_ledger
