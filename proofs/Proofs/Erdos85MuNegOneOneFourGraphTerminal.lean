import Proofs.Erdos85MuNegOneOneFourFiniteInstantiation
import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourStructure

/-!
# Graph-level terminal for the canonical h114 switch cell

This removes the three abstract mode callbacks from the older terminal
assembly.  The refined switch either leaves `(-1,1,4)`, or its complete
exterior geometry is fed directly to the checked owner-model elimination.
-/

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

theorem orderSixtyFour_sizeTwo_muNegOne_refined_switch_ne_self_of_oneFour
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
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ, MuNegOneRefinedSectorCells N₁ N₂ k r ∧
      sizeTwoMuSwitchTarget (-1) k r ≠ -1 := by
  classical
  dsimp only
  obtain ⟨k, r, hcell, hne | hgeom⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_refined_switch_or_completeExteriorGeometry
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  · exact ⟨k, r, hcell, hne⟩
  · have hfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
    have hflip
        (w : ZMod 8 → c.supp)
        (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
          {w (z - 1), w (z + 1)}) :
        ∀ i, s (w (i + 1)).1 = -s (w i).1 := by
      intro i
      have hadj : (G.induce c.supp).Adj (w i) (w (i + 1)) := by
        rw [← (G.induce c.supp).mem_neighborFinset, hw]
        simp
      have hmem : (w (i + 1)).1 ∈ componentNeighborFinset G
          (secondOrderDefectGraph G) c (w i).1 := by
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (w (i + 1)).2⟩
      exact (internal_alternation G hfree (by omega) hreg hcard c hc s
        hs_in hs_out hfull (w i).2).2 _ hmem
    exact False.elim <| muNegOneOneFour_graph_false G c
      hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange hu hv
      (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
      (fun i ↦ hs_in _ (u i).2) (fun j ↦ hs_in _ (v j).2)
      (hflip u hu) (hflip v hv) hgeom

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_refined_switch_ne_self_of_oneFour
