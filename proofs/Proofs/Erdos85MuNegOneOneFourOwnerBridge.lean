import Proofs.Erdos85MuNegOneOneFourFiniteInstantiation
import Proofs.Erdos85SizeTwoSwitchedJointExtension

/-!
# Ambient ledger-pinned terminal for the μ=-1 `(1,4)` cell

Node: outline F.3 negative-lane assembly (endpoint callback for the
global orbit spine; squad msgs 14249/14256/14258).

The h114 endpoint callback in the exact shape the global assembly
consumes: an ambient signed joint at `θ = -1` whose first shore carries
diagonal quotient `3` and same-sign defect row count `1` is impossible.
The supplied ledger facts pin the aligned-ledger cell at `(1,4)`; the
complete exterior geometry is then reconstructed and fed to the checked
owner certificates.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **Ambient `(1,4)` terminal.** -/
theorem muNegOneOneFour_ambient_false_of_oneFour_ledger
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s : V → ℤ) (hs : IsAmbientSignedJoint G c (-1) s)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hkOne : ∃ x ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp),
      ((((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp).filter
        fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
          s y.1 = s x.1).card = 1)) :
    False := by
  classical
  obtain ⟨hs_out, hs_in, hH, hD⟩ := hs
  obtain ⟨k, r, hcell, ha8, hb8, haa, habq, hbaq, hbb,
      hA, hB, hcrossA, hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_refined_alignedLedger
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  -- the supplied ledger facts pin the aligned cell at (1,4).
  obtain rfl : r = 4 := by
    have h74 : 7 - r = 3 := by
      rw [← haa]
      exact haa3
    omega
  obtain rfl : k = 1 := by
    obtain ⟨x, hxA, hx1⟩ := hkOne
    have hxk := hA x hxA
    have : (1 : ℕ) = k := by
      rw [← hx1]
      exact hxk
    omega
  -- reconstruct the complete exterior geometry (structure-theorem
  -- self-branch, inlined).
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have flip_of_coordinates
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
      hs_in hs_out hAfull (w i).2).2 _ hmem
  have hurangeA : Set.range u =
      ↑((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp) := by
    rw [hurange]
    ext x
    simp
  have hvrangeB : Set.range v =
      ↑((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp) := by
    rw [hvrange]
    ext x
    simp
  have hdiagU : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u i).1 ∧
          ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j)).card
        = 1 := by
    intro i
    rw [coordinate_sameSign_adj_card_eq_support
      ((secondOrderDefectGraph G).induce c.supp)
      ((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp)
      u huinj hurangeA (fun x : c.supp ↦ s x.1) i]
    exact hA (u i) (by
      change u i ∈
        (↑((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp) :
          Set c.supp)
      rw [← hurangeA]
      exact ⟨i, rfl⟩)
  have hdiagV : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (v i).1 ∧
          ((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j)).card
        = 1 := by
    intro i
    rw [coordinate_sameSign_adj_card_eq_support
      ((secondOrderDefectGraph G).induce c.supp)
      ((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp)
      v hvinj hvrangeB (fun x : c.supp ↦ s x.1) i]
    exact hB (v i) (by
      change v i ∈
        (↑((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp) :
          Set c.supp)
      rw [← hvrangeB]
      exact ⟨i, rfl⟩)
  have hgeom :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_oneFour_completeExteriorGeometry
      G hfree hreg hcard c hc a b ha8 hb8 hab u v huinj hvinj
        hurange hvrange hu hv s (fun i ↦ hs_in _ (u i).2)
        (fun j ↦ hs_in _ (v j).2) (flip_of_coordinates u hu)
        (flip_of_coordinates v hv) (by simpa using haa) (by simpa using hbb)
        (by simpa using habq) hdiagU hdiagV (by simpa using hcrossA)
        (by simpa using hcrossB)
  exact muNegOneOneFour_graph_false G c hfree hreg hcard hc a b hab
    u v huinj hvinj hurange hvrange hu hv
    (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
    (fun i ↦ hs_in _ (u i).2) (fun j ↦ hs_in _ (v j).2)
    (flip_of_coordinates u hu) (flip_of_coordinates v hv) hgeom

end

end Erdos85

#print axioms Erdos85.muNegOneOneFour_ambient_false_of_oneFour_ledger
