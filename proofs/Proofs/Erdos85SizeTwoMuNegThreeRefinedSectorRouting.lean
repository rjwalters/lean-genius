import Proofs.Erdos85SizeTwoMuNegThreeAlignedLedger
import Proofs.Erdos85SizeTwoMuNegThreeSelfCellZeroFourRouter

/-! # Refined exact sector routing for μ=-3 -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact μ=-3 sector cells after deleting the impossible all-triangle-free
`(k,r)=(0,4)` cell.  The witness is the authoritative aligned-ledger witness,
so the deletion uses its own quotient and signed-row data. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_refined_sector_cells
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
        s y = (-3 : ℤ) * s z)
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
    ∃ k r : ℕ,
      (C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂ ∧
        MuNegThreeBothTriangleCell k r) ∨
      ((((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
          (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∧
            MuNegThreeMixedCell k r) ∨
        (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ ∧
          ((k = 0 ∧ r = 3) ∨ (k = 0 ∧ r = 5) ∨
           (k = 1 ∧ r = 2) ∨ (k = 1 ∧ r = 3) ∨
           (k = 1 ∧ r = 4)))) := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨k, r, hk, hr2, hr7, hlower, hupper, hgrid,
      _ha8, _hb8, haa, _habq, _hbaq, _hbb, hA, _hB,
      _hcrossA, _hcrossB, _hsector₁, _hsector₂⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_alignedLedger
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  have hcases := muNegThree_sector_grid_discrete N₁ N₂ k r
    hk hr2 hr7 hlower hupper hgrid
  refine ⟨k, r, ?_⟩
  rcases hcases with hzero | hmixed | hone
  · exact Or.inl hzero
  · exact Or.inr (Or.inl hmixed)
  · right; right
    refine ⟨hone.1, hone.2.1, ?_⟩
    dsimp [MuNegThreeBothTriangleFreeCell] at hone
    rcases hone.2.2 with hcell | hcell | hcell | hcell | hcell | hcell
    · exact Or.inl hcell
    · exfalso
      exact orderSixtyFour_sizeTwo_muNegThree_zeroFour_false_of_parameters
        G hfree hreg hcard c hc s hs_out hs_in hH a u huinj hurange hu
          k r hcell.1 hcell.2 haa hA hone.1
    · exact Or.inr (Or.inl hcell)
    · exact Or.inr (Or.inr (Or.inl hcell))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hcell)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hcell)))

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_refined_sector_cells
