import Proofs.Erdos85SizeTwoMuNegOneAlignedLedger
import Proofs.Erdos85SizeTwoMuNegOneSelfCellZeroSixRouter

/-! # Refined exact sector routing for μ=-1 -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact μ=-1 sector cells after deleting the impossible all-triangle
`(k,r)=(0,6)` cell. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_refined_sector_cells
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
    ∃ k r : ℕ,
      ((MuNegOneC8CycleEntriesZero N₁ ∧ MuNegOneC8CycleEntriesZero N₂) ∧
        ((k = 0 ∧ r = 5) ∨ (k = 0 ∧ r = 7) ∨
         (k = 1 ∧ r = 4) ∨ (k = 1 ∧ r = 5) ∨ (k = 1 ∧ r = 6))) ∨
      ((((MuNegOneC8CycleEntriesZero N₁ ∧ MuNegOneC8CycleEntriesOne N₂) ∨
          (MuNegOneC8CycleEntriesOne N₁ ∧ MuNegOneC8CycleEntriesZero N₂))) ∧
        ((k = 0 ∧ r = 5) ∨ (k = 1 ∧ r = 4))) ∨
      ((MuNegOneC8CycleEntriesOne N₁ ∧ MuNegOneC8CycleEntriesOne N₂) ∧
        ((k = 0 ∧ r = 3) ∨ (k = 0 ∧ r = 4) ∨ (k = 0 ∧ r = 5) ∨
         (k = 1 ∧ r = 2) ∨ (k = 1 ∧ r = 3) ∨ (k = 1 ∧ r = 4))) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨k, r, hk, hr2, hr7, hbase, hupper, _ha8, _hb8,
      haa, _habq, _hbaq, _hbb, hA, _hB, _hcrossA, _hcrossB,
      hsector₁, hsector₂, hgrid⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_alignedLedger
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  let allZero := MuNegOneC8CycleEntriesZero N₁ ∧
    MuNegOneC8CycleEntriesZero N₂
  let mixed := (MuNegOneC8CycleEntriesZero N₁ ∧
      MuNegOneC8CycleEntriesOne N₂) ∨
    (MuNegOneC8CycleEntriesOne N₁ ∧ MuNegOneC8CycleEntriesZero N₂)
  let allOne := MuNegOneC8CycleEntriesOne N₁ ∧
    MuNegOneC8CycleEntriesOne N₂
  have hgrid' : (allZero ∧ 5 ≤ r + k) ∨
      (mixed ∧ r + k = 5) ∨ (allOne ∧ r + k ≤ 5) := by
    simpa [allZero, mixed, allOne, N₁, N₂, K, and_assoc] using hgrid
  have hcases := sizeTwoMuNegOne_sector_parameter_cases k r
    allZero mixed allOne hk hr2 hr7 hbase hupper hgrid'
  refine ⟨k, r, ?_⟩
  rcases hcases with ⟨hz, hcell⟩ | ⟨hm, hcell⟩ | ⟨ho, hcell⟩
  · left
    refine ⟨by simpa [allZero, N₁, N₂, K, SimpleGraph.adjMatrix_apply] using hz, ?_⟩
    rcases hcell with hcell | hcell | hcell | hcell | hcell | hcell
    · exact Or.inl hcell
    · exfalso
      exact orderSixtyFour_sizeTwo_muNegOne_zeroSix_false_of_parameters
        G hfree hreg hcard c hc s hs_out hs_in hH a u huinj hurange hu
          k r hcell.1 hcell.2 haa hA (by simpa [allZero, N₁, N₂, K] using hz.1)
    · exact Or.inr (Or.inl hcell)
    · exact Or.inr (Or.inr (Or.inl hcell))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hcell)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hcell)))
  · right; left
    exact ⟨by simpa [mixed, N₁, N₂, K, SimpleGraph.adjMatrix_apply] using hm, hcell⟩
  · right; right
    exact ⟨by simpa [allOne, N₁, N₂, K, SimpleGraph.adjMatrix_apply] using ho, hcell⟩

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_refined_sector_cells
