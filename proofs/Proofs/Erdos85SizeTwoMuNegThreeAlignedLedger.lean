import Proofs.Erdos85SizeTwoMuNegThreeSectorSwitchRouting

/-! # Aligned quotient, sign, and sector ledger for μ=-3 -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- One shared `(k,r)` witness carrying every graph ledger consumed by the
μ=-3 cell terminals.  Unlike the projected exact-cell theorem, this result
retains the quotient and signed-row facts that define its parameters. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_alignedLedger
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
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
    let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ,
      k ≤ 2 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      a.supp.ncard = 8 ∧ b.supp.ncard = 8 ∧
      componentQuotientMatrix K H a a = 7 - r ∧
      componentQuotientMatrix K H a b = r ∧
      componentQuotientMatrix K H b a = r ∧
      componentQuotientMatrix K H b b = 7 - r ∧
      (∀ x ∈ A,
        (A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = k) ∧
      (∀ x ∈ B,
        (B.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = k) ∧
      (∀ x ∈ A,
        (B.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = 2 - k) ∧
      (∀ x ∈ B,
        (A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = 2 - k) ∧
      (C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁) ∧
      (C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨ha8, hb8, r, hr2, hr7, haa, habq, hbaq, hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨k, hk, hA, hB, hcrossA, hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hsector₁ : C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁ := by
    simpa [N₁, K] using
      (binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector
        G hfree hreg hcard c hc a u hurange hu)
  have hsector₂ : C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂ := by
    simpa [N₂, K] using
      (binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector
        G hfree hreg hcard c hc b v hvrange hv)
  exact ⟨k, r, hk, hr2, hr7, ha8, hb8, haa, habq, hbaq, hbb,
    hA, hB, hcrossA, hcrossB, hsector₁, hsector₂⟩

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_alignedLedger
