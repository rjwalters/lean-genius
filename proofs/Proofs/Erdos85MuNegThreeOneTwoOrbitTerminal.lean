import Proofs.Erdos85MuNegThreeOneTwoGraphTerminal
import Proofs.Erdos85SizeTwoMuNegThreeAlignedShoreSwitch
import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourSignPhaseRouting

/-!
# Orbit consumer for the `mu=-3`, `(k,r)=(1,2)` fixed switch cell

For aligned sign phases, the unique refined cell fixed by the shore switch is
fed directly to the checked h312 graph terminal.  Thus every surviving refined
witness genuinely leaves the `mu=-3` eigenvalue under the shore switch.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

theorem orderSixtyFour_sizeTwo_muNegThree_refined_switch_ne_self_of_oneTwo_aligned
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
      {v (z - 1), v (z + 1)})
    (hbase : s (u 0).1 = s (v 0).1) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (v j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ, MuNegThreeRefinedSectorCells N₁ N₂ k r ∧
      sizeTwoMuSwitchTarget (-3) k r ≠ -3 ∧
      componentQuotientMatrix K (G.induce c.supp) a a = 7 - r ∧
      MuNegThreeExplicitParameterLedger N₁ M₁
        (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  let M₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (u j)
  obtain ⟨k, r, hcell, _heigK, _heigH, _ht, _htsign, _hneOne,
      _hpost, _htargets, _hglobal, _hT, horient, haa, hbb, L₁, L₂⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_refined_shoreSwitch
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  by_cases hself : sizeTwoMuSwitchTarget (-3) k r = -3
  · have hkr :=
      (muNegThree_refined_switch_target_eq_self_iff N₁ N₂ k r hcell).mp hself
    obtain ⟨rfl, rfl⟩ := hkr
    have hphase := zmodEight_two_alternating_sign_phase_routing
      (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
      L₁.f_sign L₁.g_sign L₁.f_flip L₁.g_flip
    have hpar : ∀ i j : Nat, i < 8 → j < 8 →
        (s (v (j : ZMod 8)).1 = s (u (i : ZMod 8)).1 ↔
          i % 2 = j % 2) := by
      intro i j hi hj
      obtain ⟨hu0, hv0, hpu, hpv, _⟩ := hphase
      change s (u 0).1 = -1 ∨ s (u 0).1 = 1 at hu0
      change s (v 0).1 = -1 ∨ s (v 0).1 = 1 at hv0
      have hui : s (u (i : ZMod 8)).1 =
          (if i % 2 = 0 then s (u 0).1 else -s (u 0).1) := by
        by_cases he : i % 2 = 0
        · rw [if_pos he]
          have hpui : s (u (i : ZMod 8)).1 = s (u 0).1 ↔
              ZModEightEvenOffset (i : ZMod 8) := by
            simpa using hpu (i : ZMod 8)
          exact hpui.mpr (by
            interval_cases i <;> simp_all [ZModEightEvenOffset])
        · rw [if_neg he]
          have hne : s (u (i : ZMod 8)).1 ≠ s (u 0).1 := by
            intro h
            have hpui : s (u (i : ZMod 8)).1 = s (u 0).1 ↔
                ZModEightEvenOffset (i : ZMod 8) := by
              simpa using hpu (i : ZMod 8)
            have := hpui.mp h
            interval_cases i <;> contradiction
          rcases L₁.f_sign (i : ZMod 8) with h | h <;>
            rcases hu0 with h0 | h0 <;> rw [h, h0] <;>
            rw [h, h0] at hne <;> omega
      have hvj : s (v (j : ZMod 8)).1 =
          (if j % 2 = 0 then s (v 0).1 else -s (v 0).1) := by
        by_cases he : j % 2 = 0
        · rw [if_pos he]
          have hpvj : s (v (j : ZMod 8)).1 = s (v 0).1 ↔
              ZModEightEvenOffset (j : ZMod 8) := by
            simpa using hpv (j : ZMod 8)
          exact hpvj.mpr (by
            interval_cases j <;> simp_all [ZModEightEvenOffset])
        · rw [if_neg he]
          have hne : s (v (j : ZMod 8)).1 ≠ s (v 0).1 := by
            intro h
            have hpvj : s (v (j : ZMod 8)).1 = s (v 0).1 ↔
                ZModEightEvenOffset (j : ZMod 8) := by
              simpa using hpv (j : ZMod 8)
            have := hpvj.mp h
            interval_cases j <;> contradiction
          rcases L₁.g_sign (j : ZMod 8) with h | h <;>
            rcases hv0 with h0 | h0 <;> rw [h, h0] <;>
            rw [h, h0] at hne <;> omega
      rw [hui, hvj, ← hbase]
      rcases Nat.mod_two_eq_zero_or_one i with hi2 | hi2 <;>
        rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2 <;>
        rcases hu0 with h0 | h0 <;> simp [hi2, hj2, h0]
    have hD₁ : ∀ i j, i < 8 → j < 8 →
        muNegThreeCrossDefectRel G c u v i j =
          decide (M₁ (i : ZMod 8) (j : ZMod 8) = 1) := by
      intro i j _ _
      simp [muNegThreeCrossDefectRel, M₁, K, SimpleGraph.adjMatrix_apply]
    have hD₂ : ∀ i j, i < 8 → j < 8 →
        muNegThreeCrossDefectRel G c u v i j =
          decide (M₂ (j : ZMod 8) (i : ZMod 8) = 1) := by
      intro i j _ _
      simp [muNegThreeCrossDefectRel, M₂, K, SimpleGraph.adjMatrix_apply,
        SimpleGraph.adj_comm]
    exact False.elim <| muNegThree_graph_false_of_ledgers_diagonalFive
      G c hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange
        hu hv (by simpa [K, H] using haa) (by simpa [K, H] using hbb)
        L₁ L₂ hD₁ hD₂ hpar (horient rfl)
  · exact ⟨k, r, hcell, hself, haa, L₁⟩

/-- Phase-free orbit terminal.  If the two coordinate-zero signs disagree,
rotate the second C8 by one step, apply the aligned terminal there, and use
the invariant first-shore ledger and quotient entry to identify the returned
`k,r` with the original refined witness. -/
theorem orderSixtyFour_sizeTwo_muNegThree_refined_switch_ne_self_of_oneTwo
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
    ∃ k r : ℕ, MuNegThreeRefinedSectorCells N₁ N₂ k r ∧
      sizeTwoMuSwitchTarget (-3) k r ≠ -3 := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨k, r, hcell, _heigK, _heigH, _ht, _htsign, _hneOne,
      _hpost, _htargets, _hglobal, _hT, _horient, haa, _hbb, L₁, _L₂⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_refined_shoreSwitch
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  by_cases hbase : s (u 0).1 = s (v 0).1
  · obtain ⟨k', r', _hcell', hne, _haa', _L'⟩ :=
      orderSixtyFour_sizeTwo_muNegThree_refined_switch_ne_self_of_oneTwo_aligned
        G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
          u v huinj hvinj hurange hvrange hu hv hbase
    have hr : r = r' := by
      have hrsum := L₁.sum_le_six
      have hrsum' := _L'.sum_le_six
      have hr6 : r ≤ 6 := by omega
      have hr6' : r' ≤ 6 := by omega
      omega
    have hk : k = k' := by
      have hk0 := L₁.internal_same 0
      have hk0' := _L'.internal_same 0
      omega
    subst k'
    subst r'
    exact ⟨k, r, hcell, hne⟩
  · have hop : s (u 0).1 = -s (v 0).1 := by
      rcases L₁.f_sign 0 with hu0 | hu0 <;>
        rcases L₁.g_sign 0 with hv0 | hv0 <;> omega
    let vp : ZMod 8 → c.supp := fun j ↦ v (j + 1)
    have hvpinj : Function.Injective vp := by
      intro i j hij
      apply add_right_cancel (b := (1 : ZMod 8))
      exact hvinj hij
    have hvprange : Set.range vp = b.supp := by
      rw [← hvrange]
      ext z
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j + 1, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j - 1, by simp [vp]⟩
    have hvp : ∀ z, (G.induce c.supp).neighborFinset (vp z) =
        {vp (z - 1), vp (z + 1)} := by
      intro z
      simpa [vp] using hv (z + 1)
    have hvp0 : s (vp 0).1 = -s (v 0).1 := by
      simpa [vp] using L₁.g_flip 0
    have hbasep : s (u 0).1 = s (vp 0).1 := hop.trans hvp0.symm
    obtain ⟨k', r', _hcell', hne, haa', L'⟩ :=
      orderSixtyFour_sizeTwo_muNegThree_refined_switch_ne_self_of_oneTwo_aligned
        G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
          u vp huinj hvpinj hurange hvprange hu hvp hbasep
    have hr : r = r' := by
      have hrsum := L₁.sum_le_six
      have hrsum' := L'.sum_le_six
      have hr6 : r ≤ 6 := by omega
      have hr6' : r' ≤ 6 := by omega
      omega
    have hk : k = k' := by
      have hk0 := L₁.internal_same 0
      have hk0' := L'.internal_same 0
      omega
    subst k'
    subst r'
    exact ⟨k, r, hcell, hne⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_refined_switch_ne_self_of_oneTwo_aligned
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_refined_switch_ne_self_of_oneTwo
