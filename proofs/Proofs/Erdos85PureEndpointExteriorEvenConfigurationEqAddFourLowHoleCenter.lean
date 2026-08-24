import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddFourPrivateSupport
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationGeneralCenterParity

/-! # A low-hole full center in the `m+4` stratum -/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- A nonempty finite family whose total is at most four times its size has
an entry at most four. -/
theorem exists_le_four_of_sum_le_four_mul_card
    {α : Type*} [DecidableEq α] (F : Finset α) (f : α → ℕ)
    (hF : F.Nonempty) (hsum : (∑ x ∈ F, f x) ≤ 4 * F.card) :
    ∃ x ∈ F, f x ≤ 4 := by
  classical
  by_contra h
  have hall : ∀ x ∈ F, 5 ≤ f x := by
    intro x hx
    have hnle : ¬f x ≤ 4 := by
      intro hle
      exact h ⟨x, hx, hle⟩
    omega
  have hlow : 5 * F.card ≤ ∑ x ∈ F, f x := by
    calc
      5 * F.card = ∑ x ∈ F, 5 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ F, f x := by
        apply sum_le_sum
        intro x hx
        exact hall x hx
  have hpos := card_pos.mpr hF
  omega

set_option maxHeartbeats 800000 in
/-- Every endpoint `m+4` even configuration has a full center omitted by an
even number of rows no greater than four. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_exists_lowHoleCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let K := fun w : W =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 4 →
      ∃ i ∈ F, Even ((T.filter fun w => i ∈ K w).card) ∧
        (T.filter fun w => i ∈ K w).card ≤ 4 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard
  have hprivate :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_privateSupport
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hFcard : F.card = q := by simpa [F] using hCcard
  have hFnonempty : F.Nonempty := by
    apply card_pos.mp
    rw [hFcard]
    omega
  have hswap :
      (∑ w ∈ T, (K w).card) =
        ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
    calc
      (∑ w ∈ T, (K w).card) =
          ∑ w ∈ T, ∑ i ∈ F, if i ∈ K w then 1 else 0 := by
        apply sum_congr rfl
        intro w _hw
        have hsub : K w ⊆ F := inter_subset_right
        have heq : K w = F.filter fun i => i ∈ K w := by
          ext i
          constructor
          · intro hi
            exact mem_filter.mpr ⟨hsub hi, hi⟩
          · intro hi
            exact (mem_filter.mp hi).2
        calc
          (K w).card = (F.filter fun i => i ∈ K w).card :=
            congrArg card heq
          _ = ∑ i ∈ F, if i ∈ K w then 1 else 0 := card_filter _ _
      _ = ∑ i ∈ F, ∑ w ∈ T, if i ∈ K w then 1 else 0 := by
        rw [sum_comm]
      _ = ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
        apply sum_congr rfl
        intro i _hi
        rw [card_filter]
  have hcenterSum :
      (∑ i ∈ F, (T.filter fun w => i ∈ K w).card) ≤ 4 * F.card := by
    rw [← hswap, hFcard]
    exact hprivate.2.2
  obtain ⟨i, hiF, hiLow⟩ :=
    exists_le_four_of_sum_le_four_mul_card F
      (fun i => (T.filter fun w => i ∈ K w).card) hFnonempty hcenterSum
  have hTcardEven : Even T.card := by
    rw [hTcard]
    rcases hmEven with ⟨a, ha⟩
    refine ⟨a + 2, ?_⟩
    omega
  have hiEven :=
    (c4Free_binarySquare_pureEndpoint_evenConfiguration_centerHoleParity_iff
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
      T heven i hiF).mpr hTcardEven
  exact ⟨i, hiF, by simpa [K, F] using hiEven, hiLow⟩

end

end Erdos85

#print axioms Erdos85.exists_le_four_of_sum_le_four_mul_card
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_exists_lowHoleCenter
