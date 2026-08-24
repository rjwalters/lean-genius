import Proofs.Erdos85PureEndpointExteriorEvenConfigurationCenterMatching

/-!
# Minimum-hole rigidity for an equality circuit

Centerwise oddness forces at least one hole at every full center.  Since total
hole mass is even, it is either the minimum `q` or at least `q+2`.  At the
minimum, every center has exactly one hole and all support counts are rigid.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- The total hole mass of an equality circuit either exceeds its centerwise
minimum by at least two, or the entire center/private-support profile is
forced. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_holeMassDichotomy
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
    let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
    let R₁ := S.filter fun y => (owner y).card = 1
    let K : W → Finset V := fun w =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      let H := ∑ w ∈ T, (K w).card
      let U := R₁.filter fun y => (T.filter fun w => G.Adj w.1 y).Nonempty
      (H = q ∧
        (∀ i ∈ F, (T.filter fun w => i ∈ K w).card = 1) ∧
        U.card = m ∧
        ∀ i ∈ F,
          let Uᵢ := S.filter fun y =>
            i ∈ owner y ∧ (T.filter fun w => G.Adj w.1 y).Nonempty
          2 * Uᵢ.card = m) ∨
      q + 2 ≤ H := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard
  let H := ∑ w ∈ T, (K w).card
  let U := R₁.filter fun y => (T.filter fun w => G.Adj w.1 y).Nonempty
  have hcenter :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerHoleParity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hprivate :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_privateSupport
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hmassEq : H = 2 * U.card := by
    simpa [H, U, K, R₁, owner, F] using hprivate.2.1
  have hHLower : q ≤ H := by simpa [H, K, F] using hcenter.2
  have hHEven : Even H := ⟨U.card, by omega⟩
  have hqEven : Even q := ⟨m, by omega⟩
  by_cases hmin : H = q
  · left
    have hswap : H =
        ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
      calc
        H = ∑ w ∈ T, ∑ i ∈ F, if i ∈ K w then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro w _hw
          have hsub : K w ⊆ F := Finset.inter_subset_right
          rw [← Finset.sum_subset hsub]
          · simp [H]
          · intro i _hiF hiK
            simp [hiK]
        _ = ∑ i ∈ F, ∑ w ∈ T, if i ∈ K w then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.card_filter]
    have honeLe : ∀ i ∈ F, 1 ≤ (T.filter fun w => i ∈ K w).card := by
      intro i hiF
      have hiOdd : Odd ((T.filter fun w => i ∈ K w).card) := by
        simpa [K, F] using hcenter.1 i hiF
      rcases hiOdd with ⟨a, ha⟩
      omega
    have hcenterOne : ∀ i ∈ F,
        (T.filter fun w => i ∈ K w).card = 1 := by
      have hsumEq : (∑ i ∈ F, (T.filter fun w => i ∈ K w).card) =
          ∑ _i ∈ F, 1 := by
        rw [← hswap, hmin]
        simpa [F] using hCcard.symm
      have hall := (Finset.sum_eq_sum_iff_of_le honeLe).mp hsumEq.symm
      intro i hiF
      exact (hall i hiF).symm
    have hUcard : U.card = m := by
      rw [hmin, hqm] at hmassEq
      omega
    refine ⟨hmin, hcenterOne, hUcard, ?_⟩
    intro i hiF
    let Uᵢ := S.filter fun y =>
      i ∈ owner y ∧ (T.filter fun w => G.Adj w.1 y).Nonempty
    have hmatching :=
      c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerMatching
        G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
        T heven hTcard i hiF
    change 2 * Uᵢ.card = m
    have hiOne := hcenterOne i hiF
    change (T.filter fun w => i ∈ K w).card = 1 at hiOne
    have hmatchEq : 2 * Uᵢ.card +
        (T.filter fun w => i ∈ K w).card = m + 1 := by
      simpa [Uᵢ, owner, K, F] using hmatching.1
    omega
  · right
    rcases hHEven with ⟨a, ha⟩
    rcases hqEven with ⟨b, hb⟩
    have hab : b + 1 ≤ a := by omega
    calc
      q + 2 = (b + b) + 2 := by omega
      _ ≤ a + a := by omega
      _ = H := by omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_holeMassDichotomy
