import Proofs.Erdos85PureEndpointExteriorEvenConfigurationGeneralCenterParity

/-!
# Hole pressure in every odd circuit

The unrestricted center parity law implies that every odd-cardinality even
configuration omits every full center a positive odd number of times.  Double
counting center holes gives total hole mass at least `q`.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- Every odd exterior even configuration has an odd positive hole fiber at
each center and total hole mass at least `q`. -/
theorem c4Free_binarySquare_pureEndpoint_odd_evenConfiguration_centerHoleMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
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
    let K : W → Finset V := fun w =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      Odd T.card →
      (∀ i ∈ F, Odd ((T.filter fun w => i ∈ K w).card)) ∧
      q ≤ ∑ w ∈ T, (K w).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTOdd
  have hparity :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_centerHoleParity_iff
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri T heven
  have hcenterOdd : ∀ i ∈ F,
      Odd ((T.filter fun w => i ∈ K w).card) := by
    intro i hiF
    apply Nat.not_even_iff_odd.mp
    intro hholeEven
    have hTEven : Even T.card := by
      apply (hparity i hiF).mp
      simpa [K, F] using hholeEven
    rcases hTOdd with ⟨a, ha⟩
    rcases hTEven with ⟨b, hb⟩
    omega
  refine ⟨hcenterOdd, ?_⟩
  have hswap : (∑ w ∈ T, (K w).card) =
      ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
    calc
      (∑ w ∈ T, (K w).card) =
          ∑ w ∈ T, ∑ i ∈ F, if i ∈ K w then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro w _hw
        have hsub : K w ⊆ F := Finset.inter_subset_right
        rw [← Finset.sum_subset hsub]
        · simp
        · intro i _hiF hiK
          simp [hiK]
      _ = ∑ i ∈ F, ∑ w ∈ T, if i ∈ K w then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.card_filter]
  rw [hswap]
  calc
    q = F.card := by simpa [F] using hCcard.symm
    _ = ∑ _i ∈ F, 1 := by simp
    _ ≤ ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
      apply Finset.sum_le_sum
      intro i hiF
      rcases hcenterOdd i hiF with ⟨a, ha⟩
      omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_odd_evenConfiguration_centerHoleMass
