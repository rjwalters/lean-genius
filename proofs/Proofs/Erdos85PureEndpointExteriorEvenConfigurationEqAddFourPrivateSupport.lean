import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddFourLocalMultiplicity
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationPrivateSupport

/-! # Weighted private support in the `m+4` stratum -/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- If every nonempty fiber over `R` has cardinality two or four, its total
mass is twice the support size plus twice the quartic-fiber count. -/
theorem sum_fiberCard_eq_two_mul_support_add_two_mul_quartic
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : Finset α) (A : α → Finset β)
    (hcard : ∀ x ∈ R, (A x).Nonempty → (A x).card = 2 ∨ (A x).card = 4) :
    let U := R.filter fun x => (A x).Nonempty
    let Q := R.filter fun x => (A x).card = 4
    (∑ x ∈ R, (A x).card) = 2 * U.card + 2 * Q.card := by
  classical
  dsimp only
  let U := R.filter fun x => (A x).Nonempty
  let Q := R.filter fun x => (A x).card = 4
  calc
    (∑ x ∈ R, (A x).card) =
        ∑ x ∈ R, ((2 * (if (A x).Nonempty then 1 else 0)) +
          (2 * (if (A x).card = 4 then 1 else 0))) := by
      apply sum_congr rfl
      intro x hx
      by_cases hn : (A x).Nonempty
      · rcases hcard x hx hn with htwo | hfour
        · simp [hn, htwo]
        · simp [hn, hfour]
      · have hz : A x = ∅ := not_nonempty_iff_eq_empty.mp hn
        simp [hz]
    _ = 2 * U.card + 2 * Q.card := by
      have hU : U.card =
          ∑ x ∈ R, if (A x).Nonempty then 1 else 0 := by
        dsimp [U]
        rw [card_filter]
      have hQ : Q.card =
          ∑ x ∈ R, if (A x).card = 4 then 1 else 0 := by
        dsimp [Q]
        rw [card_filter]
      rw [hU, hQ, Finset.mul_sum, Finset.mul_sum]
      simp only [sum_add_distrib, mul_ite, mul_one, mul_zero]

/-- For an endpoint exterior even configuration of size `m+4`, total
full-center hole mass equals twice the used private support plus twice its
quartic sublayer.  In particular it is at most `4q`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_privateSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcardV : Fintype.card V = q * q)
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
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 4 →
      let U := R₁.filter fun y => (T.filter fun w => y ∈ row w).Nonempty
      let Q₄ := R₁.filter fun y => (T.filter fun w => y ∈ row w).card = 4
      R₁.card = q ∧
        (∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) =
            2 * U.card + 2 * Q₄.card ∧
        (∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) ≤ 4 * q := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard
  let U := R₁.filter fun y => (T.filter fun w => y ∈ row w).Nonempty
  let Q₄ := R₁.filter fun y => (T.filter fun w => y ∈ row w).card = 4
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcardV S hempty hCcard hshore htri
  have hloc :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_localMultiplicity
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven hTcard
  have hfiber : ∀ y ∈ R₁, (T.filter fun w => y ∈ row w).Nonempty →
      (T.filter fun w => y ∈ row w).card = 2 ∨
      (T.filter fun w => y ∈ row w).card = 4 := by
    intro y _hyR hyUsed
    obtain ⟨w, hw⟩ := hyUsed
    have hwData := mem_filter.mp hw
    rcases hloc w hwData.1 with hthree | hone
    · exact Or.inl (hthree.2 y hwData.2)
    · by_cases hySpecial : y = hone.2.choose
      · subst y
        exact Or.inr hone.2.choose_spec.1.2.1
      · exact Or.inl
          (hone.2.choose_spec.1.2.2 y hwData.2 hySpecial)
  have hpoint : ∀ w : W,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card =
        (row w ∩ R₁).card := by
    intro w
    have hwF : w.1 ∉ F := mem_compl.mp w.2
    rw [(hnear w.1 hwF).2.1]
    congr 1
    ext y
    simp [F, owner, R₁, row]
  have hswap :
      (∑ w ∈ T, (row w ∩ R₁).card) =
        ∑ y ∈ R₁, (T.filter fun w => y ∈ row w).card := by
    calc
      (∑ w ∈ T, (row w ∩ R₁).card) =
          ∑ w ∈ T, ∑ y ∈ R₁, if y ∈ row w then 1 else 0 := by
        apply sum_congr rfl
        intro w _hw
        rw [show row w ∩ R₁ = R₁.filter (fun y => y ∈ row w) by
          ext y
          simp [and_comm]]
        rw [card_filter]
      _ = ∑ y ∈ R₁, ∑ w ∈ T, if y ∈ row w then 1 else 0 := by
        rw [sum_comm]
      _ = ∑ y ∈ R₁, (T.filter fun w => y ∈ row w).card := by
        apply sum_congr rfl
        intro y _hy
        rw [card_filter]
  have hweighted :=
    sum_fiberCard_eq_two_mul_support_add_two_mul_quartic
      R₁ (fun y => T.filter fun w => y ∈ row w) hfiber
  change (∑ y ∈ R₁, (T.filter fun w => y ∈ row w).card) =
    2 * U.card + 2 * Q₄.card at hweighted
  have hmass : (∑ w ∈ T,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) =
        2 * U.card + 2 * Q₄.card := by
    rw [sum_congr rfl (fun w _hw => hpoint w), hswap, hweighted]
  have hRcard : R₁.card = q := by
    simpa [R₁, owner, F] using
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcardV S hempty hCcard hshore htri).2.1
  refine ⟨hRcard, hmass, ?_⟩
  rw [hmass]
  have hUle : U.card ≤ q := by
    calc U.card ≤ R₁.card := card_filter_le _ _
      _ = q := hRcard
  have hQle : Q₄.card ≤ q := by
    calc Q₄.card ≤ R₁.card := card_filter_le _ _
      _ = q := hRcard
  omega

end

end Erdos85

#print axioms Erdos85.sum_fiberCard_eq_two_mul_support_add_two_mul_quartic
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_privateSupport
