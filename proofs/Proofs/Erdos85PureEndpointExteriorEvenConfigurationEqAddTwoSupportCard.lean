import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddTwoPairMultiplicity

/-!
# Exact shore support of an `m+2` circuit

Uniform row size and point multiplicity two determine the exact number of
points used by the circuit through the incidence double count.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- A uniform incidence configuration supported inside `L`, with every used
point occurring twice, uses exactly half of its total row-incidence mass. -/
theorem uniform_degreeTwo_configuration_support_mass
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (L : Finset β) (m : ℕ)
    (hsub : ∀ a ∈ T, B a ⊆ L)
    (hcard : ∀ a ∈ T, (B a).card = m)
    (hpoint : ∀ y ∈ L, (T.filter fun a => y ∈ B a).Nonempty →
      (T.filter fun a => y ∈ B a).card = 2) :
    2 * (L.filter fun y => (T.filter fun a => y ∈ B a).Nonempty).card =
      T.card * m := by
  classical
  let d : β → ℕ := fun y => (T.filter fun a => y ∈ B a).card
  have hleft : (∑ a ∈ T, (B a).card) = T.card * m := by
    rw [Finset.sum_congr rfl (fun a ha => hcard a ha)]
    simp
  have hswap : (∑ a ∈ T, (B a).card) = ∑ y ∈ L, d y := by
    calc
      (∑ a ∈ T, (B a).card) =
          ∑ a ∈ T, ∑ y ∈ L, if y ∈ B a then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.card_filter]
        congr 1
        ext y
        simp only [Finset.mem_filter]
        exact (and_iff_right_of_imp (fun hy => hsub a ha hy)).symm
      _ = ∑ y ∈ L, ∑ a ∈ T, if y ∈ B a then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ y ∈ L, d y := by
        apply Finset.sum_congr rfl
        intro y _hy
        simp only [d, Finset.card_filter]
  have hright : (∑ y ∈ L, d y) =
      2 * (L.filter fun y => (T.filter fun a => y ∈ B a).Nonempty).card := by
    calc
      (∑ y ∈ L, d y) = ∑ y ∈ L,
          if (T.filter fun a => y ∈ B a).Nonempty then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hu : (T.filter fun a => y ∈ B a).Nonempty
        · simp [hu, d, hpoint y hy hu]
        · have hz : d y = 0 := by
            exact Finset.card_eq_zero.mpr
              (Finset.not_nonempty_iff_eq_empty.mp hu)
          simp [hu, hz]
      _ = 2 * (L.filter fun y =>
          (T.filter fun a => y ∈ B a).Nonempty).card := by
        rw [← Finset.sum_filter]
        simp [Nat.mul_comm]
  omega

set_option maxHeartbeats 800000 in
/-- An endpoint `m+2` even configuration uses exactly `(m/2)(m+2)` shore
points. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_supportCard
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
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 2 →
      (S.filter fun y => (T.filter fun w => y ∈ row w).Nonempty).card =
        (m / 2) * (m + 2) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hrowCard : ∀ w ∈ T, (row w).card = m := by
    intro w _hw
    exact hdesign.1 w.1 (by simpa [F] using Finset.mem_compl.mp w.2)
  have hpointOnRow :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_pointMultiplicity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hpoint : ∀ y ∈ S, (T.filter fun w => y ∈ row w).Nonempty →
      (T.filter fun w => y ∈ row w).card = 2 := by
    intro y _hyS hy
    obtain ⟨w, hw⟩ := hy
    have hwData := Finset.mem_filter.mp hw
    exact hpointOnRow w hwData.1 y hwData.2
  have hmass := uniform_degreeTwo_configuration_support_mass
    row T S m (fun w _hw => Finset.inter_subset_right) hrowCard hpoint
  rcases hmEven with ⟨a, ha⟩
  have hmHalf : m / 2 = a := by omega
  change (S.filter fun y =>
    (T.filter fun w => y ∈ row w).Nonempty).card = (m / 2) * (m + 2)
  rw [hTcard, ha] at hmass
  rw [hmHalf, ha]
  apply Nat.mul_left_cancel (n := 2)
  · omega
  · rw [hmass]
    ring

end

end Erdos85

#print axioms Erdos85.uniform_degreeTwo_configuration_support_mass
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_supportCard
