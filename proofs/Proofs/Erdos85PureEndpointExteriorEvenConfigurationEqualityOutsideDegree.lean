import Proofs.Erdos85PureEndpointExteriorEvenConfigurationIntersectionParity

/-! # Outside-degree cap for a minimum exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- An even number bounded by the successor of an even number is bounded by
the even number itself. -/
theorem even_le_of_le_succ_even {a m : ℕ}
    (ha : Even a) (hm : Even m) (h : a ≤ m + 1) : a ≤ m := by
  rcases ha with ⟨u, rfl⟩
  rcases hm with ⟨v, rfl⟩
  omega

/-- In an equality-size even exterior configuration, each exterior row
outside the configuration meets at most `m` selected rows. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_outsideDegree_le
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
      T.card = m + 1 →
      ∀ w : W, w ∉ T →
        (T.filter fun u => (row w ∩ row u).Nonempty).card ≤ m := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard w hwT
  let Inc : W → V → Prop := fun u y => y ∈ row u
  have heven' : ∀ y ∈ (univ : Finset V),
      Even ((T.filter fun u => Inc u y).card) := by
    intro y _hy
    by_cases hyS : y ∈ S
    · let yy : P := ⟨y, hyS⟩
      simpa [Inc, row, hyS] using heven yy
    · have hz : T.filter (fun u => Inc u y) = ∅ := by
        ext u
        simp [Inc, row, hyS]
      rw [hz]
      exact ⟨0, rfl⟩
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hlinear : ∀ u ∈ T,
      ((univ : Finset V).filter fun y => Inc w y ∧ Inc u y).card ≤ 1 := by
    intro u huT
    have hwu : w.1 ≠ u.1 := by
      intro h
      apply hwT
      simpa [Subtype.ext h] using huT
    have h := hdesign.2.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
      u.1 (by simpa [F] using (mem_compl.mp u.2)) hwu
    have heq : ((univ : Finset V).filter fun y =>
        Inc w y ∧ Inc u y) = row w ∩ row u := by
      ext y
      simp [Inc, row, and_assoc, and_left_comm, and_comm]
    rw [heq]
    exact h
  have hparity := linear_even_configuration_meeting_card_even
    Inc T (univ : Finset V) w heven' hlinear
  have hsame : (T.filter fun u =>
      ((univ : Finset V).filter fun y => Inc w y ∧ Inc u y).Nonempty) =
      T.filter fun u => (row w ∩ row u).Nonempty := by
    ext u
    simp only [mem_filter]
    apply and_congr_right
    intro _huT
    have heq : ((univ : Finset V).filter fun y =>
        Inc w y ∧ Inc u y) = row w ∩ row u := by
      ext y
      simp [Inc, row, and_assoc, and_left_comm, and_comm]
    rw [heq]
  rw [hsame] at hparity
  apply even_le_of_le_succ_even hparity hmEven
  rw [← hTcard]
  exact card_filter_le _ _

end

end Erdos85

#print axioms Erdos85.even_le_of_le_succ_even
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_outsideDegree_le
