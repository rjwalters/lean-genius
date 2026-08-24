import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEquality

/-! # Outside rows induce matchings on a minimum exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- If every used point has configuration degree two and an outside block
meets each selected block in at most one point, then its selected-block
meeting degree is twice the number of used points it contains. -/
theorem linear_degree_two_configuration_outside_meeting_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (p : α)
    (hpoint : ∀ y, (T.filter fun a => y ∈ B a).Nonempty →
      (T.filter fun a => y ∈ B a).card = 2)
    (hlinear : ∀ a ∈ T, ((B p) ∩ (B a)).card ≤ 1) :
    (T.filter fun a => ((B p) ∩ (B a)).Nonempty).card =
      2 * ((B p).filter fun y =>
        (T.filter fun a => y ∈ B a).Nonempty).card := by
  classical
  let d : β → ℕ := fun y => (T.filter fun a => y ∈ B a).card
  have hindicator : ∀ a ∈ T,
      (if ((B p) ∩ (B a)).Nonempty then 1 else 0) =
        ((B p) ∩ (B a)).card := by
    intro a ha
    by_cases hn : ((B p) ∩ (B a)).Nonempty
    · simp only [hn, if_true]
      exact Nat.le_antisymm (card_pos.mpr hn) (hlinear a ha)
    · simp only [hn, if_false]
      exact (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)).symm
  calc
    (T.filter fun a => ((B p) ∩ (B a)).Nonempty).card =
        ∑ a ∈ T, if ((B p) ∩ (B a)).Nonempty then 1 else 0 := by
      rw [card_filter]
    _ = ∑ a ∈ T, ((B p) ∩ (B a)).card := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hindicator a ha
    _ = ∑ a ∈ T, ∑ y ∈ B p, if y ∈ B a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [← card_filter]
      congr 1
    _ = ∑ y ∈ B p, ∑ a ∈ T, if y ∈ B a then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ y ∈ B p, d y := by
      apply Finset.sum_congr rfl
      intro y _hy
      simp only [d, card_filter]
    _ = ∑ y ∈ B p, if (T.filter fun a => y ∈ B a).Nonempty
        then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hu : (T.filter fun a => y ∈ B a).Nonempty
      · simp [hu, d, hpoint y hu]
      · have hz : d y = 0 := by
          exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hu)
        simp [hu, hz]
    _ = ∑ y ∈ (B p).filter (fun y =>
        (T.filter fun a => y ∈ B a).Nonempty), 2 := by
      rw [sum_filter]
    _ = 2 * ((B p).filter fun y =>
        (T.filter fun a => y ∈ B a).Nonempty).card := by
      simp [mul_comm]

/-- Every exterior row outside an equality circuit induces a matching on the
selected rows: its selected-row meeting degree is twice the number of used
circuit points lying on it. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_outsideMatching
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
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      ∀ u : W, u ∉ T →
        (T.filter fun w => (row u ∩ row w).Nonempty).card =
          2 * ((row u).filter fun y =>
            (T.filter fun w => y ∈ row w).Nonempty).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard u huT
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have huniform : ∀ w ∈ T, (row w).card = m := by
    intro w hw
    exact hdesign.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
  have hlinearT : ∀ w ∈ T, ∀ z ∈ T, w ≠ z →
      ((row w) ∩ (row z)).card ≤ 1 := by
    intro w hw z hz hwz
    exact hdesign.2.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
      z.1 (by simpa [F] using (mem_compl.mp z.2))
      (fun h => hwz (Subtype.ext h))
  have hevenV : ∀ y : V, Even ((T.filter fun w => y ∈ row w).card) := by
    intro y
    by_cases hy : y ∈ S
    · let yy : P := ⟨y, hy⟩
      simpa [row, hy] using heven yy
    · have hz : T.filter (fun w => y ∈ row w) = ∅ := by
        ext w
        simp [row, hy]
      rw [hz]
      exact ⟨0, rfl⟩
  have hpoint := (linear_evenConfiguration_eq_succ_rigidity
    row T m huniform hlinearT hevenV hTcard).2
  have hlinearU : ∀ w ∈ T, ((row u) ∩ (row w)).card ≤ 1 := by
    intro w hw
    have huw : u.1 ≠ w.1 := by
      intro h
      apply huT
      simpa [Subtype.ext h] using hw
    exact hdesign.2.1 u.1 (by simpa [F] using (mem_compl.mp u.2))
      w.1 (by simpa [F] using (mem_compl.mp w.2)) huw
  exact linear_degree_two_configuration_outside_meeting_eq
    row T u hpoint hlinearU

end

end Erdos85

#print axioms Erdos85.linear_degree_two_configuration_outside_meeting_eq
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_outsideMatching
