import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddTwoRigidity

/-!
# The canonical mate involution in an `m+2` circuit

If every member of a finite family has a unique distinct disjoint member,
those unique mates pair the family by a fixed-point-free involution.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Unique disjoint partners in a finite family canonically form a
fixed-point-free involution. -/
theorem exists_disjointMate_involution_of_unique
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α)
    (hunique : ∀ a ∈ T,
      ((T.erase a).filter fun b => ¬(B a ∩ B b).Nonempty).card = 1) :
    ∃ mate : {a // a ∈ T} → {a // a ∈ T},
      (∀ a, mate a ≠ a) ∧
      Function.Involutive mate ∧
      (∀ a, ¬(B a.1 ∩ B (mate a).1).Nonempty) := by
  classical
  let N (a : {a // a ∈ T}) :=
    (T.erase a.1).filter fun b => ¬(B a.1 ∩ B b).Nonempty
  have hNcard : ∀ a, (N a).card = 1 := by
    intro a
    simpa [N] using hunique a.1 a.2
  have hNnonempty : ∀ a, (N a).Nonempty := by
    intro a
    exact Finset.card_pos.mp (by rw [hNcard a]; omega)
  let mate : {a // a ∈ T} → {a // a ∈ T} := fun a =>
    ⟨(hNnonempty a).choose,
      Finset.mem_of_mem_erase
        (Finset.mem_filter.mp (hNnonempty a).choose_spec).1⟩
  have hmateN : ∀ a, (mate a).1 ∈ N a := by
    intro a
    exact (hNnonempty a).choose_spec
  have hmateNe : ∀ a, mate a ≠ a := by
    intro a hEq
    have hne := Finset.ne_of_mem_erase (Finset.mem_filter.mp (hmateN a)).1
    exact hne (congrArg Subtype.val hEq)
  have hmateDisjoint : ∀ a, ¬(B a.1 ∩ B (mate a).1).Nonempty := by
    intro a
    exact (Finset.mem_filter.mp (hmateN a)).2
  have hmateInv : Function.Involutive mate := by
    intro a
    apply Subtype.ext
    apply Finset.card_le_one.mp (by rw [hNcard (mate a)])
    · exact hmateN (mate a)
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_erase.mpr ⟨?_, a.2⟩, ?_⟩
      · exact fun h => hmateNe a (Subtype.ext h.symm)
      · simpa [Finset.inter_comm] using hmateDisjoint a
  exact ⟨mate, hmateNe, hmateInv, hmateDisjoint⟩

set_option maxHeartbeats 800000 in
/-- The unique nonmeeting rows of an endpoint `m+2` even configuration form
a canonical fixed-point-free involution. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_mateInvolution
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
      ∃ mate : {w // w ∈ T} → {w // w ∈ T},
        (∀ w, mate w ≠ w) ∧
        Function.Involutive mate ∧
        (∀ w, ¬(row w.1 ∩ row (mate w).1).Nonempty) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard
  have hunique : ∀ w ∈ T,
      ((T.erase w).filter fun u => ¬(row w ∩ row u).Nonempty).card = 1 := by
    intro w hw
    exact (c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_rigidity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard w hw).2
  exact exists_disjointMate_involution_of_unique row T hunique

end

end Erdos85

#print axioms Erdos85.exists_disjointMate_involution_of_unique
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_mateInvolution
