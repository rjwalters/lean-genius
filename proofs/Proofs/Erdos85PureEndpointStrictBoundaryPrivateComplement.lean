import Proofs.Erdos85PureEndpointStrictPrivateCutGap

/-!
# The private-shore complement at the strict boundary

At equality, the heavy rows are exactly the blocks witnessing missing defect
edges inside the private shore.  Thus the induced defect graph on private
points is a complete graph with the heavy-row intersection graph deleted.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
theorem c4Free_binarySquare_pureEndpoint_privateCut_boundary_privateComplement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V) (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v, (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun p =>
        (G.neighborFinset p ∩ fullLineCenters G S q).card = 1) = 2 * q - 4) :
    let F := fullLineCenters G S q
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let B := Fᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let H := B.filter fun b => 1 < r b
    ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
      (¬ (secondOrderDefectGraph G).Adj p p' ↔
        ∃! b, b ∈ H ∧ G.Adj p b ∧ G.Adj p' b) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
  let B := Fᶜ
  let r := fun b => (G.neighborFinset b ∩ P).card
  let H := B.filter fun b => 1 < r b
  have hs :=
    (c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_rowProfile_and_saturation
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri).2 hcut
  have hfull : ∀ f ∈ F, (G.neighborFinset f ∩ P).card = 1 := by
    intro f hf
    simpa [F, P] using
      c4Free_binarySquare_pureEndpoint_fullCenter_privateOccupancy_one
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri f hf
  intro p hp p' hp' hpp'
  constructor
  · intro hnotD
    have hcommonNonzero :
        (G.neighborFinset p ∩ G.neighborFinset p').card ≠ 0 := by
      intro hzero
      exact hnotD
        ((secondOrderDefectGraph_adj_iff_card_common_eq_zero
          G hfree hpp').mpr hzero)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcommonNonzero)
    have hpb : G.Adj p b :=
      (G.mem_neighborFinset p b).mp (Finset.mem_inter.mp hb).1
    have hp'b : G.Adj p' b :=
      (G.mem_neighborFinset p' b).mp (Finset.mem_inter.mp hb).2
    have hbNotF : b ∉ F := by
      intro hbF
      have hpair : ({p, p'} : Finset V) ⊆ G.neighborFinset b ∩ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · subst x
          exact Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset b p).mpr hpb.symm, hp⟩
        · subst x
          exact Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset b p').mpr hp'b.symm, hp'⟩
      have htwo : 2 ≤ (G.neighborFinset b ∩ P).card := by
        calc
          2 = ({p, p'} : Finset V).card := (Finset.card_pair hpp').symm
          _ ≤ _ := Finset.card_le_card hpair
      rw [hfull b hbF] at htwo
      omega
    have hbB : b ∈ B := by simpa [B] using hbNotF
    have hrTwoLower : 2 ≤ r b := by
      have hpair : ({p, p'} : Finset V) ⊆ G.neighborFinset b ∩ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · subst x
          exact Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset b p).mpr hpb.symm, hp⟩
        · subst x
          exact Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset b p').mpr hp'b.symm, hp'⟩
      change 2 ≤ (G.neighborFinset b ∩ P).card
      calc
        2 = ({p, p'} : Finset V).card := (Finset.card_pair hpp').symm
        _ ≤ _ := Finset.card_le_card hpair
    have hbH : b ∈ H := Finset.mem_filter.mpr ⟨hbB, by omega⟩
    refine ⟨b, ⟨hbH, hpb, hp'b⟩, ?_⟩
    intro c hc
    rcases hc with ⟨_hcH, hpc, hp'c⟩
    by_contra hbc
    exact hfree (containsC4_of_two_common hpp' hbc
      hpc.symm hp'c.symm hpb.symm hp'b.symm)
  · rintro ⟨b, ⟨_hbH, hpb, hp'b⟩, _huniq⟩ hD
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hpp').mp hD
    have hbmem : b ∈ G.neighborFinset p ∩ G.neighborFinset p' :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset p b).mpr hpb,
          (G.mem_neighborFinset p' b).mpr hp'b⟩
    rw [Finset.card_eq_zero.mp hzero] at hbmem
    simp at hbmem

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_privateCut_boundary_privateComplement
