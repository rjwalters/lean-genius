import Proofs.Erdos85PureEndpointPrivatePairDefectBridge
import Proofs.Erdos85ExteriorDefectDecomposition

/-!
# A forced collision between private points at the pure endpoint

A private point has total defect degree `q-1`, all inside the shore.  Once
preconnectedness forces one of those neighbors to be a pair point, it cannot
also be defect-adjacent to all `q-1` other private points.  The resulting
non-defect private pair has a common graph neighbor.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In a preconnected pure endpoint, two distinct replication-one shore
points share a graph neighbor. -/
theorem c4Free_binarySquare_pureEndpoint_exists_private_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∃ x ∈ S.filter (fun x =>
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 1),
      ∃ x' ∈ S.filter (fun x' =>
          (G.neighborFinset x' ∩ fullLineCenters G S q).card = 1),
        x ≠ x' ∧ ∃ w, G.Adj x w ∧ G.Adj x' w := by
  classical
  let D := secondOrderDefectGraph G
  let R₁ := S.filter fun x =>
    (G.neighborFinset x ∩ fullLineCenters G S q).card = 1
  let R₂ := S.filter fun x =>
    (G.neighborFinset x ∩ fullLineCenters G S q).card = 2
  obtain ⟨x, hxR₁, y, hyR₂, hxyD⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_private_pair_defectBridge
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hR₁card : R₁.card = q := by
    simpa [R₁] using
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.1
  have hyNotR₁ : y ∉ R₁ := by
    intro hyR₁
    have hyOne := (Finset.mem_filter.mp hyR₁).2
    have hyTwo := (Finset.mem_filter.mp hyR₂).2
    omega
  have hDcard : (D.neighborFinset x).card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree (by omega) hreg hcard]
  have hmissing : ∃ x' ∈ R₁, x' ≠ x ∧ ¬ D.Adj x x' := by
    by_contra hnone
    push Not at hnone
    have hsub : insert y (R₁.erase x) ⊆ D.neighborFinset x := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hzy | hzErase
      · exact (D.mem_neighborFinset x z).mpr (by simpa [hzy] using hxyD)
      · have hzData := Finset.mem_erase.mp hzErase
        exact (D.mem_neighborFinset x z).mpr
          (hnone z hzData.2 hzData.1)
    have hyNotErase : y ∉ R₁.erase x := fun hy =>
      hyNotR₁ (Finset.mem_erase.mp hy).2
    have hlarge : q ≤ (D.neighborFinset x).card := by
      calc
        q = (insert y (R₁.erase x)).card := by
          rw [Finset.card_insert_of_notMem hyNotErase,
            Finset.card_erase_of_mem hxR₁, hR₁card]
          omega
        _ ≤ (D.neighborFinset x).card := Finset.card_le_card hsub
    omega
  obtain ⟨x', hx'R₁, hxx', hnotD⟩ := hmissing
  have hxx'Forward : x ≠ x' := hxx'.symm
  have hcommonNe :
      (G.neighborFinset x ∩ G.neighborFinset x').card ≠ 0 := by
    intro hzero
    exact hnotD
      ((secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hxx'Forward).mpr hzero)
  have hcommonPos :
      0 < (G.neighborFinset x ∩ G.neighborFinset x').card :=
    Nat.pos_of_ne_zero hcommonNe
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hcommonPos
  have hxw : G.Adj x w :=
    (G.mem_neighborFinset x w).mp (Finset.mem_inter.mp hw).1
  have hx'w : G.Adj x' w :=
    (G.mem_neighborFinset x' w).mp (Finset.mem_inter.mp hw).2
  exact ⟨x, by simpa [R₁] using hxR₁,
    x', by simpa [R₁] using hx'R₁, hxx'Forward, w, hxw, hx'w⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_private_commonNeighbor
