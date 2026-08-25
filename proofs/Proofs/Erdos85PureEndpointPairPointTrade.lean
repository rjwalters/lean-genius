import Proofs.Erdos85PureEndpointZeroPrivateRows

/-!
# The pair-point private-occupancy trade

At a pure endpoint, the average number of private points on the exterior
rows through a replication-two shore point is at most one.  The deficit is
exactly its second-order-defect degree into the private class.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

private theorem pairPoint_commonNeighbor_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra huv
  exact hfree (containsC4_of_two_common hxy huv
    ((G.mem_neighborFinset x u).mp (Finset.mem_inter.mp hu).1).symm
    ((G.mem_neighborFinset y u).mp (Finset.mem_inter.mp hu).2).symm
    ((G.mem_neighborFinset x v).mp (Finset.mem_inter.mp hv).1).symm
    ((G.mem_neighborFinset y v).mp (Finset.mem_inter.mp hv).2).symm)

/-- Exact local private-occupancy identity at every replication-two shore
point of a pure endpoint. -/
theorem c4Free_binarySquare_pureEndpoint_pairPoint_privateOccupancy_add_defect
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
    let B := Fᶜ
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
    ∀ x ∈ X,
      (∑ b ∈ G.neighborFinset x ∩ B,
          (G.neighborFinset b ∩ P).card) +
        ((secondOrderDefectGraph G).neighborFinset x ∩ P).card =
          (G.neighborFinset x ∩ B).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let B := Fᶜ
  let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
  let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
  obtain ⟨sel, _hselInj, hsel, hselSurj⟩ :=
    c4Free_binarySquare_pureEndpoint_privatePoint_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hPcard : P.card = q := by
    simpa [P, F] using
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.1
  have hfullPrivate : ∀ f ∈ F, (G.neighborFinset f ∩ P).card = 1 := by
    intro f hf
    let fi : {i // i ∈ F} := ⟨f, hf⟩
    have hEq : G.neighborFinset f ∩ P = {sel fi} := by
      ext p
      constructor
      · intro hp
        have hpAdj : G.Adj f p :=
          (G.mem_neighborFinset f p).mp (Finset.mem_inter.mp hp).1
        have hpP := Finset.mem_filter.mp (Finset.mem_inter.mp hp).2
        obtain ⟨i, hi⟩ := hselSurj p hpP.1 (by simpa [F] using hpP.2)
        have hfOwner : f ∈ G.neighborFinset (sel i) ∩ F :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset (sel i) f).mpr
            (by simpa [hi] using hpAdj.symm), hf⟩
        rw [(hsel i).2.2] at hfOwner
        have hfi : i = fi := by
          apply Subtype.ext
          exact (Finset.mem_singleton.mp hfOwner).symm
        exact Finset.mem_singleton.mpr
          (hi.symm.trans (congrArg sel hfi))
      · intro hp
        have hpEq : p = sel fi := Finset.mem_singleton.mp hp
        subst p
        have hs := hsel fi
        have hmemP : sel fi ∈ P := by
          apply Finset.mem_filter.mpr
          simpa [P, F] using ⟨hs.1, by rw [hs.2.2]; simp⟩
        have hadj : sel fi ∈ G.neighborFinset f := by
          simpa [SimpleGraph.mem_neighborFinset] using hs.2.1
        exact Finset.mem_inter.mpr ⟨hadj, hmemP⟩
    rw [hEq]
    simp
  intro x hx
  change
    (∑ b ∈ G.neighborFinset x ∩ B, (G.neighborFinset b ∩ P).card) +
      ((secondOrderDefectGraph G).neighborFinset x ∩ P).card =
        (G.neighborFinset x ∩ B).card
  have hxData := Finset.mem_filter.mp hx
  have hxOwner : (G.neighborFinset x ∩ F).card = 2 := hxData.2
  have hxBcard : (G.neighborFinset x ∩ B).card = q - 2 := by
    have hsplit := neighbor_inter_complement_card G F x
    change (G.neighborFinset x ∩ Fᶜ).card = q - 2
    simpa only [Finset.compl_eq_univ_sdiff, hreg x, hxOwner] using hsplit
  have hxpNe : ∀ p ∈ P, p ≠ x := by
    intro p hp hpx
    subst p
    have := (Finset.mem_filter.mp hp).2
    omega
  have hcommon : ∀ p ∈ P,
      (G.neighborFinset p ∩ G.neighborFinset x).card +
        (if (secondOrderDefectGraph G).Adj p x then 1 else 0) = 1 := by
    intro p hp
    have hpne := hxpNe p hp
    by_cases hD : (secondOrderDefectGraph G).Adj p x
    · have hz := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hpne).mp hD
      simp [hD, hz]
    · have hnezero : (G.neighborFinset p ∩ G.neighborFinset x).card ≠ 0 := by
        intro hz
        exact hD ((secondOrderDefectGraph_adj_iff_card_common_eq_zero
          G hfree hpne).mpr hz)
      have hle := pairPoint_commonNeighbor_card_le_one G hfree hpne
      simp [hD]
      omega
  have hall :
      (∑ b ∈ G.neighborFinset x, (G.neighborFinset b ∩ P).card) +
        ((secondOrderDefectGraph G).neighborFinset x ∩ P).card = q := by
    have hdouble := sum_neighbor_inter_card_comm G (G.neighborFinset x) P
    have hDsum : ((secondOrderDefectGraph G).neighborFinset x ∩ P).card =
        ∑ p ∈ P, if (secondOrderDefectGraph G).Adj p x then 1 else 0 := by
      have heq : (secondOrderDefectGraph G).neighborFinset x ∩ P =
          P.filter fun p => (secondOrderDefectGraph G).Adj p x := by
        ext p
        simp [SimpleGraph.mem_neighborFinset,
          (secondOrderDefectGraph G).adj_comm, and_comm]
      rw [heq, Finset.card_filter]
    rw [hdouble, hDsum, ← Finset.sum_add_distrib]
    calc
      ∑ p ∈ P, ((G.neighborFinset p ∩ G.neighborFinset x).card +
          if (secondOrderDefectGraph G).Adj p x then 1 else 0) =
          ∑ _p ∈ P, 1 := Finset.sum_congr rfl hcommon
      _ = P.card := by simp
      _ = q := hPcard
  have hsplitSum :
      ∑ b ∈ G.neighborFinset x, (G.neighborFinset b ∩ P).card =
        (∑ b ∈ G.neighborFinset x ∩ F,
          (G.neighborFinset b ∩ P).card) +
        ∑ b ∈ G.neighborFinset x ∩ B,
          (G.neighborFinset b ∩ P).card := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext b
        by_cases hb : b ∈ F <;> simp [B, hb]
      · intro _ _
        rfl
    · exact Finset.disjoint_left.mpr fun b hbF hbB =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hbB).2)
          (Finset.mem_inter.mp hbF).2
  have hfullSum :
      (∑ b ∈ G.neighborFinset x ∩ F,
        (G.neighborFinset b ∩ P).card) = 2 := by
    calc
      _ = ∑ _b ∈ G.neighborFinset x ∩ F, 1 :=
        Finset.sum_congr rfl fun b hb => hfullPrivate b (Finset.mem_inter.mp hb).2
      _ = (G.neighborFinset x ∩ F).card := by simp
      _ = 2 := hxOwner
  have htotal :
      2 + (∑ b ∈ G.neighborFinset x ∩ B,
        (G.neighborFinset b ∩ P).card) +
          ((secondOrderDefectGraph G).neighborFinset x ∩ P).card = q := by
    calc
      _ = (∑ b ∈ G.neighborFinset x,
            (G.neighborFinset b ∩ P).card) +
          ((secondOrderDefectGraph G).neighborFinset x ∩ P).card := by
            rw [hsplitSum, hfullSum]
      _ = q := hall
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_pairPoint_privateOccupancy_add_defect
