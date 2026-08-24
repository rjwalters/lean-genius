import Proofs.Erdos85PureEndpointCanonicalPrivateMatching
import Proofs.Erdos85PureLargeExceptionalGraphTerminal

/-!
# Private matching at the pure final-layer endpoint

This file discharges the two remaining structural inputs of the canonical
four-class matching theorem from the actual final dyadic layer.  Thus a pure
exceptional family of size exactly `q` has the full partial-Baer private-point
structure without any replication hypothesis in its public API.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **Pure endpoint private matching.**  In a binary-square C4-free regular
graph, if the final layer is pure full and has exactly `q` exceptional
centers, those centers admit an injective matching to private neighbors.
The matched vertex of each center has it as its unique exceptional neighbor. -/
theorem c4Free_binarySquare_pureEndpoint_fullLineCenters_structure
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
    (∀ i ∈ fullLineCenters G S q,
      ∀ j ∈ fullLineCenters G S q, i ≠ j →
        ¬(secondOrderDefectGraph G).Adj i j) ∧
    ∃ p : {i // i ∈ fullLineCenters G S q} → V,
      Function.Injective p ∧
      ∀ i, G.Adj i.1 (p i) ∧
        G.neighborFinset (p i) ∩ fullLineCenters G S q = {i.1} := by
  let C := fullLineCenters G S q
  have hm : 2 ≤ m := by omega
  have hregm : ∀ v, G.degree v = 2 * m := by simpa [hqm] using hreg
  have hcardm : Fintype.card V = 4 * m * m := by
    rw [hcard, hqm]
    ring
  have hshore' : 2 * S.card = (2 * m) * (2 * m) + 2 * m := by
    simpa [hqm] using hshore
  have hlower : 2 * m * m - 2 * m + 1 ≤ S.card := by
    have hprod : (2 * m) * (2 * m) = 4 * (m * m) := by ring
    rw [hprod] at hshore'
    rw [show 2 * m * m = 2 * (m * m) by ring]
    omega
  have hupper : S.card ≤ 2 * m * m + 2 * m - 1 := by
    have hprod : (2 * m) * (2 * m) = 4 * (m * m) := by ring
    rw [hprod] at hshore'
    rw [show 2 * m * m = 2 * (m * m) by ring]
    omega
  have htri' : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = 2 * m := by
    intro v
    simpa [hqm] using htri v
  have hrepUpper : ∀ p ∈ S, (G.neighborFinset p ∩ C).card ≤ 3 := by
    intro p hp
    have hbound := binarySquare_finalLayer_exceptionalNeighbors_card_le_three
      G hfree hm hregm hcardm S hlower hupper htri' p
    have hfilter :
        (G.neighborFinset p).filter (fun w =>
          (G.neighborFinset w ∩ S).card = 0 ∨
          (G.neighborFinset w ∩ S).card = 2 * m) =
        G.neighborFinset p ∩ C := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_inter,
        mem_fullLineCenters, C]
      constructor
      · rintro ⟨hwp, hzero | hfull⟩
        · have hwEmpty : w ∈ emptyLineCenters G S :=
            (mem_emptyLineCenters G S w).mpr hzero
          rw [hempty] at hwEmpty
          simp at hwEmpty
        · exact ⟨hwp, by simpa [hqm] using hfull⟩
      · rintro ⟨hwp, hfull⟩
        exact ⟨hwp, Or.inr (by simpa [hqm] using hfull)⟩
    rw [hfilter] at hbound
    exact hbound
  have hout : ∀ p ∉ S, (G.neighborFinset p ∩ C).card = 0 := by
    intro p hp
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨w, hw⟩
    have hwp := (Finset.mem_inter.mp hw).1
    have hwFull := (mem_fullLineCenters G S q w).mp
      (Finset.mem_inter.mp hw).2
    have hpNw : p ∈ G.neighborFinset w := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hwp
    have heq : G.neighborFinset w ∩ S = G.neighborFinset w := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hwFull, G.card_neighborFinset_eq_degree, hreg]
    have hpInter : p ∈ G.neighborFinset w ∩ S := by
      rw [heq]
      exact hpNw
    exact hp (Finset.mem_inter.mp hpInter).2
  have hline : ∀ i ∈ C, G.degree i = q := by
    intro i _
    exact hreg i
  exact pureEndpoint_fourClass_defectIndependent_and_privateMatching
    G hfree C S (by simpa [C] using hCcard) hline hshore hout hrepUpper

/-- Matching-only projection of the pure final-layer structure theorem. -/
theorem c4Free_binarySquare_pureEndpoint_fullLineCenters_privateMatching
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
    ∃ p : {i // i ∈ fullLineCenters G S q} → V,
      Function.Injective p ∧
      ∀ i, G.Adj i.1 (p i) ∧
        G.neighborFinset (p i) ∩ fullLineCenters G S q = {i.1} :=
  (c4Free_binarySquare_pureEndpoint_fullLineCenters_structure
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_fullLineCenters_privateMatching
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_fullLineCenters_structure
