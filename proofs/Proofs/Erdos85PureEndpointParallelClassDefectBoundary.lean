import Proofs.Erdos85PureEndpointExteriorParallelClass
import Proofs.Erdos85PureEndpointDefectCutProfile

/-!
# Defect boundary of the forced parallel class

All points in the parallel row share its center `w`, so the row is independent
in the second-order defect graph.  The exact pair-point shore degree therefore
leaves the row entirely, giving a sharp boundary census.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- The forced parallel class is D-independent and has oriented internal-shore
boundary mass `m(m-1)`. -/
theorem c4Free_binarySquare_pureEndpoint_exists_parallelClass_defectBoundary
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
    let F := fullLineCenters G S q
    ∃ w ∉ F,
      let B := G.neighborFinset w ∩ S
      B.card = m ∧
      (∀ y ∈ B,
        ((secondOrderDefectGraph G).neighborFinset y ∩ B).card = 0 ∧
        ((secondOrderDefectGraph G).neighborFinset y ∩ (S \ B)).card = m - 1) ∧
      (∑ y ∈ B,
        ((secondOrderDefectGraph G).neighborFinset y ∩ (S \ B)).card) =
          m * (m - 1) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let D := secondOrderDefectGraph G
  obtain ⟨w, hwNotF, hBcard, _hKzero, _hpair, _hcover, hownerTwo⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_exterior_parallelClass
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let B := G.neighborFinset w ∩ S
  have hDprofile := c4Free_binarySquare_pureEndpoint_defect_biregular_decomposition
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hlocal : ∀ y ∈ B,
      (D.neighborFinset y ∩ B).card = 0 ∧
      (D.neighborFinset y ∩ (S \ B)).card = m - 1 := by
    intro y hyB
    have hzero : (D.neighborFinset y ∩ B).card = 0 := by
      apply card_eq_zero.mpr
      apply not_nonempty_iff_eq_empty.mp
      rintro ⟨z, hz⟩
      have hzData := mem_inter.mp hz
      have hyzD := (D.mem_neighborFinset y z).mp hzData.1
      have hyzNe := D.ne_of_adj hyzD
      have hcommonZero :=
        (secondOrderDefectGraph_adj_iff_card_common_eq_zero
          G hfree hyzNe).mp hyzD
      have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset z := by
        apply mem_inter.mpr
        exact ⟨
          (G.mem_neighborFinset y w).mpr
            ((G.mem_neighborFinset w y).mp (mem_inter.mp hyB).1).symm,
          (G.mem_neighborFinset z w).mpr
            ((G.mem_neighborFinset w z).mp (mem_inter.mp hzData.2).1).symm⟩
      rw [card_eq_zero.mp hcommonZero] at hwCommon
      simp at hwCommon
    have htotal : (D.neighborFinset y ∩ S).card = m - 1 := by
      apply (hDprofile y).2.1
      exact hownerTwo y (by simpa [B] using hyB)
    have houtEq : D.neighborFinset y ∩ (S \ B) =
        (D.neighborFinset y ∩ S) \ B := by
      ext z
      simp [and_assoc, and_left_comm]
    have hout : (D.neighborFinset y ∩ (S \ B)).card = m - 1 := by
      rw [houtEq, card_sdiff]
      have hinter : (B ∩ (D.neighborFinset y ∩ S)).card = 0 := by
        have heq : B ∩ (D.neighborFinset y ∩ S) =
            D.neighborFinset y ∩ B := by
          ext z
          have hBsubS : B ⊆ S := inter_subset_right
          simp only [mem_inter]
          constructor
          · rintro ⟨hzB, hzD, _hzS⟩
            exact ⟨hzD, hzB⟩
          · rintro ⟨hzD, hzB⟩
            exact ⟨hzB, hzD, hBsubS hzB⟩
        rw [heq, hzero]
      rw [hinter, Nat.sub_zero, htotal]
    exact ⟨hzero, hout⟩
  refine ⟨w, hwNotF, hBcard, hlocal, ?_⟩
  calc
    (∑ y ∈ B, (D.neighborFinset y ∩ (S \ B)).card) =
        ∑ _y ∈ B, (m - 1) := by
      apply sum_congr rfl
      intro y hy
      exact (hlocal y hy).2
    _ = m * (m - 1) := by
      simp_rw [sum_const_nat]
      rw [hBcard]

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_parallelClass_defectBoundary
