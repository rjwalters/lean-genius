import Proofs.Erdos85ExceptionalEmptyPoleLeakage

/-!
# Aggregate exceptional empty-pole leakage

Below saturation, every empty pole leaks exactly `q-c` defect incidences.
Incidence reciprocity rewrites their sum as the total load seen from outside
the exceptional support.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact aggregate outside load of all exceptional empty poles. -/
theorem binarySquare_emptyPoles_outsideExceptional_defectIncidence_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    ∑ x ∈ (fullLineCenters G S q ∪ emptyLineCenters G S)ᶜ,
        ((secondOrderDefectGraph G).neighborFinset x ∩
          emptyLineCenters G S).card =
      (emptyLineCenters G S).card *
        (q - (fullLineCenters G S q ∪ emptyLineCenters G S).card) := by
  let C := fullLineCenters G S q ∪ emptyLineCenters G S
  let E := emptyLineCenters G S
  let D := secondOrderDefectGraph G
  have hswap := sum_card_neighbor_inter_comm D E Cᶜ
  have hleft :
      (∑ p ∈ E, (D.neighborFinset p ∩ Cᶜ).card) =
        E.card * (q - C.card) := by
    calc
      (∑ p ∈ E, (D.neighborFinset p ∩ Cᶜ).card) =
          ∑ _p ∈ E, (q - C.card) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hleak :=
          binarySquare_emptyPole_outsideExceptional_defectNeighbors_card
            G hfree hq hreg hcard S hemptyClique p hp
        change (D.neighborFinset p \ C).card = q - C.card at hleak
        rw [show D.neighborFinset p ∩ Cᶜ = D.neighborFinset p \ C by
          ext x
          simp] 
        exact hleak
      _ = E.card * (q - C.card) := by simp
  change (∑ x ∈ Cᶜ, (D.neighborFinset x ∩ E).card) =
    E.card * (q - C.card)
  rw [← hleft]
  exact hswap.symm

end

end Erdos85

#print axioms
  Erdos85.binarySquare_emptyPoles_outsideExceptional_defectIncidence_sum
