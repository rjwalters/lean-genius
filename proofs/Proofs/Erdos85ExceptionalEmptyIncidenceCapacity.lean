import Proofs.Erdos85ExceptionalSupportDefectCapacity
import Proofs.Erdos85FinalDyadicExceptionalProfile

/-!
# Incidence capacity forced by an exceptional empty clique

A defect clique has pairwise disjoint ambient neighborhoods.  Consequently
no point can lie on two canonical empty lines, and the empty-line incidences
fit injectively into the shore complement.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Defect-clique structure of the canonical empty family automatically
implies the point-replication-at-most-one condition. -/
theorem emptyLineCenters_replicationAtMostOne_of_defectClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    ∀ x, (G.neighborFinset x ∩ emptyLineCenters G S).card ≤ 1 := by
  intro x
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hu' := Finset.mem_inter.mp hu
  have hv' := Finset.mem_inter.mp hv
  by_contra huv
  exact (not_secondOrderDefect_adj_of_commonNeighbor
    G hfree huv
      ((G.mem_neighborFinset x u).mp hu'.1).symm
      ((G.mem_neighborFinset x v).mp hv'.1).symm)
    (hemptyClique hu'.2 hv'.2 huv)

/-- The `q` incidences of every empty line are disjoint and all land outside
the shore. -/
theorem binarySquare_emptyLineCenters_incidence_capacity_of_defectClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    q * (emptyLineCenters G S).card ≤ q * q - S.card := by
  have hcap := emptyLineCenters_replicationAtMostOne_of_defectClique
    G hfree S hemptyClique
  have hinc := regular_emptyLines_mul_card_le_complement_card
    G hreg S (emptyLineCenters G S)
      (fun e he => (mem_emptyLineCenters G S e).mp he)
      (fun v _ => hcap v)
  rwa [hcard] at hinc

/-- Intrinsic final-scale population form of the empty-incidence capacity:
`(2q-1)e+f ≤ q²`. -/
theorem binarySquare_finalDyadic_exceptionalPopulation_capacity_of_emptyClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (2 * (q : ℤ) - 1) * ((emptyLineCenters G S).card : ℤ) +
        ((fullLineCenters G S q).card : ℤ) ≤
      (q : ℤ) * q := by
  have hinc := binarySquare_emptyLineCenters_incidence_capacity_of_defectClique
    G hfree hreg hcard S hemptyClique
  have hsle : S.card ≤ q * q := by
    rw [← hcard]
    exact Finset.card_le_univ S
  have hincCast : ((q * (emptyLineCenters G S).card : ℕ) : ℤ) ≤
      ((q * q - S.card : ℕ) : ℤ) := by
    exact_mod_cast hinc
  have hincZ : (q : ℤ) * ((emptyLineCenters G S).card : ℤ) ≤
      (q : ℤ) * q - (S.card : ℤ) := by
    rw [Int.ofNat_sub hsle] at hincCast
    push_cast at hincCast
    exact hincCast
  have hmass := finalDyadic_full_sub_empty_eq_cutDisplacement
    G hqa hreg S hdiv
  rw [hcard] at hmass
  push_cast at hmass
  nlinarith

end

end Erdos85

#print axioms Erdos85.emptyLineCenters_replicationAtMostOne_of_defectClique
#print axioms
  Erdos85.binarySquare_emptyLineCenters_incidence_capacity_of_defectClique
#print axioms
  Erdos85.binarySquare_finalDyadic_exceptionalPopulation_capacity_of_emptyClique
