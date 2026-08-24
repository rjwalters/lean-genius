import Proofs.Erdos85ExceptionalEmptyCliqueIncidenceCapacity

/-!
# Intrinsic final-dyadic form of exceptional empty incidence capacity

The structural incidence provider is proved in
`Erdos85ExceptionalEmptyCliqueIncidenceCapacity`.  Here the final dyadic mass
identity eliminates the shore size, expressing its consequence purely in
the two exceptional population counts.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

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
  have hinc :=
    binarySquare_emptyLineCenters_mul_degree_le_complement_card_of_clique
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

#print axioms
  Erdos85.binarySquare_finalDyadic_exceptionalPopulation_capacity_of_emptyClique
