import Proofs.Erdos85OddIncidencePropagation
import Proofs.Erdos85OneHighPairingRefinement

/-! # Endpoint parity and off-diagonal pairing incidence -/

namespace Erdos85

open scoped BigOperators

private theorem oneHighLabelPairEndpointCount_eq_diagonal_add_incident
    (pair : OneHighLabelPair) (label : Fin 8) (hpair : pair.1 ≤ pair.2) :
    oneHighLabelPairEndpointCount pair label =
      2 * (if pair = (label, label) then 1 else 0) +
        ∑ other ∈ (Finset.univ.erase label),
          if pair = (min label other, max label other) then 1 else 0 := by
  rcases pair with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> fin_cases label <;>
    simp at hpair <;> decide

/-- Exact decomposition of an endpoint count into twice the diagonal-pair
count and the counts of all off-diagonal canonical keys incident to a label. -/
theorem oneHighPairingEndpointCount_eq_two_mul_diagonal_add_incident
    (pairs : List OneHighLabelPair)
    (hcanonical : ∀ pair ∈ pairs, pair.1 ≤ pair.2)
    (label : Fin 8) :
    oneHighPairingEndpointCount pairs label =
      2 * pairs.count (label, label) +
        ∑ other ∈ (Finset.univ.erase label),
          pairs.count (min label other, max label other) := by
  induction pairs with
  | nil => simp [oneHighPairingEndpointCount]
  | cons pair pairs ih =>
      have hpair : pair.1 ≤ pair.2 := hcanonical pair (by simp)
      have htail : ∀ p ∈ pairs, p.1 ≤ p.2 := by
        intro p hp
        exact hcanonical p (by simp [hp])
      change oneHighLabelPairEndpointCount pair label +
          oneHighPairingEndpointCount pairs label = _
      rw [ih htail]
      simp only [List.count_cons]
      simp only [beq_iff_eq]
      rw [oneHighLabelPairEndpointCount_eq_diagonal_add_incident pair label hpair]
      rw [Finset.sum_add_distrib]
      omega

/-- Diagonal pairs contribute two endpoints, so removing them does not change
the parity of the total incidence at a label. -/
theorem even_incident_pairingMultiplicity_iff_even_endpointCount
    (pairs : List OneHighLabelPair)
    (hcanonical : ∀ pair ∈ pairs, pair.1 ≤ pair.2)
    (label : Fin 8) :
    Even (∑ other ∈ (Finset.univ.erase label),
      pairs.count (min label other, max label other)) ↔
      Even (oneHighPairingEndpointCount pairs label) := by
  rw [oneHighPairingEndpointCount_eq_two_mul_diagonal_add_incident
    pairs hcanonical label, Nat.even_add]
  simp

end Erdos85
