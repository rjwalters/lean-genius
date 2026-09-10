import Proofs.Erdos85ThreeHighWitnessedColumnDomains

namespace Erdos85
open scoped BigOperators

/-- Count selected U-row incidences by rows or by columns. -/
theorem threeHighCross_subset_double_count (cross : ThreeHighCross) (S : Finset (Fin 15)) :
    (∑ i ∈ S, encodedRowDegree (cross i)) =
      ∑ j : Fin 8, (S.filter fun i => cross i j).card := by
  simp only [encodedRowDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- A finite certificate that the allowed columns cannot supply the selected rows. -/
def threeHighColumnSubsetCapacityCheck (U : Fin 15 → Fin 15 → Bool)
    (domains : Fin 8 → List (Finset (Fin 15)))
    (S : Finset (Fin 15)) (caps : Fin 8 → Nat) : Bool :=
  decide ((∑ j : Fin 8, caps j) < ∑ i ∈ S, (4 - encodedRowDegree (U i))) &&
    (List.finRange 8).all (fun j =>
      (domains j).all (fun T => decide ((S ∩ T).card ≤ caps j)))

attribute [local irreducible] threeHighCrossDomain

theorem threeHighColumnSubsetCapacityCheck_impossible
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (domains : Fin 8 → List (Finset (Fin 15)))
    (S : Finset (Fin 15)) (caps : Fin 8 → Nat)
    (hcheck : threeHighColumnSubsetCapacityCheck U domains S caps = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hd : ∀ j, threeHighCrossColumns cross j ∈ domains j) : False := by
  have hboth := hcheck
  simp only [threeHighColumnSubsetCapacityCheck, Bool.and_eq_true] at hboth
  have hlt := of_decide_eq_true hboth.1
  have hb : ∀ j : Fin 8, (S.filter fun i => cross i j).card ≤ caps j := by
    intro j
    have hj := List.all_eq_true.mp hboth.2 j (by simp)
    have h := of_decide_eq_true (List.all_eq_true.mp hj _ (hd j))
    have hset : S.filter (fun i => cross i j) = S ∩ threeHighCrossColumns cross j := by
      ext i
      simp [threeHighCrossColumns]
    rw [hset]
    exact h
  have hm : ∀ i, encodedRowDegree (cross i) = 4 - encodedRowDegree (U i) := by
    intro i
    have h := (threeHighCrossDomain_margins U R cross hc).1 i
    omega
  have hle := Finset.sum_le_sum (fun (j : Fin 8) (_ : j ∈ Finset.univ) => hb j)
  rw [← threeHighCross_subset_double_count cross S] at hle
  simp_rw [hm] at hle
  exact (Nat.not_lt_of_ge hle) hlt

/-- Domain reasons and a subset-capacity certificate exclude an actual cross. -/
theorem threeHighWitnessedColumnSubsetCapacity_impossible
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (domains : Fin 8 → List (Finset (Fin 15)))
    (reasons : Fin 8 → List ThreeHighColumnDomainReason)
    (S : Finset (Fin 15)) (caps : Fin 8 → Nat)
    (hdomains : threeHighWitnessedColumnDomainsCheck U R domains reasons = true)
    (hcheck : threeHighColumnSubsetCapacityCheck U domains S caps = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    False := by
  exact threeHighColumnSubsetCapacityCheck_impossible U R domains S caps hcheck cross hc
    (threeHighWitnessedColumnDomainsCheck_complete U R domains reasons hdomains cross hc he)

end Erdos85
#print axioms Erdos85.threeHighCross_subset_double_count
#print axioms Erdos85.threeHighColumnSubsetCapacityCheck_impossible
#print axioms Erdos85.threeHighWitnessedColumnSubsetCapacity_impossible
