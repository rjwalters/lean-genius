import Proofs.Erdos85DegreeTwoConnectedEndpointCount

/-!
# Counting path components from their endpoints

Once every connected degree-one/two component has either zero endpoints
(the cycle case) or exactly two endpoints, summing over components shows
that the number of path components is half the global endpoint mass.  This
is the numerical aggregation asserted in B22.
-/

open Finset

namespace Erdos85

/-- Arithmetic aggregation for a finite family of zero-or-two endpoint
counts. -/
theorem zero_or_two_component_count_eq_total_div_two
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (endpointCount : ι → ℕ) (total : ℕ)
    (hcases : ∀ i ∈ I, endpointCount i = 0 ∨ endpointCount i = 2)
    (htotal : total = ∑ i ∈ I, endpointCount i) :
    total = 2 * (I.filter fun i ↦ endpointCount i = 2).card ∧
      total / 2 = (I.filter fun i ↦ endpointCount i = 2).card := by
  have hsum : (∑ i ∈ I, endpointCount i) =
      2 * (I.filter fun i ↦ endpointCount i = 2).card := by
    calc
      (∑ i ∈ I, endpointCount i) =
          ∑ i ∈ I, if endpointCount i = 2 then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases hcases i hi with h | h <;> simp [h]
      _ = ∑ _i ∈ I.filter (fun i ↦ endpointCount i = 2), 2 := by
        rw [Finset.sum_filter]
      _ = 2 * (I.filter fun i ↦ endpointCount i = 2).card := by
        simp [mul_comm]
  constructor
  · rw [htotal, hsum]
  · rw [htotal, hsum]
    simp

/-- Finset-facing B22 path-count formula.  `endpointSet i` is the set of
global endpoints lying in component `i`; `hpartitionCard` records that
these component endpoint sets partition `endpoints`. -/
theorem pathComponent_card_eq_endpoint_card_div_two
    {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (I : Finset ι) (endpoints : Finset V) (endpointSet : ι → Finset V)
    (hcases : ∀ i ∈ I,
      (endpointSet i).card = 0 ∨ (endpointSet i).card = 2)
    (hpartitionCard : endpoints.card = ∑ i ∈ I, (endpointSet i).card) :
    (I.filter fun i ↦ (endpointSet i).Nonempty).card = endpoints.card / 2 := by
  have hcount := zero_or_two_component_count_eq_total_div_two
    I (fun i ↦ (endpointSet i).card) endpoints.card hcases hpartitionCard
  have hfilter : (I.filter fun i ↦ (endpointSet i).Nonempty) =
      I.filter fun i ↦ (endpointSet i).card = 2 := by
    ext i
    by_cases hi : i ∈ I
    · rcases hcases i hi with h | h
      · have hempty : endpointSet i = ∅ := Finset.card_eq_zero.mp h
        simp [hi, hempty]
      · have hne : (endpointSet i).Nonempty :=
          Finset.card_pos.mp (by omega)
        simp [hi, h, hne]
    · simp [hi]
  rw [hfilter, ← hcount.2]

#print axioms zero_or_two_component_count_eq_total_div_two
#print axioms pathComponent_card_eq_endpoint_card_div_two

end Erdos85
