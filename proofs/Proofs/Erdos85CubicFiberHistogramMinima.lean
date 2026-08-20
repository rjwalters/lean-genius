import Mathlib

/-! # Sharp bounded-histogram minima for cubic endpoint fibers -/

namespace Erdos85

open scoped BigOperators
open Finset

/-- Six values in `[0,6]` with sum 25 have square mass at least 105.  At
equality they are five fours and one five. -/
theorem six_cubicValues_sum_twentyFive_minimum
    (c : ℕ → ℕ)
    (hcard : ∑ t ∈ Finset.range 7, c t = 6)
    (hsum : ∑ t ∈ Finset.range 7, t * c t = 25) :
    105 ≤ ∑ t ∈ Finset.range 7, t ^ 2 * c t := by
  norm_num [Finset.sum_range_succ] at hcard hsum ⊢
  omega

theorem six_cubicValues_sum_twentyFive_eq_minimum
    (c : ℕ → ℕ)
    (hcard : ∑ t ∈ Finset.range 7, c t = 6)
    (hsum : ∑ t ∈ Finset.range 7, t * c t = 25)
    (hsq : ∑ t ∈ Finset.range 7, t ^ 2 * c t ≤ 105) :
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 ∧
      c 4 = 5 ∧ c 5 = 1 ∧ c 6 = 0 := by
  norm_num [Finset.sum_range_succ] at hcard hsum hsq ⊢
  omega

/-- Five values in `[0,6]` with sum 16 have square mass at least 52.  At
equality they are four threes and one four. -/
theorem five_cubicValues_sum_sixteen_minimum
    (c : ℕ → ℕ)
    (hcard : ∑ t ∈ Finset.range 7, c t = 5)
    (hsum : ∑ t ∈ Finset.range 7, t * c t = 16) :
    52 ≤ ∑ t ∈ Finset.range 7, t ^ 2 * c t := by
  norm_num [Finset.sum_range_succ] at hcard hsum ⊢
  omega

theorem five_cubicValues_sum_sixteen_eq_minimum
    (c : ℕ → ℕ)
    (hcard : ∑ t ∈ Finset.range 7, c t = 5)
    (hsum : ∑ t ∈ Finset.range 7, t * c t = 16)
    (hsq : ∑ t ∈ Finset.range 7, t ^ 2 * c t ≤ 52) :
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 4 ∧
      c 4 = 1 ∧ c 5 = 0 ∧ c 6 = 0 := by
  norm_num [Finset.sum_range_succ] at hcard hsum hsq ⊢
  omega

/-- Five values in `[0,6]` with sum 17 have square mass at least 59.  At
equality they are three threes and two fours. -/
theorem five_cubicValues_sum_seventeen_minimum
    (c : ℕ → ℕ)
    (hcard : ∑ t ∈ Finset.range 7, c t = 5)
    (hsum : ∑ t ∈ Finset.range 7, t * c t = 17) :
    59 ≤ ∑ t ∈ Finset.range 7, t ^ 2 * c t := by
  norm_num [Finset.sum_range_succ] at hcard hsum ⊢
  omega

theorem five_cubicValues_sum_seventeen_eq_minimum
    (c : ℕ → ℕ)
    (hcard : ∑ t ∈ Finset.range 7, c t = 5)
    (hsum : ∑ t ∈ Finset.range 7, t * c t = 17)
    (hsq : ∑ t ∈ Finset.range 7, t ^ 2 * c t ≤ 59) :
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 3 ∧
      c 4 = 2 ∧ c 5 = 0 ∧ c 6 = 0 := by
  norm_num [Finset.sum_range_succ] at hcard hsum hsq ⊢
  omega

/-- Four fibers of each exceptional type and eight ordinary fibers have
combined square mass at least 1100. -/
theorem h305_sixteen_cubicFiber_squareMass_ge_1100
    (S25 S16 S17 : ℕ)
    (h25 : 105 ≤ S25) (h16 : 52 ≤ S16) (h17 : 59 ≤ S17) :
    1100 ≤ 4 * S25 + 4 * S16 + 8 * S17 := by
  omega

/-- Six bounded values of total mass 24 have square mass at least 96, with
equality only when all six values equal four. -/
theorem six_cubicValues_sum_twentyFour_minimum
    (c : ℕ → ℕ)
    (hcard : ∑ t ∈ Finset.range 7, c t = 6)
    (hsum : ∑ t ∈ Finset.range 7, t * c t = 24) :
    96 ≤ ∑ t ∈ Finset.range 7, t ^ 2 * c t := by
  norm_num [Finset.sum_range_succ] at hcard hsum ⊢
  omega

theorem six_cubicValues_sum_twentyFour_eq_minimum
    (c : ℕ → ℕ)
    (hcard : ∑ t ∈ Finset.range 7, c t = 6)
    (hsum : ∑ t ∈ Finset.range 7, t * c t = 24)
    (hsq : ∑ t ∈ Finset.range 7, t ^ 2 * c t ≤ 96) :
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 ∧
      c 4 = 6 ∧ c 5 = 0 ∧ c 6 = 0 := by
  norm_num [Finset.sum_range_succ] at hcard hsum hsq ⊢
  omega

/-- The four `24`-budget fibers and twelve residual `17`-budget fibers of
an antipodal target have doubled residual square mass at least 1092. -/
theorem h305_antipodal_sixteen_cubicFiber_squareMass_ge_1092
    (S24 S17 : ℕ)
    (h24 : 96 ≤ S24) (h17 : 59 ≤ S17) :
    1092 ≤ 4 * S24 + 12 * S17 := by
  omega

end Erdos85

#print axioms Erdos85.six_cubicValues_sum_twentyFive_minimum
#print axioms Erdos85.six_cubicValues_sum_twentyFive_eq_minimum
#print axioms Erdos85.five_cubicValues_sum_sixteen_minimum
#print axioms Erdos85.five_cubicValues_sum_sixteen_eq_minimum
#print axioms Erdos85.five_cubicValues_sum_seventeen_minimum
#print axioms Erdos85.five_cubicValues_sum_seventeen_eq_minimum
#print axioms Erdos85.h305_sixteen_cubicFiber_squareMass_ge_1100
#print axioms Erdos85.six_cubicValues_sum_twentyFour_minimum
#print axioms Erdos85.six_cubicValues_sum_twentyFour_eq_minimum
#print axioms Erdos85.h305_antipodal_sixteen_cubicFiber_squareMass_ge_1092
