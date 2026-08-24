import Proofs.Erdos85ConnectedIncidenceBottleneckDyadicStrict
import Proofs.Erdos85ThreeSeparatorBottomWingRigidity

/-!
# Dyadic residues for the bottom three-separator slices

The exact B48/B51 profiles split according to `q = 3r+1` or `q = 3r+2`.
For the binary parameter `q=2^k`, these are exactly the even- and
odd-exponent cases.  This file supplies that bridge in decomposition form.
-/

namespace Erdos85

/-- A natural number with residue one modulo three has the required exact
`3r+1` decomposition. -/
theorem exists_eq_three_mul_add_one_of_mod_three_eq_one
    (q : ℕ) (hmod : q % 3 = 1) :
    ∃ r, q = 3 * r + 1 := by
  refine ⟨q / 3, ?_⟩
  have hdecomp := Nat.mod_add_div q 3
  omega

/-- A natural number with residue two modulo three has the required exact
`3r+2` decomposition. -/
theorem exists_eq_three_mul_add_two_of_mod_three_eq_two
    (q : ℕ) (hmod : q % 3 = 2) :
    ∃ r, q = 3 * r + 2 := by
  refine ⟨q / 3, ?_⟩
  have hdecomp := Nat.mod_add_div q 3
  omega

/-- Even binary exponents select the `3r+1` bottom-profile branch. -/
theorem twoPow_exists_three_mul_add_one_of_even
    (k : ℕ) (hk : Even k) :
    ∃ r, 2 ^ k = 3 * r + 1 := by
  apply exists_eq_three_mul_add_one_of_mod_three_eq_one
  exact (two_pow_mod_three_eq_of_parity k).1 hk

/-- Odd binary exponents select the `3r+2` bottom-profile branch. -/
theorem twoPow_exists_three_mul_add_two_of_odd
    (k : ℕ) (hk : Odd k) :
    ∃ r, 2 ^ k = 3 * r + 2 := by
  apply exists_eq_three_mul_add_two_of_mod_three_eq_two
  exact (two_pow_mod_three_eq_of_parity k).2 hk

/-- Complete parity-indexed residue split for the actual binary degree. -/
theorem twoPow_bottomProfile_residue_cases (k : ℕ) :
    (Even k ∧ ∃ r, 2 ^ k = 3 * r + 1) ∨
      (Odd k ∧ ∃ r, 2 ^ k = 3 * r + 2) := by
  rcases Nat.even_or_odd k with hk | hk
  · exact Or.inl ⟨hk, twoPow_exists_three_mul_add_one_of_even k hk⟩
  · exact Or.inr ⟨hk, twoPow_exists_three_mul_add_two_of_odd k hk⟩

end Erdos85

#print axioms Erdos85.exists_eq_three_mul_add_one_of_mod_three_eq_one
#print axioms Erdos85.exists_eq_three_mul_add_two_of_mod_three_eq_two
#print axioms Erdos85.twoPow_exists_three_mul_add_one_of_even
#print axioms Erdos85.twoPow_exists_three_mul_add_two_of_odd
#print axioms Erdos85.twoPow_bottomProfile_residue_cases
