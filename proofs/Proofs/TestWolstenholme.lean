import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

-- Wilson's theorem: (p-1)! ≡ -1 (mod p)
-- In ZMod p: product of nonzero elements = -1
#check ZMod.prod_univ_prime
-- Fermat's little theorem
#check ZMod.pow_card_sub_one_eq_one
#check ZMod.units_pow_card_sub_one_eq_one
-- Sum of powers
#check Finset.sum_pow_eq_pow_sum
-- ZMod field instance
#check ZMod.instField
-- Finite field power sum
example (p : ℕ) (hp : Fact (Nat.Prime p)) (k : ℕ) (hk : 1 ≤ k) (hkp : k < p - 1) :
    ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ k = 0 := by
  sorry
