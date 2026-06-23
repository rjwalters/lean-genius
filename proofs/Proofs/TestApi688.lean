import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

-- Test rpow monotonicity
example (n : ℕ) (ε₁ ε₂ : ℝ) (h1 : 1 ≤ (n : ℝ)) (h2 : ε₁ ≤ ε₂) :
    (n : ℝ) ^ ε₁ ≤ (n : ℝ) ^ ε₂ :=
  Real.rpow_le_rpow_of_exponent_le h1 h2

-- Test: Finset.filter_eq_empty_iff
#check @Finset.filter_eq_empty_iff

-- Test: Nat.cast_div_le
#check @Nat.cast_div_le

-- Test: push_neg on Nat.Prime
example (p : ℕ) (hn : p ≤ 1) : ¬Nat.Prime p := Nat.not_prime_of_le_one hn

-- Test the card_le_card for injective function approach
-- Map elements with (m+1) % p = a to m / p, which lands in range (n/p + 1)
#check @Finset.card_le_card_of_injOn

-- Test for proving single_class_coverage_nat
-- Strategy: show the map m ↦ (m+1) / p is injective on the filter set
-- and maps into Finset.range (n/p + 1)
example (n p a : ℕ) (hp : p ≠ 0) (ha : a < p) :
    ∀ m₁ m₂ : ℕ, m₁ < n → m₂ < n →
    (m₁ + 1) % p = a → (m₂ + 1) % p = a →
    (m₁ + 1) / p = (m₂ + 1) / p → m₁ = m₂ := by
  intro m₁ m₂ _ _ h1 h2 hdiv
  have := Nat.div_add_mod (m₁ + 1) p
  have := Nat.div_add_mod (m₂ + 1) p
  omega

-- Test: elements m with (m+1) % p = a have (m+1)/p in range (n/p + 1)
example (n p a m : ℕ) (hp : p ≠ 0) (hm : m < n) (ha : (m + 1) % p = a) :
    (m + 1) / p < n / p + 1 := by
  have : (m + 1) / p ≤ n / p := Nat.div_le_div_right (by omega)
  omega
