/-
  Aristotle targets for Erdos673Problem
  Routine supporting lemmas for automated proof search.
  See Erdos673Problem.lean for the main formalization.
-/
import Mathlib

namespace Erdos673.Aristotle

open Nat Finset

/-- τ(1) = 1. -/
theorem tau_one : (1 : ℕ).divisors.card = 1 := by
  simp [Nat.divisors_one]

/-- τ(p) = 2 for prime p. -/
theorem tau_prime (p : ℕ) (hp : p.Prime) : p.divisors.card = 2 := by
  rw [Nat.Prime.divisors hp]
  exact Finset.card_pair hp.one_lt.ne

/-
PROBLEM
τ(p²) = 3 for prime p.

PROVIDED SOLUTION
Use Nat.divisors_prime_pow to rewrite the divisors of p^2, then compute the card of the resulting finset (range 3 mapped by an injective function has card 3).
-/
theorem tau_prime_sq (p : ℕ) (hp : p.Prime) : (p ^ 2).divisors.card = 3 := by
  rw [ Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range ]

-- Needs factorization of p^2; Aristotle target

/-- τ(6) = 4. -/
theorem tau_6 : (6 : ℕ).divisors.card = 4 := by native_decide

/-- τ(12) = 6. -/
theorem tau_12 : (12 : ℕ).divisors.card = 6 := by native_decide

/-- Divisors of a prime p are {1, p}. -/
theorem divisors_prime (p : ℕ) (hp : p.Prime) : p.divisors = {1, p} :=
  Nat.Prime.divisors hp

/-- 1 divides every natural number. -/
theorem one_dvd_all (n : ℕ) : 1 ∣ n := one_dvd n

/-- n divides n. -/
theorem self_dvd (n : ℕ) : n ∣ n := dvd_refl n

/-- For n ≥ 1: 1 ∈ n.divisors. -/
theorem one_mem_divisors (n : ℕ) (hn : n ≥ 1) : 1 ∈ n.divisors :=
  Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩

/-- For n ≥ 1: n ∈ n.divisors. -/
theorem self_mem_divisors (n : ℕ) (hn : n ≥ 1) : n ∈ n.divisors :=
  Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩

/-- Consecutive divisor ratio is at most 1: a/b ≤ 1 when a ≤ b. -/
theorem ratio_le_one (a b : ℕ) (_ha : a ≥ 1) (hab : a ≤ b) :
    (a : ℝ) / (b : ℝ) ≤ 1 := by
  have hb : (0 : ℝ) < b := by exact_mod_cast Nat.lt_of_lt_of_le (by omega : 0 < a) hab
  rw [div_le_one hb]
  exact_mod_cast hab

/-- Divisor ratio is non-negative. -/
theorem ratio_nonneg (a b : ℕ) (_hb : b ≥ 1) :
    0 ≤ (a : ℝ) / (b : ℝ) := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- For coprime a, b: τ(a*b) = τ(a) * τ(b). -/
theorem tau_multiplicative (a b : ℕ) (_ha : a ≥ 1) (_hb : b ≥ 1)
    (hcop : Nat.Coprime a b) :
    (a * b).divisors.card = a.divisors.card * b.divisors.card :=
  Nat.Coprime.card_divisors_mul hcop

/-- Sum of ratios dᵢ/dᵢ₊₁ is non-negative. -/
theorem sum_ratios_nonneg (l : List ℕ) (_hl : ∀ x ∈ l, x ≥ 1) :
    0 ≤ ∑ i ∈ Finset.range (l.length - 1),
      ((l.getD i 0 : ℝ) / (l.getD (i + 1) 0 : ℝ)) := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end Erdos673.Aristotle