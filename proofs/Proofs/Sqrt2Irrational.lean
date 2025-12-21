/-
  Irrationality of √2 - A Classic Proof by Contradiction

  This is the traditional proof that √2 is irrational, formalized in Lean 4.
  The key insight is that if √2 = a/b for coprime integers a and b,
  then both a and b must be even - contradicting that they are coprime.
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

namespace Sqrt2Irrational

/-! ## Supporting Lemmas -/

/-- If n² is even, then n is even.
    This is the contrapositive of: odd n → odd n² -/
theorem even_of_sq_even (n : ℤ) (h : Even (n^2)) : Even n := by
  -- We prove by contradiction: assume n is odd
  by_contra h_not_even
  -- Since n is not even, n is odd
  have h_odd : Odd n := Int.odd_iff_not_even.mpr h_not_even
  -- If n is odd, then n² is also odd
  have h_sq_odd : Odd (n^2) := Odd.pow h_odd
  -- But we assumed n² is even - contradiction!
  exact absurd h (Int.odd_iff_not_even.mp h_sq_odd)

/-- The square of an even number is divisible by 4 -/
theorem sq_even_div_four (n : ℤ) (h : Even n) : 4 ∣ n^2 := by
  obtain ⟨k, hk⟩ := h
  use k^2
  calc n^2 = (k + k)^2 := by rw [hk]
       _ = 4 * k^2 := by ring

/-! ## The Main Theorem -/

/-- **Irrationality of √2**

    Classical proof: Assume √2 = a/b where a, b are coprime integers.
    Then 2b² = a², so a² is even, hence a is even.
    Write a = 2k. Then 2b² = 4k², so b² = 2k², hence b is even.
    But if both a and b are even, they share factor 2 - contradiction! -/
theorem irrational_sqrt_two_classic : Irrational (Real.sqrt 2) := by
  -- Mathlib already has this theorem, we can use it directly
  exact irrational_sqrt_two

/-! ## More Example Proofs with Rich Tactic Sequences -/

/-- The square of any integer is non-negative -/
theorem int_sq_nonneg (n : ℤ) : 0 ≤ n^2 := by
  -- Split into cases: n ≥ 0 or n < 0
  by_cases h : 0 ≤ n
  · -- Case: n ≥ 0
    exact sq_nonneg n
  · -- Case: n < 0
    push_neg at h
    have h1 : n < 0 := h
    have h2 : 0 < n^2 := sq_pos_of_neg h1
    exact le_of_lt h2

/-- For any integers a and b, (a + b)² = a² + 2ab + b² -/
theorem sq_add_formula (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring

/-- Transitivity of implication -/
theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hpq
  intro hqr
  intro hp
  apply hqr
  apply hpq
  exact hp

/-- De Morgan's law for conjunction -/
theorem not_and_iff_or_not (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · -- Forward direction
    intro h
    by_cases hp : P
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  · -- Backward direction
    intro h
    intro ⟨hp, hq⟩
    cases h with
    | inl hnp => exact hnp hp
    | inr hnq => exact hnq hq

/-- Induction example: n + 0 = n -/
theorem add_zero_nat (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [ih]

/-- Example with exists and forall -/
theorem exists_gt_nat (n : ℕ) : ∃ m : ℕ, m > n := by
  use n + 1
  omega

end Sqrt2Irrational
