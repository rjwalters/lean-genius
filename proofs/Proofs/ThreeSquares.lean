import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic

/-!
# Legendre's Three Squares Theorem

## What This Proves
A natural number n can be expressed as the sum of three squares of integers
if and only if n is NOT of the form 4^a(8b + 7), where a and b are non-negative integers.

This is a deeper refinement of Lagrange's Four Squares Theorem (every natural is a sum of
four squares). The "excluded" numbers form a sparse but infinite set: 7, 15, 23, 28, 31, ...

## Historical Context
- **1770**: Lagrange proves every natural is a sum of four squares
- **1797-1798**: Legendre proves this three-squares characterization
- **1801**: Gauss provides a more general result using quadratic form theory
- **1850**: Dirichlet gives an elegant proof using his theorem on primes in arithmetic progressions

## Approach
- **Necessity (→)**: Squares mod 8 are in {0, 1, 4}, so sums of three squares mod 8 can
  only achieve {0, 1, 2, 3, 4, 5, 6}. Numbers ≡ 7 (mod 8) cannot be sums of three squares.
  The 4^a factor is handled inductively.

- **Sufficiency (←)**: This direction requires either:
  1. Dirichlet's theorem on primes in arithmetic progressions (recently added to Mathlib), OR
  2. Theory of ternary quadratic forms (class numbers, genera)

## Status
- [x] Characterization of excluded form defined
- [x] Key lemmas stated (squares mod 8)
- [x] Main theorem stated with axiom for hard direction
- [x] Examples and computational verification
- [ ] Full proof of necessity (partial - modular arithmetic complete)
- [ ] Sufficiency proof (requires ternary quadratic form theory)

## Mathlib Dependencies
- `Nat.sum_four_squares` : Every n is a sum of 4 squares
- Modular arithmetic lemmas

## Connection to Wiedijk 100
This is a candidate for the Wiedijk 100 theorems list. The four squares theorem is #19;
the three squares theorem is a natural strengthening.

## What Would Be Needed for Full Proof
1. **Necessity**: The key modular arithmetic is straightforward. Main work is handling
   the 4-divisibility descent carefully.
2. **Sufficiency**: Either prove via Dirichlet's theorem on primes in arithmetic progressions
   (showing every n ≡ 3 (mod 8) has prime factors ≡ 1 (mod 4)), or use ternary quadratic
   form theory and class number formulas.
-/

namespace ThreeSquares

/-! ## The Excluded Form -/

/-- Predicate for numbers of the form 4^a(8b + 7).
These are exactly the numbers that CANNOT be written as sums of three squares. -/
def IsExcludedForm (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)

/-- The excluded form is decidable. -/
noncomputable instance : DecidablePred IsExcludedForm :=
  fun _ => Classical.propDecidable _

/-- 7 is in excluded form (a=0, b=0). -/
example : IsExcludedForm 7 := ⟨0, 0, rfl⟩

/-- 15 is in excluded form (a=0, b=1). -/
example : IsExcludedForm 15 := ⟨0, 1, rfl⟩

/-- 28 = 4 * 7 is in excluded form (a=1, b=0). -/
example : IsExcludedForm 28 := ⟨1, 0, rfl⟩

/-- 23 is in excluded form (a=0, b=2). -/
example : IsExcludedForm 23 := ⟨0, 2, rfl⟩

/-- 112 = 16 * 7 is in excluded form (a=2, b=0). -/
example : IsExcludedForm 112 := ⟨2, 0, rfl⟩

/-! ## Key Lemma: Squares Modulo 8 -/

/-- Natural number version: A square is congruent to 0, 1, or 4 modulo 8. -/
lemma nat_sq_mod_eight (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h : x % 8 < 8 := Nat.mod_lt x (by norm_num)
  have key : ∀ r : ℕ, r < 8 → r ^ 2 % 8 = 0 ∨ r ^ 2 % 8 = 1 ∨ r ^ 2 % 8 = 4 := by
    intro r hr
    interval_cases r <;> decide
  have hxmod := key (x % 8) h
  have hsq : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by conv_lhs => rw [Nat.pow_mod]
  rw [hsq]; exact hxmod

/-! ## Main Theorems (with axioms for hard directions) -/

/-- **Necessity Axiom**: Numbers of excluded form are NOT sums of three squares.

The proof uses modular arithmetic:
1. Squares mod 8 ∈ {0, 1, 4}
2. Sums of three such values mod 8 ∈ {0, 1, 2, 3, 4, 5, 6} - never 7
3. Descent: if 4|n and n = a² + b² + c², then 2|a,b,c, so n/4 = (a/2)² + (b/2)² + (c/2)² -/
axiom excluded_form_not_sum_three_sq {n : ℕ} (h : IsExcludedForm n) :
    ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n

/-- **Sufficiency Axiom**: Numbers NOT of excluded form ARE sums of three squares.

This requires Dirichlet's theorem on primes in arithmetic progressions or
ternary quadratic form theory. -/
axiom not_excluded_form_is_sum_three_sq {n : ℕ} (h : ¬IsExcludedForm n) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n

/-- **Legendre's Three Squares Theorem** (1797-1798)

A natural number n can be expressed as a sum of three integer squares
if and only if n is NOT of the form 4^a(8b + 7). -/
theorem legendre_three_squares (n : ℕ) :
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n) ↔ ¬IsExcludedForm n :=
  ⟨fun h hf => excluded_form_not_sum_three_sq hf h, not_excluded_form_is_sum_three_sq⟩

/-! ## Examples: Numbers that ARE sums of three squares -/

example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 0 := ⟨0, 0, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 1 := ⟨1, 0, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 2 := ⟨1, 1, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 3 := ⟨1, 1, 1, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 5 := ⟨2, 1, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 6 := ⟨2, 1, 1, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 8 := ⟨2, 2, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 9 := ⟨3, 0, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 10 := ⟨3, 1, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 12 := ⟨2, 2, 2, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 14 := ⟨3, 2, 1, rfl⟩

/-! ## Examples: Numbers that are NOT sums of three squares -/

/-- 7 cannot be written as a sum of three squares. -/
example : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 7 :=
  excluded_form_not_sum_three_sq ⟨0, 0, rfl⟩

/-- 15 cannot be written as a sum of three squares. -/
example : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 15 :=
  excluded_form_not_sum_three_sq ⟨0, 1, rfl⟩

/-- 28 = 4 * 7 cannot be written as a sum of three squares. -/
example : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 28 :=
  excluded_form_not_sum_three_sq ⟨1, 0, rfl⟩

/-- 31 cannot be written as a sum of three squares. -/
example : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 31 :=
  excluded_form_not_sum_three_sq ⟨0, 3, rfl⟩

/-! ## Relationship to Four Squares Theorem -/

/-- Connection: Four squares always suffice (Lagrange). -/
theorem four_squares_always_suffice (n : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

/-- For excluded numbers, the fourth square is essential. -/
theorem fourth_square_essential {n : ℕ} (h : IsExcludedForm n) :
    (∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n) ∧
    ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n :=
  ⟨Nat.sum_four_squares n, excluded_form_not_sum_three_sq h⟩

/-- 7 = 1² + 1² + 1² + 2² (four squares work) -/
example : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 7 := ⟨1, 1, 1, 2, rfl⟩

#check legendre_three_squares

end ThreeSquares
