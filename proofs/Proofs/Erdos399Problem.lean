/-
Erdős Problem #399: Factorial Diophantine Equations

**Problem (Erdős)**: Is it true that there are no solutions to
  n! = x^k ± y^k
with x,y,n ∈ ℕ, xy > 1, and k > 2?

**Answer**: NO — Disproved by Jonas Barfield who found the counterexample:
  10! = 48^4 - 36^4

**Historical Results**:
- Erdős-Obláth (1937): No solutions when gcd(x,y)=1 and k≠4
- Pollack-Shapiro (1973): No solutions to n! = x^4 - 1
- Cambie: No solutions to n! = x^4 + y^4 with gcd(x,y)=1 and xy > 1
- Only solution to n! = x^2 + y^2 is 6! = 12^2 + 24^2

Reference: https://erdosproblems.com/399
-/

import Mathlib

open Nat

namespace Erdos399

/-! ## The Counterexample -/

/-- 10! = 3628800 -/
theorem factorial_10 : 10! = 3628800 := by native_decide

/-- 48^4 = 5308416 -/
theorem pow_48_4 : (48 : ℕ)^4 = 5308416 := by native_decide

/-- 36^4 = 1679616 -/
theorem pow_36_4 : (36 : ℕ)^4 = 1679616 := by native_decide

/-- Barfield's counterexample: 10! = 48^4 - 36^4 -/
theorem barfield_counterexample : 10! + (36 : ℕ)^4 = (48 : ℕ)^4 := by native_decide

/-- The condition xy > 1 is satisfied: 48 * 36 = 1728 > 1 -/
theorem barfield_xy_gt_one : 1 < 48 * 36 := by decide

/-- The condition k > 2 is satisfied: 4 > 2 -/
theorem barfield_k_gt_two : 2 < 4 := by decide

/-! ## Main Result -/

/--
**Erdős Problem #399** is DISPROVED:

The conjecture claimed there are no solutions to n! = x^k ± y^k with xy > 1 and k > 2.
However, Barfield's counterexample 10! = 48^4 - 36^4 shows such solutions exist.

We state this as: there exists a counterexample to the conjecture.
-/
theorem erdos_399_disproved :
    ∃ n : ℕ, ∃ x : ℕ, ∃ y : ℕ, ∃ k : ℕ, 1 < x * y ∧ 2 < k ∧ Nat.factorial n + y^k = x^k := by
  exact ⟨10, 48, 36, 4, by decide⟩

/-- Alternative form: 10! = 48^4 - 36^4 -/
theorem erdos_399_alt : (10! : ℤ) = (48 : ℤ)^4 - (36 : ℤ)^4 := by native_decide

/-! ## Historical Results (Axiomatized) -/

/--
**Erdős-Obláth Theorem (1937)**: There are no solutions to n! = x^k ± y^k
when gcd(x,y) = 1 and k ≠ 4.

The proof uses deep results from algebraic number theory including the
analysis of the Fermat equation in cyclotomic fields.
-/
axiom erdos_oblath {n x y k : ℕ} :
    x.Coprime y → 1 < x * y → 2 < k → k ≠ 4 →
    n! ≠ x^k + y^k ∧ n! + y^k ≠ x^k

/--
**Pollack-Shapiro Theorem (1973)**: There are no solutions to n! = x^4 - 1.

This was called "the next to last case" because it left open the
case of n! = x^4 - y^4 with y > 1, which Barfield later resolved.
-/
axiom pollack_shapiro (n x : ℕ) : n! + 1 ≠ x^4

/--
**Cambie's Observation**: There are no solutions to n! = x^4 + y^4
with gcd(x,y) = 1 and xy > 1.

This follows from considerations modulo 8.
-/
axiom cambie {n x y : ℕ} :
    x.Coprime y → 1 < x * y → n! ≠ x^4 + y^4

/-! ## Sum of Two Squares -/

/-- Verification: 6! = 720 -/
theorem factorial_6 : 6! = 720 := by native_decide

/-- Verification: 12^2 + 24^2 = 144 + 576 = 720 -/
theorem sum_squares_720 : (12 : ℕ)^2 + (24 : ℕ)^2 = 720 := by native_decide

/-- The equation 6! = 12^2 + 24^2 holds -/
theorem six_factorial_sum_squares : 6! = (12 : ℕ)^2 + (24 : ℕ)^2 := by native_decide

/--
**Erdős-Obláth**: The only solution to n! = x^2 + y^2 with xy > 1
is 6! = 12^2 + 24^2 (up to swapping x and y).

The proof uses Breusch's result that consecutive primes ≡ 3 (mod 4)
satisfy q_{i+1} < 2q_i (except q_1 = 3), together with Fermat's theorem
on sums of two squares.
-/
axiom sum_two_squares_unique :
    ∀ {n x y : ℕ}, 1 < x * y → n! = x^2 + y^2 →
    n = 6 ∧ (x = 12 ∧ y = 24 ∨ x = 24 ∧ y = 12)

/-! ## Properties of the Solution -/

/-- GCD(48, 36) = 12, so they are NOT coprime -/
theorem barfield_gcd : Nat.gcd 48 36 = 12 := by native_decide

/-- The counterexample works precisely because gcd(x,y) > 1 -/
theorem barfield_not_coprime : ¬ Nat.Coprime 48 36 := by
  intro h
  have : Nat.gcd 48 36 = 1 := h
  simp [barfield_gcd] at this

/-- We can write 48^4 - 36^4 = 12^4 * (4^4 - 3^4) = 12^4 * 175 -/
theorem barfield_factored : (48 : ℕ)^4 - (36 : ℕ)^4 = (12 : ℕ)^4 * 175 := by native_decide

/-- 12^4 = 20736 -/
theorem pow_12_4 : (12 : ℕ)^4 = 20736 := by native_decide

/-- 4^4 - 3^4 = 256 - 81 = 175 -/
theorem diff_4_3_pow4 : (4 : ℕ)^4 - (3 : ℕ)^4 = 175 := by native_decide

end Erdos399
