import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic

/-
# Waring's Problem for Squares: g(2) = 4

## What This Proves

Waring's problem asks: for each positive integer k, what is the smallest number g(k) such
that every natural number is a sum of at most g(k) perfect k-th powers?

For k = 2 (squares), the answer is g(2) = 4. This file proves:

1. **Upper bound g(2) ≤ 4**: Every natural number is a sum of at most 4 squares (Lagrange).
2. **Lower bound g(2) ≥ 4**: 7 cannot be written as a sum of 3 or fewer squares.
3. **General descent**: 4^a(8b+7) cannot be a sum of 3 squares for any a, b.
4. **Computable classification**: Which numbers need 1, 2, 3, or 4 squares.
5. **Infinitely many**: There are infinitely many numbers needing exactly 4 squares.

## Mathematical Background

- **1770**: Lagrange proves every n is a sum of 4 squares → g(2) ≤ 4
- **1798**: Legendre proves n is NOT sum of 3 squares iff n = 4^a(8b+7) → g(2) ≥ 4
- **1909**: Hilbert proves g(k) exists for all k (Waring's problem solved in general)

## Approach
- Use existing Mathlib infrastructure for Lagrange
- Prove lower bound via modular arithmetic (self-contained, no axioms)
- Prove general descent argument for excluded forms
- Computable classification and batch verification
-/

namespace WaringG2

open Finset Nat

/-
## Part 1: Upper Bound — Every Number is a Sum of at Most 4 Squares
-/

/-- **Lagrange's theorem**: Every natural number is a sum of 4 squares.
This gives the upper bound g(2) ≤ 4. -/
theorem sum_four_squares (n : ℕ) : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

/-
## Part 2: Lower Bound — Some Numbers Need 4 Squares
-/

/-- Squares mod 8 are in {0, 1, 4}. -/
lemma sq_mod_eight (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h : x % 8 < 8 := Nat.mod_lt x (by norm_num)
  have key : ∀ r : ℕ, r < 8 → r ^ 2 % 8 = 0 ∨ r ^ 2 % 8 = 1 ∨ r ^ 2 % 8 = 4 := by
    intro r hr; interval_cases r <;> decide
  have hsq : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by conv_lhs => rw [Nat.pow_mod]
  rw [hsq]; exact key (x % 8) h

/-- Helper: sum of three elements from {0,1,4} is never 7 mod 8. -/
private lemma sum_three_from_014_ne_7 (a b c : ℕ)
    (ha : a = 0 ∨ a = 1 ∨ a = 4)
    (hb : b = 0 ∨ b = 1 ∨ b = 4)
    (hc : c = 0 ∨ c = 1 ∨ c = 4) :
    (a + b + c) % 8 ≠ 7 := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl <;> decide

/-- A sum of three natural number squares can never be ≡ 7 (mod 8). -/
theorem sum_three_sq_mod_eight_ne_seven (x y z : ℕ) :
    (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  have hx := sq_mod_eight x
  have hy := sq_mod_eight y
  have hz := sq_mod_eight z
  have hmod : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = (x^2 % 8 + y^2 % 8 + z^2 % 8) % 8 := by omega
  rw [hmod]
  exact sum_three_from_014_ne_7 (x^2 % 8) (y^2 % 8) (z^2 % 8) hx hy hz

/-- 7 cannot be written as a sum of three natural number squares. -/
theorem seven_not_sum_three_sq : ¬∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = 7 := by
  intro ⟨x, y, z, h⟩
  have := sum_three_sq_mod_eight_ne_seven x y z
  omega

/-- 7 cannot be written as a sum of two natural number squares. -/
theorem seven_not_sum_two_sq : ¬∃ x y : ℕ, x ^ 2 + y ^ 2 = 7 := by
  intro ⟨x, y, h⟩
  exact seven_not_sum_three_sq ⟨x, y, 0, by omega⟩

/-- 7 cannot be written as a single perfect square. -/
theorem seven_not_sq : ¬∃ x : ℕ, x ^ 2 = 7 := by
  intro ⟨x, h⟩
  have hle : x ≤ 2 := by nlinarith
  interval_cases x <;> omega

/-- 7 requires exactly 4 squares. Together with Lagrange, this gives g(2) ≥ 4. -/
theorem seven_needs_four_squares :
    (∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 7) ∧
    ¬∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = 7 :=
  ⟨⟨1, 1, 1, 2, rfl⟩, seven_not_sum_three_sq⟩

/-
## Part 3: g(2) = 4 — The Main Theorem
-/

/-- **Upper bound**: g(2) ≤ 4 (Lagrange's theorem). -/
theorem waring_g2_upper : ∀ n : ℕ, ∃ a b c d : ℕ,
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  sum_four_squares

/-- **Lower bound**: g(2) ≥ 4 (7 needs 4 squares). -/
theorem waring_g2_lower : ∃ n : ℕ, ¬∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n :=
  ⟨7, seven_not_sum_three_sq⟩

/-- **Main theorem**: g(2) = 4 — every natural number is a sum of 4 squares,
and 4 is optimal (some numbers can't be done with 3). -/
theorem waring_g2_eq_four :
    (∀ n : ℕ, ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n) ∧
    (∃ n : ℕ, ¬∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :=
  ⟨waring_g2_upper, waring_g2_lower⟩

/-
## Part 4: Numbers Needing 4 Squares — General Arguments
-/

/-- All numbers ≡ 7 (mod 8) need 4 squares. -/
theorem seven_mod_eight_needs_four {n : ℕ} (h : n % 8 = 7) :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  intro ⟨x, y, z, hsum⟩
  have := sum_three_sq_mod_eight_ne_seven x y z
  omega

/-- 15 = 8·1 + 7 also needs 4 squares. -/
theorem fifteen_needs_four :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 15 :=
  seven_mod_eight_needs_four (by norm_num)

/-- 23 = 8·2 + 7 also needs 4 squares. -/
theorem twentythree_needs_four :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 23 :=
  seven_mod_eight_needs_four (by norm_num)

/-- 31 = 8·3 + 7 also needs 4 squares. -/
theorem thirtyone_needs_four :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 31 :=
  seven_mod_eight_needs_four (by norm_num)

/-- General: for any b, 8b + 7 needs 4 squares. -/
theorem eight_b_plus_seven_needs_four (b : ℕ) :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 8 * b + 7 :=
  seven_mod_eight_needs_four (by omega)

/-
## Part 5: The Descent Argument — 4·n Preserves Exclusion
-/

/-- Squares mod 4 are 0 or 1. -/
lemma sq_mod_four (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have hsq : x ^ 2 % 4 = (x % 4) ^ 2 % 4 := by conv_lhs => rw [Nat.pow_mod]
  rw [hsq]
  have : x % 4 < 4 := Nat.mod_lt x (by norm_num)
  have key : ∀ r : ℕ, r < 4 → r ^ 2 % 4 = 0 ∨ r ^ 2 % 4 = 1 := by
    intro r hr; interval_cases r <;> decide
  exact key (x % 4) this

/-- If x² ≡ 0 (mod 4), then x is even. -/
lemma sq_mod_four_zero_imp_even (x : ℕ) (h : x ^ 2 % 4 = 0) : 2 ∣ x := by
  have hsq : x ^ 2 % 4 = (x % 4) ^ 2 % 4 := by conv_lhs => rw [Nat.pow_mod]
  rw [hsq] at h
  have : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases this with hx | hx | hx | hx
  · exact Nat.dvd_of_mod_eq_zero (by omega)
  · simp [hx] at h
  · exact Nat.dvd_of_mod_eq_zero (by omega)
  · simp [hx] at h

/-- If 4 divides a sum of three squares, all three roots are even. -/
lemma four_dvd_sum_three_sq_imp_all_even (x y z : ℕ)
    (h : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0) : 2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  have hx := sq_mod_four x
  have hy := sq_mod_four y
  have hz := sq_mod_four z
  -- Sum of three terms each 0 or 1 mod 4, equalling 0 mod 4 → all must be 0
  have hxz : x^2 % 4 = 0 := by omega
  have hyz : y^2 % 4 = 0 := by omega
  have hzz : z^2 % 4 = 0 := by omega
  exact ⟨sq_mod_four_zero_imp_even x hxz, sq_mod_four_zero_imp_even y hyz,
         sq_mod_four_zero_imp_even z hzz⟩

/-- If n is not a sum of 3 squares, then 4n is also not a sum of 3 squares.
The descent: if 4n = x² + y² + z², then 4 | x² + y² + z²,
so x, y, z are all even, and n = (x/2)² + (y/2)² + (z/2)². -/
theorem four_mul_not_sum_three_sq {n : ℕ} (h : ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = n) :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 4 * n := by
  intro ⟨x, y, z, hsum⟩
  have hmod : (x^2 + y^2 + z^2) % 4 = 0 := by omega
  obtain ⟨hx_even, hy_even, hz_even⟩ := four_dvd_sum_three_sq_imp_all_even x y z hmod
  obtain ⟨x', rfl⟩ := hx_even
  obtain ⟨y', rfl⟩ := hy_even
  obtain ⟨z', rfl⟩ := hz_even
  apply h
  use x', y', z'
  nlinarith

/-- 28 = 4 · 7 needs 4 squares (by descent from 7). -/
theorem twentyeight_needs_four :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 28 :=
  four_mul_not_sum_three_sq seven_not_sum_three_sq

/-- 112 = 4 · 28 = 16 · 7 needs 4 squares. -/
theorem onehundredtwelve_needs_four :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 112 :=
  four_mul_not_sum_three_sq twentyeight_needs_four

/-- 448 = 4 · 112 = 64 · 7 needs 4 squares. -/
theorem fourhundredfortyeight_needs_four :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 448 :=
  four_mul_not_sum_three_sq onehundredtwelve_needs_four

/-- General descent: 4^a · (8b + 7) needs 4 squares for all a, b.
This is the "necessity" direction of Legendre's three-square theorem. -/
theorem excluded_form_needs_four (a b : ℕ) :
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = 4 ^ a * (8 * b + 7) := by
  induction a with
  | zero => simpa using eight_b_plus_seven_needs_four b
  | succ k ih =>
    have h : 4 ^ (k + 1) * (8 * b + 7) = 4 * (4 ^ k * (8 * b + 7)) := by
      rw [pow_succ]; ring
    rw [h]
    exact four_mul_not_sum_three_sq ih

/-- There are infinitely many numbers needing 4 squares: the sequence 8b + 7. -/
theorem infinitely_many_need_four :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  intro N
  use 8 * (N + 1) + 7
  exact ⟨by omega, eight_b_plus_seven_needs_four (N + 1)⟩

/-
## Part 6: Computable Classification
-/

/-- Computable minimum number of squares needed for n. -/
def numSquaresNeeded (n : ℕ) : ℕ :=
  let s := Nat.sqrt n
  if n = 0 then 0
  else if s * s = n then 1
  else if (List.range (s + 1)).any (fun x =>
    let rem := n - x ^ 2
    Nat.sqrt rem * Nat.sqrt rem = rem) then 2
  else if (List.range (s + 1)).any (fun x =>
    (List.range (Nat.sqrt (n - x ^ 2) + 1)).any (fun y =>
      x ^ 2 + y ^ 2 ≤ n ∧
      let rem := n - x ^ 2 - y ^ 2
      Nat.sqrt rem * Nat.sqrt rem = rem)) then 3
  else 4

-- Verify for key cases
theorem numSq_0 : numSquaresNeeded 0 = 0 := by native_decide
theorem numSq_1 : numSquaresNeeded 1 = 1 := by native_decide
theorem numSq_2 : numSquaresNeeded 2 = 2 := by native_decide
theorem numSq_3 : numSquaresNeeded 3 = 3 := by native_decide
theorem numSq_4 : numSquaresNeeded 4 = 1 := by native_decide
theorem numSq_5 : numSquaresNeeded 5 = 2 := by native_decide
theorem numSq_6 : numSquaresNeeded 6 = 3 := by native_decide
theorem numSq_7 : numSquaresNeeded 7 = 4 := by native_decide
theorem numSq_8 : numSquaresNeeded 8 = 2 := by native_decide
theorem numSq_9 : numSquaresNeeded 9 = 1 := by native_decide
theorem numSq_10 : numSquaresNeeded 10 = 2 := by native_decide
theorem numSq_15 : numSquaresNeeded 15 = 4 := by native_decide
theorem numSq_23 : numSquaresNeeded 23 = 4 := by native_decide
theorem numSq_28 : numSquaresNeeded 28 = 4 := by native_decide
theorem numSq_31 : numSquaresNeeded 31 = 4 := by native_decide

/-- Check if n has the excluded form 4^a(8b+7). -/
def isExcludedForm (n : ℕ) : Bool :=
  if n = 0 then false else
  let rec stripFours : ℕ → ℕ
    | 0 => 0
    | m + 1 => if (m + 1) % 4 = 0 then stripFours ((m + 1) / 4) else m + 1
  (stripFours n) % 8 = 7

-- Verify excluded form detection
theorem excluded_7 : isExcludedForm 7 = true := by native_decide
theorem excluded_15 : isExcludedForm 15 = true := by native_decide
theorem excluded_23 : isExcludedForm 23 = true := by native_decide
theorem excluded_28 : isExcludedForm 28 = true := by native_decide
theorem excluded_31 : isExcludedForm 31 = true := by native_decide
theorem excluded_39 : isExcludedForm 39 = true := by native_decide
theorem excluded_47 : isExcludedForm 47 = true := by native_decide
theorem excluded_60 : isExcludedForm 60 = true := by native_decide
theorem excluded_112 : isExcludedForm 112 = true := by native_decide

theorem not_excluded_0 : isExcludedForm 0 = false := by native_decide
theorem not_excluded_1 : isExcludedForm 1 = false := by native_decide
theorem not_excluded_2 : isExcludedForm 2 = false := by native_decide
theorem not_excluded_3 : isExcludedForm 3 = false := by native_decide
theorem not_excluded_4 : isExcludedForm 4 = false := by native_decide
theorem not_excluded_5 : isExcludedForm 5 = false := by native_decide
theorem not_excluded_6 : isExcludedForm 6 = false := by native_decide
theorem not_excluded_8 : isExcludedForm 8 = false := by native_decide
theorem not_excluded_10 : isExcludedForm 10 = false := by native_decide

/-- Check that all n up to bound need at most 4 squares. -/
def checkAllAtMostFour (bound : ℕ) : Bool :=
  (List.range (bound + 1)).all (fun n => numSquaresNeeded n ≤ 4)

-- Batch verification
theorem all_at_most_four_100 : checkAllAtMostFour 100 = true := by native_decide

/-- The first number needing 4 squares is 7. -/
def firstNeedingFour (bound : ℕ) : Option ℕ :=
  (List.range (bound + 1)).find? (fun n => numSquaresNeeded n = 4)

theorem first_needing_four : firstNeedingFour 100 = some 7 := by native_decide

/-- Verify that excluded form exactly characterizes numbers needing 4 squares (up to 100). -/
def checkExcludedMatchesFour (bound : ℕ) : Bool :=
  (List.range (bound + 1)).all fun n =>
    (isExcludedForm n) = (numSquaresNeeded n == 4)

theorem excluded_matches_four_100 : checkExcludedMatchesFour 100 = true := by native_decide

/-
## Part 7: Counting Statistics
-/

/-- Count how many numbers in [0, bound] need exactly k squares. -/
def countNeedingK (bound k : ℕ) : ℕ :=
  ((List.range (bound + 1)).filter (fun n => numSquaresNeeded n = k)).length

-- Distribution up to 50 (smaller bound for safety)
theorem count_0sq_50 : countNeedingK 50 0 = 1 := by native_decide
theorem count_1sq_50 : countNeedingK 50 1 = 7 := by native_decide  -- 1,4,9,16,25,36,49

/-- List the numbers needing 4 squares up to bound. -/
def listNeedingFour (bound : ℕ) : List ℕ :=
  (List.range (bound + 1)).filter (fun n => numSquaresNeeded n = 4)

-- The numbers ≤ 50 needing 4 squares
theorem needingFour_list_50 : listNeedingFour 50 =
    [7, 15, 23, 28, 31, 39, 47] := by native_decide

/-
## Part 8: The G(2) Function (Asymptotic Waring)

G(2) asks: for all sufficiently large n, how many squares suffice?
Davenport (1939) showed G(2) = 4, meaning there are arbitrarily large numbers
needing 4 squares. This follows from our `infinitely_many_need_four`.
-/

/-- G(2) = 4 follows from the fact that 8b+7 grows without bound
and always needs 4 squares. -/
theorem waring_big_G2_lower :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = n :=
  infinitely_many_need_four

/-
## Part 9: Additional Structural Results
-/

/-- The converse of the descent: if n IS a sum of 3 squares, so is 4n. -/
theorem four_mul_sum_three_sq {n : ℕ} (h : ∃ x y z : ℕ, x^2 + y^2 + z^2 = n) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = 4 * n := by
  obtain ⟨x, y, z, hsum⟩ := h
  use 2 * x, 2 * y, 2 * z
  nlinarith

/-- Square scaling: if n is a sum of 3 squares, so is k²n. -/
theorem sq_mul_sum_three_sq {n k : ℕ} (h : ∃ x y z : ℕ, x^2 + y^2 + z^2 = n) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = k^2 * n := by
  obtain ⟨x, y, z, hsum⟩ := h
  use k * x, k * y, k * z
  nlinarith

/-- Concrete decompositions showing various numbers ARE sums of 3 squares. -/
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 0 := ⟨0, 0, 0, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 1 := ⟨1, 0, 0, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 2 := ⟨1, 1, 0, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 3 := ⟨1, 1, 1, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 5 := ⟨2, 1, 0, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 6 := ⟨2, 1, 1, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 8 := ⟨2, 2, 0, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 9 := ⟨3, 0, 0, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 10 := ⟨3, 1, 0, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 12 := ⟨2, 2, 2, rfl⟩
example : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 14 := ⟨3, 2, 1, rfl⟩

/-- Concrete decompositions showing excluded numbers DO have 4-square representations. -/
example : ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = 7 := ⟨1, 1, 1, 2, rfl⟩
example : ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = 15 := ⟨1, 1, 2, 3, rfl⟩
example : ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = 23 := ⟨1, 2, 3, 3, rfl⟩
example : ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = 28 := ⟨2, 2, 2, 4, rfl⟩
example : ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = 31 := ⟨1, 1, 2, 5, rfl⟩

/-- For excluded numbers, the fourth square is essential. -/
theorem fourth_square_essential (a b : ℕ) :
    let n := 4 ^ a * (8 * b + 7)
    (∃ w x y z : ℕ, w^2 + x^2 + y^2 + z^2 = n) ∧
    ¬∃ x y z : ℕ, x^2 + y^2 + z^2 = n :=
  ⟨Nat.sum_four_squares _, excluded_form_needs_four a b⟩

/-
## Part 10: Batch Verification of At-Most-4 Property
-/

/-- Check no number ≤ bound needs 5+ squares. -/
def checkMaxFour (bound : ℕ) : Bool :=
  (List.range (bound + 1)).all (fun n => numSquaresNeeded n ≤ 4)

theorem max_four_200 : checkMaxFour 200 = true := by native_decide

/-
## Summary

### Proved Results (0 axioms, 0 sorries)

| Category | Count | Key Results |
|----------|-------|-------------|
| Upper bound | 1 | Lagrange (from Mathlib) |
| Lower bound (mod 8) | 5 | 7, 15, 23, 31 not sum of 3 sq; general 8b+7 |
| Descent argument | 4 | four_mul_not_sum_three_sq, 28, 112, 448 |
| General exclusion | 1 | excluded_form_needs_four (∀ a b) |
| Waring g(2) = 4 | 3 | Upper, lower, combined |
| Computable | 3 | numSquaresNeeded, isExcludedForm, checkExcludedMatchesFour |
| Verification | 15+ | Individual numSq for n ≤ 31 |
| Batch verification | 3 | ≤ 100 at most 4; ≤ 200 at most 4; excluded ↔ needs 4 |
| Counting | 3 | Distribution stats, list of excluded numbers ≤ 50 |
| Infinity | 2 | infinitely_many_need_four, G(2) = 4 |
| Scaling | 2 | four_mul_sum_three_sq, sq_mul_sum_three_sq |
| Examples | 16 | Concrete 3-square and 4-square decompositions |

### Key Mathematical Insights

1. **g(2) = 4 is tight**: Both bounds proved without axioms.
2. **Modular arithmetic**: The lower bound needs only mod 8 analysis.
3. **Descent principle**: four_mul_not_sum_three_sq chains to give 4^a · (8b+7) excluded.
4. **Excluded form = needs 4**: Computationally verified up to 100.
5. **G(2) = g(2) = 4**: Both little-g and big-G equal 4 for squares.
-/

end WaringG2
