/-
  Erdős Problem #674: The Equation x^x y^y = z^z

  Source: https://erdosproblems.com/674
  Status: SOLVED (Ko 1940, with further results by Schinzel, Dem'janenko, Uchiyama)

  Statement:
  Are there any integer solutions to x^x y^y = z^z with x, y, z > 1?

  Solution:
  - YES, infinitely many solutions exist (Ko 1940)
  - Ko's family: x = 2^12 · 3^6, y = 2^8 · 3^8, z = 2^11 · 3^7 is an example
  - No solutions when gcd(x,y) = 1 (Ko 1940)
  - All solutions have x, y, z sharing the same prime factors (Dem'janenko 1975)

  Tags: number-theory, diophantine-equations, exponential-equations
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Tactic

namespace Erdos674

open Nat

/- ## Part I: The Main Equation -/

/-- A solution to x^x y^y = z^z with x, y, z > 1. -/
structure Solution where
  x : ℕ
  y : ℕ
  z : ℕ
  hx : x > 1
  hy : y > 1
  hz : z > 1
  eq : x ^ x * y ^ y = z ^ z

/-- The main question: Do solutions exist? -/
def SolutionsExist : Prop := Nonempty Solution

/-- Ko (1940): YES, solutions exist. -/
theorem ko_1940 : SolutionsExist := by
  sorry

/- ## Part II: Ko's Explicit Solution -/

/-- Ko's example: x = 2^12 · 3^6. -/
def koX : ℕ := 2 ^ 12 * 3 ^ 6

/-- Ko's example: y = 2^8 · 3^8. -/
def koY : ℕ := 2 ^ 8 * 3 ^ 8

/-- Ko's example: z = 2^11 · 3^7. -/
def koZ : ℕ := 2 ^ 11 * 3 ^ 7

/-- koX > 1. -/
theorem koX_gt_one : koX > 1 := by
  unfold koX
  norm_num

/-- koY > 1. -/
theorem koY_gt_one : koY > 1 := by
  unfold koY
  norm_num

/-- koZ > 1. -/
theorem koZ_gt_one : koZ > 1 := by
  unfold koZ
  norm_num

/-- Ko's solution satisfies the equation. -/
theorem ko_solution_valid : koX ^ koX * koY ^ koY = koZ ^ koZ := by
  sorry

/-- Ko's solution as a Solution structure. -/
noncomputable def koSolution : Solution where
  x := koX
  y := koY
  z := koZ
  hx := koX_gt_one
  hy := koY_gt_one
  hz := koZ_gt_one
  eq := ko_solution_valid

/- ## Part III: The Coprime Case -/

/-- No solutions exist when gcd(x, y) = 1. -/
theorem no_coprime_solutions (s : Solution) : s.x.gcd s.y ≠ 1 := by
  sorry

/-- Equivalently: All solutions have gcd(x, y) > 1. -/
theorem solutions_share_factor (s : Solution) : s.x.gcd s.y > 1 := by
  sorry

/- ## Part IV: Schinzel's Result -/

/-- Schinzel (1958): Every prime dividing x or y divides both. -/
theorem schinzel_1958 (s : Solution) (p : ℕ) (hp : p.Prime) :
    (p ∣ s.x ↔ p ∣ s.y) := by
  sorry

/-- Schinzel's conjecture: x, y, z have identical prime factors. -/
def SchinzelConjecture : Prop :=
  ∀ s : Solution, ∀ p : ℕ, p.Prime →
    (p ∣ s.x ↔ p ∣ s.y) ∧ (p ∣ s.y ↔ p ∣ s.z)

/- ## Part V: Dem'janenko's Theorem -/

/-- Dem'janenko (1975): Schinzel's conjecture is true. -/
theorem demjanenko_1975 : SchinzelConjecture := by
  sorry

/-- All three variables share the same prime divisors. -/
theorem same_prime_divisors (s : Solution) :
    s.x.primeFactors = s.y.primeFactors ∧
    s.y.primeFactors = s.z.primeFactors := by
  sorry

/- ## Part VI: Mills' Constraint -/

/-- The ratio Q = xy / z². -/
noncomputable def ratioQ (s : Solution) : ℚ :=
  (s.x * s.y : ℚ) / (s.z ^ 2 : ℚ)

/-- Mills: No non-trivial solutions when 4xy > z². -/
theorem mills_no_solutions_large_product (s : Solution) :
    ¬(4 * s.x * s.y > s.z ^ 2 ∧ s.x ≠ s.y) := by
  sorry

/-- Ko's family satisfies 4xy = z². -/
theorem ko_family_ratio : 4 * koX * koY = koZ ^ 2 := by
  sorry

/-- Mills: Only Ko's family satisfies 4xy = z². -/
def MillsTheorem : Prop :=
  ∀ s : Solution, 4 * s.x * s.y = s.z ^ 2 →
    ∃ n : ℕ, -- Ko's parametric family
      let a := 2 ^ (n + 1)
      let b := 2 ^ n - 1
      s.x.primeFactors = {2} ∪ b.primeFactors

/- ## Part VII: Uchiyama's Finiteness -/

/-- Uchiyama (1984): For fixed Q ∈ (0, 1/4), finitely many solutions. -/
theorem uchiyama_finiteness (Q : ℚ) (hQ : 0 < Q) (hQ' : Q < 1/4) :
    Set.Finite {s : Solution | ratioQ s = Q} := by
  sorry

/-- No solutions for Q = (1 - k²)/4 with k ∈ (0, 1) rational. -/
theorem uchiyama_special_Q (k : ℚ) (hk : 0 < k) (hk' : k < 1) :
    ¬∃ s : Solution, ratioQ s = (1 - k ^ 2) / 4 := by
  sorry

/- ## Part VIII: Ko's General Family -/

/-- Ko's parametric family: For n ≥ 2. -/
def koFamily (n : ℕ) : ℕ × ℕ × ℕ :=
  let a := 2 ^ (n + 1)
  let b := 2 ^ n - 1
  let base := 2 ^ (a * (b - n)) * b ^ (2 * b)
  (base * 2 ^ (2 * n), base * b ^ 2, base * 2 ^ (n + 1) * b)

/-- Ko's family produces valid solutions for appropriate n. -/
theorem ko_family_valid (n : ℕ) (hn : n ≥ 2) :
    let (x, y, z) := koFamily n
    x > 1 ∧ y > 1 ∧ z > 1 ∧ x ^ x * y ^ y = z ^ z := by
  sorry

/-- Ko's family gives infinitely many solutions. -/
theorem infinitely_many_solutions :
    Set.Infinite {s : Solution | True} := by
  sorry

/- ## Part IX: Computational Bounds -/

/-- Mills' computational search: No solutions with 4xy < z² for small (x,y). -/
def MillsComputational : Prop :=
  ∀ x y z : ℕ, x > 1 → y > 1 → z > 1 →
    x < 6 ^ 150 → y < 6 ^ 150 →
    x ^ x * y ^ y = z ^ z →
    4 * x * y ≥ z ^ 2

/-- Mills' computational result. -/
theorem mills_computational : MillsComputational := by
  sorry

/- ## Part X: Structure of Solutions -/

/-- All solutions have a specific form related to Ko's construction. -/
def IsKoType (s : Solution) : Prop :=
  ∃ n : ℕ, n ≥ 2 ∧
    let (x, y, z) := koFamily n
    s.x = x ∧ s.y = y ∧ s.z = z

/-- Conjecture: All solutions are of Ko type. -/
def KoConjectureFull : Prop :=
  ∀ s : Solution, IsKoType s

/-- The ratio constraint. -/
theorem ratio_constraint (s : Solution) :
    ratioQ s ≤ 1/4 := by
  sorry

/-- Equality iff Ko family. -/
theorem ratio_equality_ko (s : Solution) :
    ratioQ s = 1/4 ↔ 4 * s.x * s.y = s.z ^ 2 := by
  sorry

/- ## Part XI: Small Cases -/

/-- No solution with x = 2. -/
theorem no_solution_x_eq_2 :
    ¬∃ y z : ℕ, y > 1 ∧ z > 1 ∧ 2 ^ 2 * y ^ y = z ^ z := by
  sorry

/-- No solution with x = 3. -/
theorem no_solution_x_eq_3 :
    ¬∃ y z : ℕ, y > 1 ∧ z > 1 ∧ 3 ^ 3 * y ^ y = z ^ z := by
  sorry

/-- No solution with x = y. -/
theorem no_solution_x_eq_y :
    ¬∃ x z : ℕ, x > 1 ∧ z > 1 ∧ x ^ x * x ^ x = z ^ z := by
  sorry

/-- Equivalently: x^{2x} ≠ z^z for x, z > 1. -/
theorem no_double_solution (x z : ℕ) (hx : x > 1) (hz : z > 1) :
    x ^ (2 * x) ≠ z ^ z := by
  sorry

/- ## Part XII: Ordering -/

/-- WLOG, assume x ≤ y in solutions. -/
theorem wlog_x_le_y (s : Solution) :
    ∃ s' : Solution, s'.x ≤ s'.y ∧
      ({s'.x, s'.y} : Finset ℕ) = {s.x, s.y} ∧ s'.z = s.z := by
  sorry

/-- In any solution, z is between x and y (roughly). -/
theorem z_ordering (s : Solution) (hxy : s.x ≤ s.y) :
    s.x < s.z ∧ s.z < s.y := by
  sorry

end Erdos674

/-
  ## Summary

  This file formalizes Erdős Problem #674 on the equation x^x y^y = z^z.

  **Status**: SOLVED (Ko 1940 + subsequent work)

  **The Question**: Are there integer solutions with x, y, z > 1?

  **Answer**: YES! Infinitely many solutions exist.

  **Key Results**:
  - Ko (1940): Discovered solutions, proved none exist when gcd(x,y) = 1
  - Ko's example: x = 2^12·3^6, y = 2^8·3^8, z = 2^11·3^7
  - Schinzel (1958): Primes dividing x must divide y
  - Dem'janenko (1975): x, y, z share identical prime factors
  - Mills: No solutions with 4xy > z², only Ko family for 4xy = z²
  - Uchiyama (1984): Finitely many solutions for each fixed Q = xy/z² < 1/4

  **What we formalize**:
  1. Solution structure
  2. Ko's explicit solution
  3. Coprime impossibility
  4. Schinzel's prime divisor result
  5. Dem'janenko's theorem
  6. Mills' constraint
  7. Uchiyama's finiteness
  8. Ko's parametric family
  9. Small cases

  **Key sorries**:
  - `ko_solution_valid`: Verification of Ko's example
  - `demjanenko_1975`: Main structural result
  - `infinitely_many_solutions`: Ko family produces infinitely many
-/
