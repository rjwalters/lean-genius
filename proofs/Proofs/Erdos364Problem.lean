/-
Erdős Problem #364: Consecutive Powerful Numbers

A positive integer n is **powerful** if for every prime p dividing n, we have p² | n.
Equivalently, n can be written as a²b³ for some integers a, b ≥ 1.

Examples: 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100, ...

**Question**: Are there three consecutive powerful numbers n, n+1, n+2?

**Status**: OPEN (believed to be NO)

**Known Results**:
- Pairs exist infinitely: Pell equation x² = 8y² + 1 gives (8,9), (288,289), ...
- Quadruples impossible: one of four consecutive integers is ≡ 2 (mod 4)
- No triple found for n < 10²² (OEIS A060355)
- abc conjecture implies only finitely many triples
- Chan (2025): No triple where the middle number is a cube

Reference: https://erdosproblems.com/364
-/

import Mathlib

namespace Erdos364

open Nat

/-
## Powerful Numbers

A number n is powerful if every prime that divides n also has its square
divide n. This is equivalent to n being expressible as a²b³.
-/

/--
A natural number n is powerful if for every prime p, if p | n then p² | n.
Equivalently, in the prime factorization of n, every exponent is at least 2.
-/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-
## Basic Properties of Powerful Numbers
-/

/-- 1 is powerful (vacuously, no primes divide 1). -/
theorem one_powerful : Powerful 1 := by
  intro p hp hdiv
  exact absurd hdiv (Nat.Prime.not_dvd_one hp)

/-- 4 = 2² is powerful. -/
theorem four_powerful : Powerful 4 := by
  intro p hp hdiv
  -- p is prime and p | 4 = 2², so p = 2
  have hp2 : p = 2 := by
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := hp.two_le
    interval_cases p
    · rfl  -- p = 2
    · exact absurd hdiv (by decide : ¬(3 ∣ 4))  -- p = 3
    · exact absurd hp (by decide : ¬Nat.Prime 4)  -- p = 4
  subst hp2
  norm_num

/-- 8 = 2³ is powerful. -/
theorem eight_powerful : Powerful 8 := by
  intro p hp hdiv
  -- p is prime and p | 8 = 2³, so p = 2
  have hp2 : p = 2 := by
    have hle : p ≤ 8 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := hp.two_le
    interval_cases p
    · rfl  -- p = 2
    · exact absurd hdiv (by decide : ¬(3 ∣ 8))  -- p = 3
    · exact absurd hp (by decide : ¬Nat.Prime 4)  -- p = 4
    · exact absurd hdiv (by decide : ¬(5 ∣ 8))  -- p = 5
    · exact absurd hp (by decide : ¬Nat.Prime 6)  -- p = 6
    · exact absurd hdiv (by decide : ¬(7 ∣ 8))  -- p = 7
    · exact absurd hp (by decide : ¬Nat.Prime 8)  -- p = 8
  subst hp2
  norm_num

/-- 9 = 3² is powerful. -/
theorem nine_powerful : Powerful 9 := by
  intro p hp hdiv
  -- p is prime and p | 9 = 3², so p = 3
  have hp3 : p = 3 := by
    have hle : p ≤ 9 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := hp.two_le
    interval_cases p
    · exact absurd hdiv (by decide : ¬(2 ∣ 9))  -- p = 2
    · rfl  -- p = 3
    · exact absurd hp (by decide : ¬Nat.Prime 4)  -- p = 4
    · exact absurd hdiv (by decide : ¬(5 ∣ 9))  -- p = 5
    · exact absurd hp (by decide : ¬Nat.Prime 6)  -- p = 6
    · exact absurd hdiv (by decide : ¬(7 ∣ 9))  -- p = 7
    · exact absurd hp (by decide : ¬Nat.Prime 8)  -- p = 8
    · exact absurd hp (by decide : ¬Nat.Prime 9)  -- p = 9
  subst hp3
  norm_num

/-
## Pairs of Consecutive Powerful Numbers

Infinitely many pairs (n, n+1) of consecutive powerful numbers exist.
The Pell equation x² = 8y² + 1 provides solutions: (8,9), (288,289), etc.
-/

/-- 8 and 9 are consecutive powerful numbers. -/
theorem pair_8_9 : Powerful 8 ∧ Powerful 9 := ⟨eight_powerful, nine_powerful⟩

/--
There exist infinitely many pairs of consecutive powerful numbers.
This follows from the Pell equation x² = 8y² + 1, which has infinitely
many solutions. Each solution (x, y) gives the pair (8y², x²).

Observed by Mahler when Erdős asked the question.
-/
axiom infinitely_many_consecutive_pairs :
  {n : ℕ | Powerful n ∧ Powerful (n + 1)}.Infinite

/-
## No Quadruple of Consecutive Powerful Numbers

A number ≡ 2 (mod 4) cannot be powerful: 2 divides it but 4 does not.
Among any four consecutive integers, exactly one is ≡ 2 (mod 4).
-/

/-- A number congruent to 2 mod 4 is not powerful. -/
theorem not_powerful_of_two_mod_four {n : ℕ} (h : n % 4 = 2) : ¬Powerful n := by
  intro hpow
  have h2 : 2 ∣ n := by omega
  have h4 : 4 ∣ n := hpow 2 Nat.prime_two h2
  have : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  omega

/--
There is no quadruple of consecutive powerful numbers.
Among n, n+1, n+2, n+3, one must be ≡ 2 (mod 4), which cannot be powerful.
-/
theorem no_consecutive_quadruple :
    ¬∃ n : ℕ, Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) ∧ Powerful (n + 3) := by
  intro ⟨n, hn, hn1, hn2, hn3⟩
  have h : n % 4 = 2 ∨ (n + 1) % 4 = 2 ∨ (n + 2) % 4 = 2 ∨ (n + 3) % 4 = 2 := by omega
  rcases h with h | h | h | h
  · exact not_powerful_of_two_mod_four h hn
  · exact not_powerful_of_two_mod_four h hn1
  · exact not_powerful_of_two_mod_four h hn2
  · exact not_powerful_of_two_mod_four h hn3

/-
## The Main Conjecture (OPEN)

Erdős conjectured there is no triple of consecutive powerful numbers.
This remains open, though no triple has been found for n < 10²².
-/

/--
Erdős's conjecture: There is no triple of consecutive powerful numbers.

This is OPEN. Computational searches have verified no triple exists
for n < 10²² (OEIS A060355). The abc conjecture would imply only
finitely many such triples exist.

Reference: Erdős, P., "Problems and results on number theoretic properties
of consecutive integers", Proc. Manitoba Conf. (1976), 25-44.
-/
axiom no_consecutive_triple :
    ¬∃ n : ℕ, Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2)

/-
## Stronger Conjecture

Erdős also conjectured a quantitative version: gaps between powerful
numbers grow polynomially.
-/

/--
Erdős's stronger conjecture: If nₖ is the k-th powerful number, then
the gap nₖ₊₂ - nₖ grows like nₖᶜ for some constant c > 0.

This implies no consecutive triple exists, but is much stronger.
-/
axiom gap_conjecture :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ,
      (Nat.nth Powerful (k + 2) - Nat.nth Powerful k : ℝ) >
        (Nat.nth Powerful k : ℝ) ^ c

/-
## Partial Results
-/

/--
Chan (2025): There is no triple n-1, n, n+1 of consecutive powerful
numbers where n is a perfect cube.

Reference: Chan, Tsz Ho, "A note on three consecutive powerful numbers",
Integers (2025), Paper No. A7.
-/
axiom chan_cube_result :
    ¬∃ n : ℕ, (∃ m : ℕ, n = m ^ 3) ∧
      Powerful (n - 1) ∧ Powerful n ∧ Powerful (n + 1)

end Erdos364
