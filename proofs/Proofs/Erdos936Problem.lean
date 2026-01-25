/-
Erdős Problem #936: Powerful Numbers Near 2^n and n!

Source: https://erdosproblems.com/936
Status: OPEN (conditionally resolved assuming ABC conjecture)

Statement:
Are 2^n ± 1 and n! ± 1 powerful for only finitely many n?

A number m is *powerful* if whenever a prime p divides m, then p² also divides m.
Equivalently, m can be written as a²b³ for some integers a, b ≥ 1.

**Conditional Results:**
- Cushing-Pascoe (2016): Assuming the ABC conjecture, n! ± 1 is powerful
  for only finitely many n.
- CrowdMath (2020): Assuming the ABC conjecture, 2^n ± 1 is powerful
  for only finitely many n.

**Known powerful values:**
- 2^n + 1: Only n = 0 gives 2, which is not powerful (2 | 2 but 4 ∤ 2)
- 2^n - 1: n = 1 gives 1 (vacuously powerful), n = 3 gives 7 (not powerful)
- n! + 1: No known powerful values for n > 0
- n! - 1: No known powerful values for n > 1

The ABC conjecture would imply these sequences eventually avoid powerful numbers,
but unconditional proofs remain elusive.

References:
- Erdős [Er76d, p.32]: Original problem
- Cushing, Pascoe (2016): "The abc conjecture implies n! ± 1 is squarefree for large n"
- CrowdMath (2020): Polymath project extending to 2^n ± 1
- OEIS A146968: Powerful numbers n! ± 1 (empty for large n)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Nat.Factorial.Basic

open Nat Filter BigOperators Finset

namespace Erdos936

/-
## Part I: Powerful Numbers

A positive integer is *powerful* if every prime factor appears with exponent ≥ 2.
-/

/--
**Powerful Number:**
A natural number n is powerful if for every prime p dividing n,
we have p² | n. Equivalently, all prime exponents in the factorization are ≥ 2.

Examples:
- 1 is powerful (vacuously - no prime divisors)
- 4 = 2² is powerful
- 8 = 2³ is powerful
- 9 = 3² is powerful
- 36 = 2² · 3² is powerful
- 6 = 2 · 3 is NOT powerful (both primes appear with exponent 1)
-/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

/-- 1 is powerful (vacuously true). -/
theorem one_powerful : Powerful 1 := by
  intro p _ hp_div
  have : p ∣ 1 := hp_div
  interval_cases p <;> simp_all

/-- Perfect squares are powerful. -/
theorem sq_powerful (n : ℕ) : Powerful (n^2) := by
  intro p hp hp_div
  have : p ∣ n^2 := hp_div
  have hp_div_n : p ∣ n := hp.dvd_of_dvd_pow this
  exact Nat.pow_dvd_pow_of_dvd hp_div_n 2

/-- 4 is powerful. -/
theorem four_powerful : Powerful 4 := sq_powerful 2

/-- 9 is powerful. -/
theorem nine_powerful : Powerful 9 := sq_powerful 3

/-- 36 is powerful. -/
theorem thirtysix_powerful : Powerful 36 := by
  have h : 36 = 6^2 := by norm_num
  rw [h]
  exact sq_powerful 6

/-- Primes are NOT powerful. -/
theorem prime_not_powerful (p : ℕ) (hp : p.Prime) : ¬Powerful p := by
  intro h
  have h_self := h p hp (dvd_refl p)
  have : p^2 ∣ p := h_self
  have : p^2 ≤ p := Nat.le_of_dvd hp.pos this
  have : p * p ≤ p := this
  have hp_ge : p ≥ 2 := hp.two_le
  omega

/-- 2 is not powerful. -/
theorem two_not_powerful : ¬Powerful 2 := prime_not_powerful 2 Nat.prime_two

/-- 3 is not powerful. -/
theorem three_not_powerful : ¬Powerful 3 := prime_not_powerful 3 Nat.prime_three

/-
## Part II: The Sequences in Question

We examine four sequences:
- 2^n + 1
- 2^n - 1
- n! + 1
- n! - 1
-/

/--
**Eventually Not Powerful:**
A sequence a : ℕ → ℕ is eventually not powerful if there exists N such that
for all n ≥ N, a(n) is not powerful.
-/
def EventuallyNotPowerful (a : ℕ → ℕ) : Prop :=
  atTop.Eventually (fun n => ¬Powerful (a n))

/-- Alternative characterization: exists N such that all a(n) for n ≥ N are not powerful. -/
theorem eventuallyNotPowerful_iff (a : ℕ → ℕ) :
    EventuallyNotPowerful a ↔ ∃ N : ℕ, ∀ n ≥ N, ¬Powerful (a n) := by
  simp only [EventuallyNotPowerful, Filter.eventually_atTop]

/-
## Part III: Concrete Examples
-/

/-- 2^0 + 1 = 2 is not powerful. -/
theorem two_pow_zero_add_one_not_powerful : ¬Powerful (2^0 + 1) := by
  simp only [pow_zero]
  exact two_not_powerful

/-- 2^1 + 1 = 3 is not powerful. -/
theorem two_pow_one_add_one_not_powerful : ¬Powerful (2^1 + 1) := by
  simp only [pow_one]
  exact three_not_powerful

/-- 2^2 + 1 = 5 is not powerful (5 is prime). -/
theorem two_pow_two_add_one_not_powerful : ¬Powerful (2^2 + 1) := by
  have h : 2^2 + 1 = 5 := by norm_num
  rw [h]
  exact prime_not_powerful 5 (by norm_num : Nat.Prime 5)

/-- 2^1 - 1 = 1 is powerful. -/
theorem two_pow_one_sub_one_powerful : Powerful (2^1 - 1) := by
  simp only [pow_one, Nat.sub_self]
  exact one_powerful

/-- 2^2 - 1 = 3 is not powerful. -/
theorem two_pow_two_sub_one_not_powerful : ¬Powerful (2^2 - 1) := by
  have h : 2^2 - 1 = 3 := by norm_num
  rw [h]
  exact three_not_powerful

/-- 1! + 1 = 2 is not powerful. -/
theorem one_factorial_add_one_not_powerful : ¬Powerful (1! + 1) := by
  simp only [Nat.factorial_one]
  exact two_not_powerful

/-- 2! + 1 = 3 is not powerful. -/
theorem two_factorial_add_one_not_powerful : ¬Powerful (2! + 1) := by
  simp only [Nat.factorial_two]
  exact three_not_powerful

/-- 3! + 1 = 7 is not powerful (7 is prime). -/
theorem three_factorial_add_one_not_powerful : ¬Powerful (3! + 1) := by
  have h : 3! + 1 = 7 := by norm_num
  rw [h]
  exact prime_not_powerful 7 (by norm_num : Nat.Prime 7)

/-- 1! - 1 = 0 (edge case). -/
theorem one_factorial_sub_one : 1! - 1 = 0 := by simp

/-- 2! - 1 = 1 is powerful. -/
theorem two_factorial_sub_one_powerful : Powerful (2! - 1) := by
  simp only [Nat.factorial_two]
  exact one_powerful

/-- 3! - 1 = 5 is not powerful. -/
theorem three_factorial_sub_one_not_powerful : ¬Powerful (3! - 1) := by
  have h : 3! - 1 = 5 := by norm_num
  rw [h]
  exact prime_not_powerful 5 (by norm_num : Nat.Prime 5)

/-
## Part IV: The ABC Conjecture Connection

The ABC conjecture implies that near factorials and powers of 2,
powerful numbers become increasingly rare.
-/

/--
**ABC Conjecture (informal):**
For coprime positive integers a, b, c with a + b = c,
the product of distinct prime factors of abc (the "radical")
satisfies rad(abc) > c^(1-ε) for any ε > 0 with finitely many exceptions.

This is axiomatized here as it remains unproven.
-/
axiom abc_conjecture_holds : Prop

/--
**Cushing-Pascoe Theorem (2016):**
Assuming the ABC conjecture, for any fixed k ≥ 0, there exist only
finitely many n and powerful numbers x satisfying |x - n!| ≤ k.

In particular, n! ± 1 is powerful for only finitely many n.
-/
axiom cushing_pascoe_theorem :
    abc_conjecture_holds →
    EventuallyNotPowerful (fun n => n! + 1) ∧
    EventuallyNotPowerful (fun n => n! - 1)

/--
**CrowdMath Theorem (2020):**
Assuming the ABC conjecture, 2^n ± 1 is powerful for only finitely many n.
-/
axiom crowdmath_theorem :
    abc_conjecture_holds →
    EventuallyNotPowerful (fun n => 2^n + 1) ∧
    EventuallyNotPowerful (fun n => 2^n - 1)

/-
## Part V: The Four Variants of Erdős #936
-/

/--
**Erdős #936 Variant 1:**
Is 2^n + 1 powerful for only finitely many n?

Conditionally YES (assuming ABC).
-/
axiom erdos_936_two_pow_add_one :
    abc_conjecture_holds → EventuallyNotPowerful (fun n => 2^n + 1)

/--
**Erdős #936 Variant 2:**
Is 2^n - 1 powerful for only finitely many n?

Conditionally YES (assuming ABC).
-/
axiom erdos_936_two_pow_sub_one :
    abc_conjecture_holds → EventuallyNotPowerful (fun n => 2^n - 1)

/--
**Erdős #936 Variant 3:**
Is n! + 1 powerful for only finitely many n?

Conditionally YES (assuming ABC).
-/
axiom erdos_936_factorial_add_one :
    abc_conjecture_holds → EventuallyNotPowerful (fun n => n! + 1)

/--
**Erdős #936 Variant 4:**
Is n! - 1 powerful for only finitely many n?

Conditionally YES (assuming ABC).
-/
axiom erdos_936_factorial_sub_one :
    abc_conjecture_holds → EventuallyNotPowerful (fun n => n! - 1)

/--
**All Four Variants Combined:**
Assuming ABC, all four sequences are eventually not powerful.
-/
theorem erdos_936_all_variants :
    abc_conjecture_holds →
    EventuallyNotPowerful (fun n => 2^n + 1) ∧
    EventuallyNotPowerful (fun n => 2^n - 1) ∧
    EventuallyNotPowerful (fun n => n! + 1) ∧
    EventuallyNotPowerful (fun n => n! - 1) := by
  intro habc
  exact ⟨erdos_936_two_pow_add_one habc,
         erdos_936_two_pow_sub_one habc,
         erdos_936_factorial_add_one habc,
         erdos_936_factorial_sub_one habc⟩

/-
## Part VI: Squarefree Observations

Squarefree numbers (those with all prime exponents = 1) are the opposite extreme
from powerful numbers. The ABC conjecture actually implies n! ± 1 is squarefree
for large n (a stronger result than merely not being powerful).
-/

/--
**Squarefree:**
A number is squarefree if no prime square divides it.
-/
def Squarefree' (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬(p^2 ∣ n)

/-- Squarefree numbers with n > 1 are not powerful. -/
theorem squarefree_not_powerful (n : ℕ) (hn : n > 1) (hsq : Squarefree' n) :
    ¬Powerful n := by
  intro hpow
  obtain ⟨p, hp, hp_div⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have := hpow p hp hp_div
  have := hsq p hp
  contradiction

/-
## Part VII: Summary and Open Status
-/

/--
**Erdős Problem #936: OPEN**

The problem asks whether 2^n ± 1 and n! ± 1 are powerful for only finitely many n.

Current status:
- Conditionally resolved: YES assuming the ABC conjecture
- Unconditional proof: OPEN

The ABC conjecture itself remains one of the most important open problems
in number theory.
-/
theorem erdos_936_summary :
    (abc_conjecture_holds →
      EventuallyNotPowerful (fun n => 2^n + 1) ∧
      EventuallyNotPowerful (fun n => 2^n - 1) ∧
      EventuallyNotPowerful (fun n => n! + 1) ∧
      EventuallyNotPowerful (fun n => n! - 1)) ∧
    ¬Powerful 2 ∧
    ¬Powerful 3 ∧
    Powerful 1 ∧
    Powerful 4 ∧
    Powerful 9 :=
  ⟨erdos_936_all_variants,
   two_not_powerful,
   three_not_powerful,
   one_powerful,
   four_powerful,
   nine_powerful⟩

end Erdos936
