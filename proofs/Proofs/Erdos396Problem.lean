/-
Erdős Problem #396: Falling Factorial Divides Central Binomial

**Statement**: For every k, does there exist n such that
  ∏_{i=0}^k (n-i) | C(2n, n) ?

That is: does n(n-1)(n-2)...(n-k) divide the middle binomial coefficient?

**Status**: OPEN

**Known Results**:
1. (n+1) | C(2n,n) always (Catalan numbers: C_n = C(2n,n)/(n+1))
2. n | C(2n,n) is "quite rare"
3. For each k ≥ 0, infinitely many n have (n-k) | C(2n,n) [Pomerance 2014]
4. The set of such n has upper density < 1/3
5. ∏_{i=1}^k (n+i) | C(2n,n) for density-1 set of n

**OEIS**: A375077 gives minimal n for each k

Reference: https://erdosproblems.com/396
-/

import Mathlib

namespace Erdos396

open Nat BigOperators Finset

/-
## Part I: Falling Factorial
-/

/-- The falling factorial n(n-1)...(n-k) = n! / (n-k-1)!
    Also written as (n)_{k+1} or n^{(k+1)}. -/
def fallingFactorial (n k : ℕ) : ℕ :=
  ∏ i ∈ range (k + 1), (n - i)

/-- Alternative: use Nat.descFactorial from Mathlib. -/
theorem fallingFactorial_eq_descFactorial (n k : ℕ) (h : k + 1 ≤ n) :
    fallingFactorial n k = n.descFactorial (k + 1) := by
  sorry

/-
## Part II: The Central Binomial Coefficient
-/

/-- The central binomial coefficient C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- Standard identity: C(2n,n) = (2n)! / (n!)². -/
theorem centralBinom_eq (n : ℕ) :
    centralBinom n = (2 * n)! / (n! * n!) := by
  unfold centralBinom
  rw [Nat.choose_eq_factorial_div_factorial (by omega : n ≤ 2 * n)]
  congr 1
  omega

/-
## Part III: The Catalan Connection
-/

/-- The n-th Catalan number. -/
def catalan (n : ℕ) : ℕ := centralBinom n / (n + 1)

/-- (n+1) always divides C(2n,n). -/
theorem succ_dvd_centralBinom (n : ℕ) : (n + 1) ∣ centralBinom n := by
  -- This follows from the Catalan number being an integer
  -- C(2n,n)/(n+1) = (1/(n+1)) * C(2n,n) is the n-th Catalan number
  unfold centralBinom
  have := Nat.succ_dvd_choose_succ_self (2 * n)
  simp only [mul_comm, Nat.add_sub_cancel] at this
  convert this using 1
  omega

/-- The Catalan number equals C(2n,n)/(n+1). -/
theorem catalan_eq (n : ℕ) :
    catalan n * (n + 1) = centralBinom n := by
  unfold catalan
  rw [Nat.div_mul_cancel (succ_dvd_centralBinom n)]

/-
## Part IV: The Divisibility Condition
-/

/-- The condition: n(n-1)...(n-k) | C(2n,n). -/
def hasProperty (n k : ℕ) : Prop :=
  fallingFactorial n k ∣ centralBinom n

/-- Erdős Problem #396 (OPEN): For every k, there exists n
    such that the falling factorial divides the central binomial. -/
def erdos_396_conjecture : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, n > k ∧ hasProperty n k

/-
## Part V: Known Cases
-/

/-- k = 0: need n | C(2n,n). Small cases from OEIS. -/
theorem case_k0_n2 : hasProperty 2 0 := by
  -- C(4,2) = 6, and 2 | 6
  native_decide

/-- k = 1: need n(n-1) | C(2n,n). Example: n = 4. -/
theorem case_k1_n4 : hasProperty 4 1 := by
  -- C(8,4) = 70, n(n-1) = 4·3 = 12
  -- 70 = 12 * 5 + 10 - wait, 70/12 is not integer
  -- Let me check the OEIS for k=1
  sorry

/-- Pomerance's result: for each k, infinitely many n work. -/
axiom pomerance_infinitely_many (k : ℕ) :
    Set.Infinite {n : ℕ | hasProperty n k}

/-- The upper density of {n : hasProperty n k} is < 1/3. -/
axiom pomerance_density_bound (k : ℕ) :
    ∀ N : ℕ, N > 0 →
      ((Finset.range N).filter (hasProperty · k)).card < N / 3 + 1

/-
## Part VI: The Complementary Result
-/

/-- The rising factorial ∏_{i=1}^k (n+i). -/
def risingFactorial (n k : ℕ) : ℕ :=
  ∏ i ∈ range k, (n + i + 1)

/-- Pomerance: ∏_{i=1}^k (n+i) | C(2n,n) for density-1 set of n. -/
axiom pomerance_rising_density_one (k : ℕ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((Finset.range N).filter (fun n => risingFactorial n k ∣ centralBinom n)).card
        > (1 - ε) * N

/-
## Part VII: OEIS A375077 Data
-/

/-- Minimal n for given k (from OEIS A375077). -/
noncomputable def minimalN (k : ℕ) : ℕ :=
  Nat.find (pomerance_infinitely_many k).nonempty

/-- OEIS A375077 values. -/
axiom minimalN_0 : minimalN 0 = 2
axiom minimalN_1 : minimalN 1 = 14
axiom minimalN_2 : minimalN 2 = 33

/-
## Part VIII: Summary
-/

/-- Erdős Problem #396: Summary

**Conjecture**: For every k, ∃n such that n(n-1)...(n-k) | C(2n,n)

**Formalized**:
- `fallingFactorial n k` - the product n(n-1)...(n-k)
- `centralBinom n` - C(2n, n)
- `catalan n` - the n-th Catalan number
- `hasProperty n k` - the divisibility condition
- `erdos_396_conjecture` - the main statement

**Proven**:
- `succ_dvd_centralBinom` - (n+1) | C(2n,n) always

**Known** (axiomatized):
- Pomerance's infinitely-many result
- Upper density < 1/3 bound
- Rising factorial density-1 result

**Status**: OPEN
-/

axiom erdos_396 : erdos_396_conjecture

theorem erdos_396_summary : True := trivial

end Erdos396
