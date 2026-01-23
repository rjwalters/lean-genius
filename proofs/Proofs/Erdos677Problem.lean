/-
Erdős Problem #677: LCM Equality for Consecutive Integer Intervals

**Statement**: Let M(n,k) = lcm{n+1, ..., n+k}. Is it true that for all m ≥ n+k,
  M(n,k) ≠ M(m,k)?

**Status**: OPEN

**Known Results**:
- Thue-Siegel theorem implies finitely many solutions for fixed k
- Known solutions: M(4,3) = M(13,2) and M(3,4) = M(19,2)
- Stronger conjecture: products cannot share same prime factors (except finite exceptions)

**General Question**: How many solutions does M(n,k) = M(m,l) have when m ≥ n+k and l > 1?
- Erdős expects very few
- None when l ≥ k (conjectured)

**References**:
- [Er79] Erdős, P. - Some problems in number theory
- [Er79d] Erdős, P. - Stronger conjecture about prime factors
- [ErGr80] Erdős-Graham - Old and new problems in combinatorial number theory
- [Gu04] Guy, R. - Unsolved Problems in Number Theory (B35)

See also: #678 (LCM comparison), #686, #850

Reference: https://erdosproblems.com/677
-/

import Mathlib

open Finset Nat

namespace Erdos677

/-!
## Part I: Core Definitions
-/

/-- The LCM of consecutive integers from n+1 to n+k.
    M(n,k) = lcm{n+1, n+2, ..., n+k} -/
def M (n k : ℕ) : ℕ :=
  (Finset.range k).fold lcm 1 (fun i => n + 1 + i)

/-- Alternative notation for M(n,k) -/
notation "M(" n "," k ")" => M n k

/-!
## Part II: Basic Properties
-/

/-- M(n, 0) = 1 (empty interval) -/
theorem M_zero (n : ℕ) : M n 0 = 1 := by
  unfold M
  simp [Finset.fold_empty]

/-- M(n, 1) = n + 1 (single element) -/
theorem M_one (n : ℕ) : M n 1 = n + 1 := by
  unfold M
  simp [Finset.range_one, Finset.fold_singleton]

/-- Each element divides M(n,k) -/
theorem elem_dvd_M (n k i : ℕ) (hi : i < k) : (n + 1 + i) ∣ M n k := by
  sorry

/-- M(n,k) divides M(n,k+1) (extending interval) -/
theorem M_dvd_succ (n k : ℕ) : M n k ∣ M n (k + 1) := by
  sorry

/-!
## Part III: The Main Conjecture
-/

/-- The main conjecture: for all m ≥ n+k, M(n,k) ≠ M(m,k)
    That is: two intervals of the same length, separated by at least the
    length of the first, cannot have the same LCM. -/
def mainConjecture : Prop :=
  ∀ n k m : ℕ, k ≥ 1 → m ≥ n + k → M n k ≠ M m k

/-- Weak version: for fixed k, only finitely many violations exist.
    This follows from Thue-Siegel theorem. -/
axiom thue_siegel_consequence (k : ℕ) (hk : k ≥ 1) :
  Set.Finite {p : ℕ × ℕ | p.2 ≥ p.1 + k ∧ M p.1 k = M p.2 k}

/-!
## Part IV: Known Examples of M(n,k) = M(m,l)
-/

/-- Compute M(4,3) = lcm{5, 6, 7} = 210 -/
theorem M_4_3 : M 4 3 = 210 := by native_decide

/-- Compute M(13,2) = lcm{14, 15} = 210 -/
theorem M_13_2 : M 13 2 = 210 := by native_decide

/-- Known solution 1: M(4,3) = M(13,2) = 210 -/
theorem known_solution_1 : M 4 3 = M 13 2 := by
  rw [M_4_3, M_13_2]

/-- Compute M(3,4) = lcm{4, 5, 6, 7} = 420 -/
theorem M_3_4 : M 3 4 = 420 := by native_decide

/-- Compute M(19,2) = lcm{20, 21} = 420 -/
theorem M_19_2 : M 19 2 = 420 := by native_decide

/-- Known solution 2: M(3,4) = M(19,2) = 420 -/
theorem known_solution_2 : M 3 4 = M 19 2 := by
  rw [M_3_4, M_19_2]

/-- The known solutions satisfy the constraint m ≥ n + k -/
theorem known_solutions_valid :
    (13 ≥ 4 + 3) ∧ (19 ≥ 3 + 4) := by norm_num

/-!
## Part V: The General Question M(n,k) = M(m,l)
-/

/-- General LCM equality: M(n,k) = M(m,l) with m ≥ n+k and l > 1 -/
def lcmEquality (n k m l : ℕ) : Prop :=
  k ≥ 1 ∧ l > 1 ∧ m ≥ n + k ∧ M n k = M m l

/-- The two known solutions -/
theorem known_solutions :
    lcmEquality 4 3 13 2 ∧ lcmEquality 3 4 19 2 := by
  constructor
  · constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · exact known_solution_1
  · constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · exact known_solution_2

/-- Erdős expects very few solutions -/
def erdos_conjecture_few_solutions : Prop :=
  Set.Finite {t : ℕ × ℕ × ℕ × ℕ | lcmEquality t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- Erdős expects NO solutions when l ≥ k -/
def erdos_conjecture_none_when_l_ge_k : Prop :=
  ∀ n k m l : ℕ, k ≥ 1 → l ≥ k → m ≥ n + k → M n k ≠ M m l

/-!
## Part VI: The Stronger Conjecture (Er79d)
-/

/-- The set of prime factors of n -/
def primeFactors (n : ℕ) : Finset ℕ :=
  (n.factorization.support)

/-- The product of an interval -/
def intervalProduct (n k : ℕ) : ℕ :=
  (Finset.range k).prod (fun i => n + 1 + i)

/-- Prime factors of interval product -/
def intervalPrimeFactors (n k : ℕ) : Finset ℕ :=
  primeFactors (intervalProduct n k)

/-- Erdős's stronger conjecture: the intervals cannot even share the
    same set of prime factors (except finitely many exceptions) -/
def stronger_conjecture : Prop :=
  ∃ N : ℕ, ∀ n k m : ℕ, k > 2 → m ≥ n + k → n + k > N →
    intervalPrimeFactors n k ≠ intervalPrimeFactors m k

/-!
## Part VII: Computational Checks for the Main Conjecture
-/

/-- Check that M(n,k) ≠ M(m,k) for small values.
    The conjecture predicts this should always hold. -/
theorem main_conjecture_check_k_2 :
    ∀ n m : ℕ, n < 100 → m < 200 → m ≥ n + 2 → M n 2 ≠ M m 2 := by
  sorry -- Would require extensive computation

/-- Check that no violations exist for k=3 in small range -/
theorem main_conjecture_check_k_3 :
    ∀ n m : ℕ, n < 50 → m < 150 → m ≥ n + 3 → M n 3 ≠ M m 3 := by
  sorry

/-!
## Part VIII: Why the Problem is Hard
-/

/-- The LCM depends heavily on prime powers in the interval.
    Two different intervals can share the same LCM if they happen
    to contain the same highest prime powers. -/
example : intervalPrimeFactors 4 3 = intervalPrimeFactors 13 2 := by
  native_decide

/-- In both known solutions, the smaller l interval captures the
    key prime powers efficiently -/
theorem efficiency_observation :
    (M 4 3 = M 13 2 ∧ 3 > 2) ∧
    (M 3 4 = M 19 2 ∧ 4 > 2) := by
  constructor
  · constructor
    · exact known_solution_1
    · norm_num
  · constructor
    · exact known_solution_2
    · norm_num

/-!
## Part IX: Summary
-/

/-- Erdős #677 Summary:

**Main Question**: For m ≥ n+k, is M(n,k) ≠ M(m,k)?
**Status**: OPEN

**Known**:
- Finitely many counterexamples exist (Thue-Siegel)
- No counterexamples found (for same k)
- Two solutions with different k,l: M(4,3)=M(13,2), M(3,4)=M(19,2)

**Stronger Conjecture**: Products cannot share same prime factors
**Expected**: Very few solutions, none when l ≥ k

**Related**: #678 (LCM comparison), #686, #850 -/
theorem erdos_677_status : True := trivial

end Erdos677
