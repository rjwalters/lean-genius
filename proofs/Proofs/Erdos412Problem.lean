/-
  Erdős Problem #412: Iterated Sum of Divisors Convergence

  Source: https://erdosproblems.com/412
  Status: OPEN

  Statement:
  Let σ₁(n) = σ(n), the sum of divisors function, and σₖ(n) = σ(σₖ₋₁(n)).
  Is it true that, for every m,n ≥ 2, there exist some i,j such that σᵢ(m) = σⱼ(n)?

  In other words: Do all iterated sum-of-divisors sequences eventually merge
  into a single common sequence?

  Historical Context:
  This conjecture was communicated to Erdős by van Wijngaarden in the 1950s.
  Selfridge provided numerical evidence suggesting the answer is NO, but
  Erdős and Graham wrote "it seems unlikely that anything can be proved
  about this in the near future."

  Related Problems: #413, #414

  References:
  [Er79d] Erdős, "Some unconventional problems in number theory" (1979)
  [ErGr80] Erdős & Graham, "Old and New Problems and Results in
           Combinatorial Number Theory" (1980)

  Tags: number-theory, sum-of-divisors, iteration, convergence
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

namespace Erdos412

open Nat

/-! ## Part I: The Sum of Divisors Function -/

/-- The sum of divisors function σ(n) = Σ_{d | n} d.
    For example: σ(6) = 1 + 2 + 3 + 6 = 12.
    We use `Nat.divisors` and explicit sums. -/
def sigma (n : ℕ) : ℕ := (n.divisors).sum id

/-- σ(1) = 1: the only divisor of 1 is 1 itself. -/
theorem sigma_one : sigma 1 = 1 := by native_decide

/-- Example: σ(2) = 3. The divisors of 2 are 1, 2. -/
example : sigma 2 = 3 := by native_decide

/-- Example: σ(6) = 12. The divisors of 6 are 1, 2, 3, 6. -/
example : sigma 6 = 12 := by native_decide

/-- Example: σ(12) = 28. The divisors of 12 are 1, 2, 3, 4, 6, 12. -/
example : sigma 12 = 28 := by native_decide

/-- Example: σ(28) = 56. -/
example : sigma 28 = 56 := by native_decide

/-! ## Part II: Iterated Sum of Divisors -/

/-- The k-th iterate of the sum of divisors function.
    σ₀(n) = n
    σₖ(n) = σ(σₖ₋₁(n)) -/
def iterSigma (k : ℕ) (n : ℕ) : ℕ := sigma^[k] n

/-- The 0-th iterate is the identity. -/
theorem iterSigma_zero (n : ℕ) : iterSigma 0 n = n := rfl

/-- The k+1-th iterate applies σ to the k-th iterate. -/
theorem iterSigma_succ (k n : ℕ) : iterSigma (k + 1) n = sigma (iterSigma k n) := by
  simp only [iterSigma, Function.iterate_succ_apply']

/-- Example: Starting from 2, we get 2 → 3 → 4 → 7 → 8 → 15 → ... -/
example : iterSigma 0 2 = 2 := rfl
example : iterSigma 1 2 = 3 := by native_decide
example : iterSigma 2 2 = 4 := by native_decide
example : iterSigma 3 2 = 7 := by native_decide
example : iterSigma 4 2 = 8 := by native_decide
example : iterSigma 5 2 = 15 := by native_decide

/-- Example: Starting from 3, we get 3 → 4 → 7 → 8 → 15 → ... -/
example : iterSigma 0 3 = 3 := rfl
example : iterSigma 1 3 = 4 := by native_decide
example : iterSigma 2 3 = 7 := by native_decide
example : iterSigma 3 3 = 8 := by native_decide
example : iterSigma 4 3 = 15 := by native_decide

/-- Note: σ₁(2) = 3 and σ₀(3) = 3, so sequences from 2 and 3 merge after 1 step! -/
theorem merge_2_3 : iterSigma 1 2 = iterSigma 0 3 := by native_decide

/-! ## Part III: The Conjecture -/

/-- Two numbers m and n are σ-equivalent if their iterated sequences eventually meet.
    That is, there exist i, j such that σᵢ(m) = σⱼ(n). -/
def SigmaEquivalent (m n : ℕ) : Prop :=
  ∃ i j : ℕ, iterSigma i m = iterSigma j n

/-- The conjecture: All integers ≥ 2 are σ-equivalent.
    This would mean there is essentially one "universal" sequence that
    all iterated sum-of-divisors sequences eventually join. -/
def Erdos412Conjecture : Prop :=
  ∀ m n : ℕ, m ≥ 2 → n ≥ 2 → SigmaEquivalent m n

/-- **Erdős Problem #412**: Is the conjecture true?

    STATUS: OPEN

    Evidence suggests the answer may be NO (Selfridge), but nothing
    has been proven either way. -/
axiom erdos_412_status : True  -- Placeholder indicating open status

/-! ## Part IV: Verified Examples -/

/-- 2 and 3 are σ-equivalent (they merge after 1 and 0 steps respectively). -/
theorem equiv_2_3 : SigmaEquivalent 2 3 := ⟨1, 0, by native_decide⟩

/-- 2 and 4 are σ-equivalent: iterSigma 2 2 = 4 = iterSigma 0 4. -/
theorem equiv_2_4 : SigmaEquivalent 2 4 := ⟨2, 0, by native_decide⟩

/-- 5 and 6 are σ-equivalent: σ(5) = 6. -/
theorem equiv_5_6 : SigmaEquivalent 5 6 := ⟨1, 0, by native_decide⟩

/-- 7 and 8 are σ-equivalent: σ(7) = 8. -/
theorem equiv_7_8 : SigmaEquivalent 7 8 := ⟨1, 0, by native_decide⟩

/-! ## Part V: The Aliquot Sequence Connection -/

/-- The aliquot sum s(n) = σ(n) - n is the sum of proper divisors.
    The aliquot sequence n → s(n) → s(s(n)) → ... is related but different.

    Perfect numbers satisfy s(n) = n (they are fixed points of s).
    Amicable pairs satisfy s(m) = n and s(n) = m.

    Problem #412 is about σ (including n) rather than s (excluding n). -/
def aliquotSum (n : ℕ) : ℕ := sigma n - n

/-- Example: s(6) = 12 - 6 = 6 (6 is perfect). -/
example : aliquotSum 6 = 6 := by native_decide

/-- Example: s(28) = 56 - 28 = 28 (28 is perfect). -/
example : aliquotSum 28 = 28 := by native_decide

/-! ## Part VI: Growth of Iterated Sigma -/

/-- For n ≥ 2, σ(n) ≥ n + 1 (since 1 and n are always divisors).
    This means the iterated sequence is non-decreasing for n ≥ 2. -/
theorem sigma_ge_succ (n : ℕ) (hn : n ≥ 2) : sigma n ≥ n + 1 := by
  unfold sigma
  have hpos : n ≠ 0 := by omega
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hpos
  have hn_mem : n ∈ n.divisors := Nat.mem_divisors_self n hpos
  have hne : (1 : ℕ) ≠ n := by omega
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  calc (n.divisors).sum id
      ≥ ({1, n} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset hsub
    _ = 1 + n := by simp [Finset.sum_pair hne]
    _ = n + 1 := add_comm 1 n

/-- For n ≥ 2, σ(n) > n (strictly increasing). -/
theorem sigma_gt (n : ℕ) (hn : n ≥ 2) : sigma n > n := by
  have h := sigma_ge_succ n hn
  omega

/-! ## Part VII: Why This Is Hard -/

/-- The difficulty of Problem #412:

    1. The sequences grow rapidly (σ(n) ≥ n + 1)
    2. There's no obvious pattern to when/if sequences merge
    3. Selfridge's numerical evidence suggests some sequences might never merge
    4. But proving non-convergence requires understanding all possible futures

    If false: Need to find m, n such that no iterate of σ starting from m
    ever equals any iterate starting from n. This requires proving infinitely
    many inequalities.

    If true: Need to show all sequences eventually hit a common value.
    The growth rate makes this seem unlikely. -/
theorem difficulty_note : True := trivial

/-! ## Part VIII: Related Concepts -/

/-- A number n is σ-periodic if σₖ(n) = n for some k ≥ 1.
    Perfect numbers (σ(n) = 2n) are related but not σ-periodic. -/
def IsSigmaPeriodic (n : ℕ) : Prop :=
  ∃ k : ℕ, k ≥ 1 ∧ iterSigma k n = n

/-- For n ≥ 2, σ(n) > n, so no such n can be σ-periodic after 1 step. -/
theorem no_sigma_periodic_step1 (n : ℕ) (hn : n ≥ 2) : iterSigma 1 n > n := by
  simp only [iterSigma, Function.iterate_one]
  exact sigma_gt n hn

/-! ## Part IX: Summary -/

/-- **Summary of Erdős Problem #412**:

    **Question**: For all m, n ≥ 2, do there exist i, j such that σᵢ(m) = σⱼ(n)?

    **Status**: OPEN

    **What we formalize**:
    1. The sum of divisors function σ
    2. Iterated σ: σₖ(n) = σ(σₖ₋₁(n))
    3. σ-equivalence: sequences eventually meeting
    4. The main conjecture
    5. Verified examples of equivalence for small numbers
    6. Growth properties: σ(n) > n for n ≥ 2

    **Key insight**: The conjecture asks if there's essentially one
    "attractor" sequence that all iterated σ-sequences eventually join.
    Numerical evidence (Selfridge) suggests this may be false, but
    nothing has been proven.

    **Difficulty**: Sequences grow without bound (σ(n) > n), making it
    hard to track long-term behavior. Proving convergence or divergence
    requires understanding infinitely many iterates. -/
theorem erdos_412_summary : True := trivial

end Erdos412

/-!
## Final Notes

This file formalizes Erdős Problem #412 on iterated sum-of-divisors convergence.

**Status**: OPEN

**The Conjecture**: All integers m, n ≥ 2 have their iterated σ-sequences
eventually meet at a common value.

**Evidence**: Selfridge's numerical evidence suggests the answer is NO,
but this has not been proven.

**What we prove**:
- Basic properties of σ (sum of divisors)
- Growth: σ(n) > n for n ≥ 2
- Examples of σ-equivalence for small numbers

**Open**: The main conjecture remains unresolved.
-/
