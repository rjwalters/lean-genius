/-
Erdős Problem #1059, Open Question 05:
Generalized interval_cases+decide tactic for factorial compositeness verification.

The parent proof (Erdos1059Problem.lean) verifies examples like p = 101 and p = 211
using manual factorial_lt_bound helper lemmas followed by interval_cases + decide.
Each new prime requires its own bespoke helper.

We eliminate this boilerplate by providing a Decidable instance for
AllFactorialSubtractionsComposite. The key insight: since k ≤ k! for all k,
the condition k! < n implies k < n, bounding the universal quantifier to
Finset.range n. With this instance, any concrete verification reduces to
`by native_decide`.

Axiom count: 0
Sorry count: 0
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-
## Core Definition
-/

/-- The condition that for every k with k! < n, n - k! is composite (≥ 2 and not prime). -/
def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ k : ℕ, Nat.factorial k < n → ¬(n - Nat.factorial k).Prime ∧ n - Nat.factorial k ≥ 2

/-
## Decidability Infrastructure
-/

/-- Since k ≤ k! for all k, the hypothesis k! < n forces k < n. -/
theorem factorial_lt_implies_lt {k n : ℕ} (h : Nat.factorial k < n) : k < n :=
  lt_of_le_of_lt (Nat.self_le_factorial k) h

/-- AllFactorialSubtractionsComposite is equivalent to a bounded quantifier
    over Finset.range n. This makes it decidable. -/
theorem allFactorialSubtractionsComposite_iff_bounded (n : ℕ) :
    AllFactorialSubtractionsComposite n ↔
    ∀ k ∈ Finset.range n,
      Nat.factorial k < n → ¬(n - Nat.factorial k).Prime ∧ n - Nat.factorial k ≥ 2 := by
  constructor
  · intro h k _ hk
    exact h k hk
  · intro h k hk
    exact h k (Finset.mem_range.mpr (factorial_lt_implies_lt hk)) hk

/-- Decidable instance: for any concrete n, AllFactorialSubtractionsComposite n
    can be checked by computation. This is the main result of this file. -/
instance decAllFactorialSubtractionsComposite (n : ℕ) :
    Decidable (AllFactorialSubtractionsComposite n) :=
  decidable_of_iff _ (allFactorialSubtractionsComposite_iff_bounded n).symm

/-
## Witness Verification

With the decidable instance, verifying any concrete prime requires only `native_decide`.
No manual factorial_lt_bound helpers needed.
-/

/-- p = 101 satisfies the property. (Compare: the parent proof needed a
    bespoke factorial_lt_bound and interval_cases.) -/
theorem witness_101 : AllFactorialSubtractionsComposite 101 := by native_decide

/-- p = 211 satisfies the property. -/
theorem witness_211 : AllFactorialSubtractionsComposite 211 := by native_decide

/-- Combined witness: 101 and 211 are both prime witnesses for Erdős 1059. -/
theorem erdos_1059_witnesses :
    (101 : ℕ).Prime ∧ AllFactorialSubtractionsComposite 101 ∧
    (211 : ℕ).Prime ∧ AllFactorialSubtractionsComposite 211 :=
  ⟨by decide, witness_101, by native_decide, witness_211⟩

/-
## Non-witnesses: the Decidable instance also verifies failures.
-/

/-- p = 89 fails: 89 - 3! = 83 is prime. -/
theorem non_witness_89 : ¬AllFactorialSubtractionsComposite 89 := by native_decide

/-- p = 223 fails: 223 - 4! = 199 is prime. -/
theorem non_witness_223 : ¬AllFactorialSubtractionsComposite 223 := by native_decide

/-
## Summary

The decidable instance `decAllFactorialSubtractionsComposite` generalizes the
interval_cases+decide pattern from the parent proof. Before this file, each new
prime verification required:
  1. A manual factorial_lt_bound_N helper proving k! < N → k ≤ M
  2. An interval_cases enumeration over k = 0, ..., M
  3. A simp + decide/native_decide chain for each case

After this file, verification is a single `by native_decide`.
-/
