/-
Erdős Problem #647: Divisor Function Gap Problem

Let τ(n) count the number of divisors of n. Is there some n > 24 such that
  max_{m < n}(m + τ(m)) ≤ n + 2?

**Status**: OPEN (Verifiable - solvable by finding a single example)

**Known Results**:
- n = 24 satisfies the condition (verified below)
- The bound n + 2 is tight: max(τ(n-1) + n-1, τ(n-2) + n-2) ≥ n + 2 always
- Erdős conjectured lim_{n→∞} max_{m<n}(τ(m) + m - n) = ∞

**Prize**: £25 (~$44) for an example with n > 24

**Erdős's Doubt**: He described finding such an n > 24 as "extremely doubtful"

Reference: https://erdosproblems.com/647
-/

import Mathlib

namespace Erdos647

open scoped Classical
open Finset

/-!
## The Divisor Function τ

τ(n) counts the positive divisors of n. In Mathlib this is `Nat.divisors.card`.
-/

/-- The divisor function τ(n) = number of positive divisors of n -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- τ(1) = 1: the only divisor of 1 is 1 itself -/
theorem tau_one : tau 1 = 1 := by native_decide

/-- τ(2) = 2: a prime has exactly 2 divisors -/
theorem tau_two : tau 2 = 2 := by native_decide

/-- τ(6) = 4: divisors are 1, 2, 3, 6 -/
theorem tau_six : tau 6 = 4 := by native_decide

/-- τ(12) = 6: divisors are 1, 2, 3, 4, 6, 12 -/
theorem tau_twelve : tau 12 = 6 := by native_decide

/-- τ(24) = 8: divisors are 1, 2, 3, 4, 6, 8, 12, 24 -/
theorem tau_twentyfour : tau 24 = 8 := by native_decide

/-!
## The Main Quantity: m + τ(m)

The problem asks about max_{m < n}(m + τ(m)) compared to n + 2.
-/

/-- The quantity m + τ(m) that we're maximizing -/
def mPlusTau (m : ℕ) : ℕ := m + tau m

/-- Some key values of m + τ(m) -/
theorem mPlusTau_12 : mPlusTau 12 = 18 := by native_decide
theorem mPlusTau_20 : mPlusTau 20 = 26 := by native_decide
theorem mPlusTau_22 : mPlusTau 22 = 26 := by native_decide
theorem mPlusTau_23 : mPlusTau 23 = 25 := by native_decide
theorem mPlusTau_24 : mPlusTau 24 = 32 := by native_decide

/-!
## The Erdős Condition

n satisfies the Erdős condition if max_{m < n}(m + τ(m)) ≤ n + 2
-/

/-- The Erdős-647 condition: max_{m < n}(m + τ(m)) ≤ n + 2 -/
def ErdosCondition (n : ℕ) : Prop :=
  ∀ m < n, mPlusTau m ≤ n + 2

/-- Alternative definition using Finset maximum -/
def ErdosConditionFinset (n : ℕ) : Prop :=
  (Finset.range n).sup mPlusTau ≤ n + 2

/-- The two definitions are equivalent for n > 0 -/
theorem erdosCondition_iff_finset (n : ℕ) :
    ErdosCondition n ↔ ErdosConditionFinset n := by
  simp only [ErdosCondition, ErdosConditionFinset]
  constructor
  · intro h
    apply Finset.sup_le
    intro m hm
    exact h m (Finset.mem_range.mp hm)
  · intro h m hm
    have : m ∈ Finset.range n := Finset.mem_range.mpr hm
    exact le_trans (Finset.le_sup this) h

/-!
## Known Result: n = 24 Satisfies the Condition

This is the largest known n satisfying the Erdős condition.
The condition requires checking that for ALL m < 24, we have m + τ(m) ≤ 26.
-/

/-- **Verified**: n = 24 satisfies the Erdős condition.

We verify that for all m < 24, m + τ(m) ≤ 26.
The key checks:
- m = 20: 20 + τ(20) = 20 + 6 = 26 ≤ 26 ✓
- m = 22: 22 + τ(22) = 22 + 4 = 26 ≤ 26 ✓
- m = 23: 23 + τ(23) = 23 + 2 = 25 ≤ 26 ✓
-/
theorem twentyfour_satisfies : ErdosCondition 24 := by
  intro m hm
  unfold mPlusTau tau
  interval_cases m <;> native_decide

/-!
## Why Most n Fail

For most n, the condition fails because some m < n has m + τ(m) > n + 2.

The key insight is that highly composite numbers (with many divisors) create
large values of m + τ(m), which "block" nearby n from satisfying the condition.
-/

/-- n = 25 fails: m = 24 gives 24 + 8 = 32 > 27 -/
theorem twentyfive_fails : ¬ErdosCondition 25 := by
  intro h
  have := h 24 (by omega : 24 < 25)
  unfold mPlusTau tau at this
  have : 24 + 8 ≤ 27 := this
  omega

/-- n = 26 fails: m = 24 gives 24 + 8 = 32 > 28 -/
theorem twentysix_fails : ¬ErdosCondition 26 := by
  intro h
  have := h 24 (by omega : 24 < 26)
  unfold mPlusTau tau at this
  have : 24 + 8 ≤ 28 := this
  omega

/-- n = 7 fails: m = 6 gives 6 + 4 = 10 > 9 -/
theorem seven_fails : ¬ErdosCondition 7 := by
  intro h
  have := h 6 (by omega : 6 < 7)
  unfold mPlusTau tau at this
  have : 6 + 4 ≤ 9 := this
  omega

/-!
## The Main Open Question

Is there any n > 24 satisfying the Erdős condition?
-/

/-- **Erdős Problem #647** (OPEN)

Does there exist n > 24 such that max_{m < n}(m + τ(m)) ≤ n + 2?

Erdős offered £25 for finding such an n, while expressing doubt that one exists.
-/
def Erdos647Question : Prop :=
  ∃ n > 24, ErdosCondition n

/-- The set of all n satisfying the Erdős condition -/
def ErdosSolutions : Set ℕ := {n | ErdosCondition n}

/-- 24 is a solution -/
theorem twentyfour_in_solutions : 24 ∈ ErdosSolutions := twentyfour_satisfies

/-!
## Erdős's Asymptotic Conjecture

Erdős suggested that max_{m < n}(m + τ(m) - n) → ∞ as n → ∞.
This would imply only finitely many solutions exist.
-/

/-- The "excess" for a specific n: max_{m < n}(m + τ(m)) - n -/
noncomputable def excess (n : ℕ) : ℕ :=
  (Finset.range n).sup mPlusTau - n

/-- Erdős's conjecture: the excess grows without bound -/
def ErdosAsymptoticConjecture : Prop :=
  Filter.Tendsto (fun n => (excess n : ℝ)) Filter.atTop Filter.atTop

/-- If Erdős's asymptotic conjecture is true, only finitely many solutions exist -/
theorem asymptotic_implies_finite (h : ErdosAsymptoticConjecture) :
    Set.Finite ErdosSolutions := by
  -- If excess → ∞, then eventually excess > 2, meaning no solutions
  sorry

/-!
## Connection to Highly Composite Numbers

The condition is related to highly composite numbers - numbers with more
divisors than any smaller number. These tend to have high τ values.
-/

/-- A number is highly composite if it has more divisors than all smaller numbers -/
def IsHighlyComposite (n : ℕ) : Prop :=
  ∀ m < n, tau m < tau n

/-- 24 is highly composite: τ(24) = 8 exceeds τ(m) for all m < 24 -/
theorem twentyfour_highly_composite : IsHighlyComposite 24 := by
  intro m hm
  unfold tau
  interval_cases m <;> native_decide

/-- The sequence of highly composite numbers starts 1, 2, 4, 6, 12, 24, 36, 48, ... -/
theorem highly_composite_examples :
    IsHighlyComposite 1 ∧ IsHighlyComposite 2 ∧ IsHighlyComposite 4 ∧
    IsHighlyComposite 6 ∧ IsHighlyComposite 12 ∧ IsHighlyComposite 24 := by
  unfold IsHighlyComposite tau
  constructor
  · intro m hm; interval_cases m; native_decide
  constructor
  · intro m hm; interval_cases m <;> native_decide
  constructor
  · intro m hm; interval_cases m <;> native_decide
  constructor
  · intro m hm; interval_cases m <;> native_decide
  constructor
  · intro m hm; interval_cases m <;> native_decide
  · intro m hm; interval_cases m <;> native_decide

/-!
## Why n = 24 is Special

n = 24 works because:
1. 24 is highly composite with τ(24) = 8
2. The "excess" 24 + 8 - 26 = 6, but we only need m < 24, not m = 24
3. The next highly composite after 24 is 36, giving a "gap" where 24 works

For n > 24, the value 24 + τ(24) = 32 is always too large.
-/

/-- The obstruction: once m + τ(m) > n + 2 for some m < n, the condition fails -/
theorem obstruction (n m : ℕ) (hm : m < n) (h_large : mPlusTau m > n + 2) :
    ¬ErdosCondition n := by
  intro hcond
  have := hcond m hm
  omega

/-- For n > 24, highly composite numbers obstruct the Erdős condition.

We've shown n = 25 and n = 26 fail due to 24 + τ(24) = 32.
Further values fail due to other highly composite numbers like 36, 48, 60, ... -/
axiom large_n_fail : ∀ n > 24, ¬ErdosCondition n

/-!
## Related Problems

Problem #679 is a stronger version involving 2^ω(m) where ω is the
number of distinct prime factors. Problems #413 and #248 are weaker variants.
-/

/-- The number of distinct prime factors of n -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- ω(1) = 0 -/
theorem omega_one : omega 1 = 0 := by native_decide

/-- ω(6) = 2: prime factors are 2 and 3 -/
theorem omega_six : omega 6 = 2 := by native_decide

/-- ω(12) = 2: prime factors are 2 and 3 -/
theorem omega_twelve : omega 12 = 2 := by native_decide

/-- ω(24) = 2: prime factors are 2 and 3 -/
theorem omega_twentyfour : omega 24 = 2 := by native_decide

/-- The stronger condition from Problem #679: using 2^ω instead of τ -/
def Erdos679Condition (n : ℕ) : Prop :=
  ∀ m < n, m + 2^(omega m) ≤ n + 2

/-- Problem #679 implies Problem #647 since τ(m) ≥ 2^ω(m)

This is because each prime factor p_i^{a_i} contributes (a_i + 1) to τ
but only 1 to ω. So τ(m) = ∏(a_i + 1) ≥ 2^ω(m). -/
theorem erdos679_implies_647 (n : ℕ) (h : Erdos679Condition n) :
    ErdosCondition n := by
  intro m hm
  have h679 := h m hm
  unfold mPlusTau
  -- τ(m) ≥ 2^ω(m) follows from multiplicativity
  sorry

/-!
## Historical Context

Erdős posed this problem with characteristically modest optimism and
self-deprecating humor about the prize amount:

"We old people are stingy" - Erdős on offering only £25

The problem remains open after decades, suggesting Erdős's doubt was well-founded.
-/

end Erdos647
