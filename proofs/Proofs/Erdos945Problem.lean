/-
Erdős Problem #945: Consecutive Integers with Distinct Divisor Counts

Let F(x) be the maximal k such that there exist consecutive integers
n+1, ..., n+k ≤ x with τ(n+1), ..., τ(n+k) all distinct, where τ(m)
counts the divisors of m.

**Question** (OPEN): Is F(x) ≤ (log x)^{O(1)}?

Equivalently: Is there a constant C > 0 such that every interval
[x, x + (log x)^C] contains two integers with the same number of divisors?

**Known Bounds** (Erdős-Mirsky 1952):
- Lower: (log x)^{1/2} / log log x ≪ F(x)
- Upper: F(x) ≪ exp(O((log x)^{1/2} / log log x))

**Improvements**:
- Beker: F(x) ≪ exp(O((log x)^{1/3+o(1)}))
- Cramér's conjecture implies F(x) ≪ (log x)²

Reference: https://erdosproblems.com/945
-/

import Mathlib

namespace Erdos945

open Filter Real
open scoped Classical

/-!
## The Divisor Counting Function

τ(n) counts the number of positive divisors of n.
For example: τ(12) = 6 (divisors: 1, 2, 3, 4, 6, 12).
-/

/-- The divisor counting function τ(n) = number of positive divisors of n -/
abbrev τ (n : ℕ) : ℕ := n.divisors.card

/-!
## Concrete Examples

Small examples of τ values:
- τ(1) = 1
- τ(2) = 2 (prime)
- τ(4) = 3 (1, 2, 4)
- τ(6) = 4 (1, 2, 3, 6)
- τ(12) = 6 (highly composite)
-/

/-- τ(1) = 1 -/
theorem tau_1 : τ 1 = 1 := by native_decide

/-- τ(2) = 2 (prime has 2 divisors) -/
theorem tau_2 : τ 2 = 2 := by native_decide

/-- τ(6) = 4 -/
theorem tau_6 : τ 6 = 4 := by native_decide

/-- τ(12) = 6 (highly composite number) -/
theorem tau_12 : τ 12 = 6 := by native_decide

/-!
## The Function F(x)

F(x) measures the longest run of consecutive integers with pairwise
distinct divisor counts. A large F(x) means divisor counts vary widely;
a small F(x) means collisions happen quickly.
-/

/-- F(x) = max k such that some n+1, ..., n+k ≤ x all have distinct τ values -/
noncomputable def F (x : ℝ) : ℕ :=
  sSup {k : ℕ | ∃ (n : ℕ), n + k ≤ x ∧ (Set.Ioc n (n + k)).InjOn τ}

/-!
## The Main Conjecture

The key question is whether F(x) is bounded by a polynomial in log x.
This would mean divisor count collisions happen within intervals of
polylogarithmic length.
-/

/-- The conjecture F(x) ≤ (log x)^{O(1)} expressed as a Prop -/
def Erdos945Prop : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ x in atTop, (F x : ℝ) ≤ x.log ^ C

/-- **Erdős Problem #945** (OPEN)

Is F(x) ≤ (log x)^{O(1)}? That is, is the maximal length of consecutive
integers with distinct divisor counts bounded by a polynomial in log x?

This remains unproven despite significant progress on bounds. -/
axiom erdos945_conjecture : Erdos945Prop

/-!
## Equivalent Formulation

The conjecture can be restated: there exists C > 0 such that every
interval [x, x + (log x)^C] contains two integers with equal τ.
-/

/-- Equivalent formulation: every long-enough interval has a τ collision -/
def Erdos945Collision : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ x in atTop,
    ∃ a b : ℕ, a ≠ b ∧
    (a : ℝ) ∈ Set.Icc x (x + x.log ^ C) ∧
    (b : ℝ) ∈ Set.Icc x (x + x.log ^ C) ∧
    τ a = τ b

/-- The two formulations are equivalent -/
axiom erdos945_equivalence : Erdos945Prop ↔ Erdos945Collision

/-!
## Known Bounds (Erdős-Mirsky 1952)

Erdős and Mirsky established both lower and upper bounds on F(x).
The gap between them remains open after 70+ years.
-/

/-- **Erdős-Mirsky Lower Bound** (1952)

F(x) ≫ (log x)^{1/2} / log log x

This shows F(x) grows at least like a fractional power of log x. -/
axiom erdos_mirsky_lower_bound :
    (fun (x : ℕ) => (x : ℝ).log.sqrt / (x : ℝ).log.log) =O[atTop]
    fun (n : ℕ) => (F n : ℝ)

/-- **Erdős-Mirsky Upper Bound** (1952)

log F(x) ≪ (log x)^{1/2} / log log x

Equivalently: F(x) ≪ exp(O((log x)^{1/2} / log log x)) -/
axiom erdos_mirsky_upper_bound :
    (fun (n : ℕ) => (F n : ℝ).log) =O[atTop]
    fun (x : ℕ) => (x : ℝ).log.sqrt / (x : ℝ).log.log

/-!
## Improved Upper Bound (Beker)

Beker improved the Erdős-Mirsky upper bound significantly.
-/

/-- **Beker's Upper Bound**

F(x) ≪ exp(O((log x)^{1/3 + o(1)}))

This is currently the best known upper bound. -/
axiom beker_upper_bound :
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    (fun (n : ℕ) => (F n : ℝ).log) =O[atTop]
    fun (x : ℕ) => (x : ℝ).log ^ (1/3 + o x)

/-!
## Conditional Result (Cramér's Conjecture)

Under Cramér's conjecture about prime gaps, F(x) ≪ (log x)².
-/

/-- **Conditional on Cramér's Conjecture**

If Cramér's conjecture holds (prime gaps ≪ (log p)²), then F(x) ≪ (log x)².
This would nearly resolve the problem. -/
axiom cramer_implies_bound :
    (∀ᶠ p in atTop, ∀ q : ℕ, q.Prime → p.Prime → p < q →
      (∀ r, p < r → r < q → ¬r.Prime) → (q - p : ℝ) ≤ (p : ℝ).log ^ 2) →
    ∀ᶠ x in atTop, (F x : ℝ) ≤ x.log ^ 2

end Erdos945
