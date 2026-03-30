/-!
Erdős Problem #287: Unit Fraction Decomposition Gaps

Source: https://erdosproblems.com/287
Status: OPEN

Statement:
Let k ≥ 2. For any distinct integers 1 < n₁ < ... < nₖ such that
1 = 1/n₁ + ... + 1/nₖ, must max(n_{i+1} - nᵢ) ≥ 3?

The example 1 = 1/2 + 1/3 + 1/6 shows that 3 would be best possible.
Erdős proved the weaker result that max(n_{i+1} - nᵢ) ≥ 2, which is
equivalent to saying 1 is not the sum of reciprocals of consecutive integers.

References:
- Erdős: Lower bound of ≥ 2 (no consecutive integer reciprocals sum to 1)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.List.Basic

namespace Erdos287

/-!
## Part I: Definitions
-/

/--
An Egyptian fraction representation of 1: a sorted list of distinct integers > 1
whose reciprocals sum to 1.
-/
def IsUnitFractionDecomp (ns : List ℕ) : Prop :=
  ns.length ≥ 2 ∧
  ns.Sorted (· < ·) ∧
  (∀ n ∈ ns, n > 1) ∧
  (ns.map (fun n => (1 : ℚ) / n)).sum = 1

/-- The maximum gap between consecutive elements of a sorted list. -/
def maxGap (ns : List ℕ) : ℕ :=
  (ns.zip ns.tail).foldl (fun acc p => max acc (p.2 - p.1)) 0

/-!
## Part II: The Example
-/

/-- 1 = 1/2 + 1/3 + 1/6 is a valid decomposition with max gap 3. -/
/-!
## Part III: Known Lower Bound
-/

/--
**Erdős's Theorem**: The maximum gap is at least 2.

Equivalently: 1 is not the sum of reciprocals of consecutive integers
n, n+1, ..., n+k for any n, k.
-/
axiom no_consecutive_reciprocals :
    ∀ ns : List ℕ, IsUnitFractionDecomp ns → maxGap ns ≥ 2

/-!
## Part IV: The Conjecture
-/

/--
**Erdős's Conjecture (OPEN)**: The maximum gap is at least 3.

If true, the example [2, 3, 6] would be optimal (max gap = 3).
-/
/-!
## Part V: Main Theorem
-/

/--
**Erdős Problem #287: OPEN**

Known: max gap ≥ 2 (Erdős).
Conjectured: max gap ≥ 3.
Best known example: [2, 3, 6] with gap 3.
-/
theorem erdos_287 :
    ∀ ns : List ℕ, IsUnitFractionDecomp ns → maxGap ns ≥ 2 :=
  no_consecutive_reciprocals

end Erdos287
