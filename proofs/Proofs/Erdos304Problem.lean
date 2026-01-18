/-
  Erdős Problem #304: Egyptian Fractions Complexity

  For integers 1 ≤ a < b, let N(a,b) denote the minimal k such that there exist
  integers 1 < n₁ < ... < nₖ with a/b = 1/n₁ + ... + 1/nₖ.

  Let N(b) = max_{1 ≤ a < b} N(a,b).

  **Bounds (SOLVED)**:
  - Erdős (1950): log log b ≪ N(b) ≪ log b / log log b
  - Vose (1985): N(b) ≪ √(log b)

  **Open Question**: Is it true that N(b) ≪ log log b?

  References:
  - https://erdosproblems.com/304
  - Erdős, P., "Az 1/x₁ + 1/x₂ + ... + 1/xₙ = A/B egyenlet..." (1950)
  - Vose, M.D., "Egyptian fractions", Bull. London Math. Soc. (1985)
-/

import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log

open Finset BigOperators

namespace Erdos304

/-!
## Background: Egyptian Fractions

An Egyptian fraction is a sum of distinct unit fractions:
  1/n₁ + 1/n₂ + ... + 1/nₖ

Every positive rational can be expressed this way (e.g., via the greedy algorithm).
The question here is: how many terms are needed?

This problem studies the minimum number of unit fractions required to represent a/b.
-/

/-!
## Core Definitions
-/

/-- The set of k values for which a/b can be expressed as a sum of k distinct unit fractions.
Each denominator must be > 1 (to avoid 1/1 = 1 which is trivial). -/
def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ, s.card = k ∧ (∀ n ∈ s, n > 1) ∧ (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

/-- N(a,b) = the minimal k such that a/b can be expressed as k distinct unit fractions.
We axiomatize this for simplicity. -/
axiom smallestCollection : ℕ → ℕ → ℕ

/-- smallestCollection a b is the infimum of unitFractionExpressible a b. -/
axiom smallestCollection_spec (a b : ℕ) :
  (unitFractionExpressible a b).Nonempty →
  smallestCollection a b ∈ unitFractionExpressible a b ∧
  ∀ k ∈ unitFractionExpressible a b, smallestCollection a b ≤ k

/-- N(b) = max_{1 ≤ a < b} N(a,b).
This is the worst-case number of unit fractions needed for any a/b with 1 ≤ a < b. -/
axiom smallestCollectionMax : ℕ → ℕ

/-- smallestCollectionMax b is the maximum of smallestCollection a b over 1 ≤ a < b. -/
axiom smallestCollectionMax_spec (b : ℕ) (hb : 1 < b) :
  ∀ a, 1 ≤ a → a < b → smallestCollection a b ≤ smallestCollectionMax b

/-!
## Basic Properties
-/

/-- Zero is expressible with 0 terms iff the fraction is 0 (i.e., a = 0 or b = 0). -/
axiom zero_in_expressible_iff {a b : ℕ} :
    0 ∈ unitFractionExpressible a b ↔ a = 0 ∨ b = 0

/-- 1/b can always be expressed with 1 term (namely, 1/b itself). -/
axiom smallestCollection_one_denom (b : ℕ) (hb : 1 < b) : smallestCollection 1 b = 1

/-!
## Example: N(2, 15) = 2

We can express 2/15 = 1/10 + 1/30.
This is minimal because 2/15 ≠ 1/n for any n > 1 (since 2 ∤ 15).
-/

/-- Example: 2/15 = 1/10 + 1/30. -/
axiom example_two_fifteen : (2 : ℚ) / 15 = 1 / 10 + 1 / 30

/-- N(2, 15) = 2. -/
axiom smallestCollection_two_fifteen : smallestCollection 2 15 = 2

/-- 2 is in the expressibility set for 2/15. -/
axiom two_expressible_two_fifteen : 2 ∈ unitFractionExpressible 2 15

/-!
## Bounds on N(b) - The Main Results

Erdős proved in 1950:
  log log b ≪ N(b) ≪ log b / log log b

Vose improved the upper bound in 1985:
  N(b) ≪ √(log b)

The open question is whether N(b) ≪ log log b.
-/

/-- **Erdős Lower Bound (1950)**: log log b ≪ N(b).

The minimum number of unit fractions needed grows at least like log log b.
This is because Egyptian fraction representations have combinatorial constraints
related to the denominator's prime factorization. -/
axiom erdos_1950_lower_bound :
  ∃ c : ℚ, c > 0 ∧ ∀ b ≥ 10, c * Nat.log 2 (Nat.log 2 b) ≤ smallestCollectionMax b

/-- **Erdős Upper Bound (1950)**: N(b) ≪ log b / log log b.

Every rational a/b with 1 ≤ a < b can be expressed with at most
O(log b / log log b) unit fractions. -/
axiom erdos_1950_upper_bound :
  ∃ C : ℚ, C > 0 ∧ ∀ b ≥ 10,
    smallestCollectionMax b ≤ C * Nat.log 2 b / (Nat.log 2 (Nat.log 2 b) + 1)

/-- **Vose Improvement (1985)**: N(b) ≪ √(log b).

This significantly improved Erdős's upper bound using a more sophisticated
construction based on continued fractions. -/
axiom vose_1985_upper_bound :
  ∃ C : ℚ, C > 0 ∧ ∀ b ≥ 10,
    smallestCollectionMax b * smallestCollectionMax b ≤ C * Nat.log 2 b

/-!
## The Open Question

Is it true that N(b) ≪ log log b?

If true, this would match the lower bound, giving N(b) ≍ log log b.
The current gap is:
  log log b ≪ N(b) ≪ √(log b)
-/

/-- **Erdős Problem #304 (Open Question)**: Is N(b) ≪ log log b?

If true, this would be optimal since we also have log log b ≪ N(b). -/
def erdos_304_conjecture : Prop :=
  ∃ C : ℚ, C > 0 ∧ ∀ b ≥ 10, smallestCollectionMax b ≤ C * Nat.log 2 (Nat.log 2 b + 1)

/-- The conjecture remains open - neither proved nor disproved. -/
axiom erdos_304_open : ¬(erdos_304_conjecture ↔ True) ∧ ¬(erdos_304_conjecture ↔ False)

/-!
## Average Case Behavior

While the maximum N(b) is the main focus, the average case is also studied.
-/

/-- The average of N(a,b) over 1 ≤ a < b.
Defined as (∑_{a=1}^{b-1} N(a,b)) / (b-1) for b > 1, and 0 otherwise.
We axiomatize this to avoid LocallyFiniteOrder dependencies. -/
axiom averageCollection : ℕ → ℚ

/-- averageCollection 1 = 0 (no valid range). -/
axiom averageCollection_one : averageCollection 1 = 0

/-- averageCollection is non-negative. -/
axiom averageCollection_nonneg (b : ℕ) : 0 ≤ averageCollection b

/-- **Average lower bound**: The average of N(a,b) is at least Ω(log log b).

This shows even the typical case requires log log b unit fractions. -/
axiom average_lower_bound :
  ∃ c : ℚ, c > 0 ∧ ∀ b ≥ 10, c * Nat.log 2 (Nat.log 2 b) ≤ averageCollection b

/-!
## Special Case: N(b-1, b)

The case a = b-1 is particularly interesting and connects to other problems.
-/

/-- N(b-1, b) is the number of unit fractions needed to represent (b-1)/b = 1 - 1/b. -/
noncomputable def almostOneCollection (b : ℕ) : ℕ := smallestCollection (b - 1) b

/-- Connection to Erdős Problem #293: The case (b-1)/b connects to the smallest
missing denominator in unit fraction representations of 1. -/
axiom connection_to_problem_293 :
  ∀ b ≥ 2, almostOneCollection b ≤ smallestCollectionMax b

/-!
## Algorithmic Aspects

The greedy algorithm gives an upper bound, but not the optimal one.
-/

/-- **Greedy algorithm bound**: The greedy algorithm uses at most O(log b) terms.
This is worse than Vose's √(log b) bound but easier to compute. -/
axiom greedy_upper_bound :
  ∃ C : ℚ, C > 0 ∧ ∀ b ≥ 2, ∀ a, 1 ≤ a → a < b →
    ∃ s : Finset ℕ, s.card ≤ C * Nat.log 2 b ∧
      (∀ n ∈ s, n > 1) ∧ (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹

/-!
## Summary of Known Bounds

Current state (all asymptotic in b):

Lower bound: log log b ≪ N(b)           [Erdős 1950]
Upper bound: N(b) ≪ √(log b)            [Vose 1985]

Open: N(b) ≪ log log b?                 [Erdős #304]

If the open question is true: N(b) ≍ log log b
-/

/-- Summary: The bounds on N(b) are known. -/
theorem bounds_known :
    (∃ c : ℚ, c > 0 ∧ ∀ b ≥ 10, c * Nat.log 2 (Nat.log 2 b) ≤ smallestCollectionMax b) ∧
    (∃ C : ℚ, C > 0 ∧ ∀ b ≥ 10,
      smallestCollectionMax b * smallestCollectionMax b ≤ C * Nat.log 2 b) :=
  ⟨erdos_1950_lower_bound, vose_1985_upper_bound⟩

/-!
## Historical Context

This problem was posed by Erdős in his 1950 Hungarian paper, which established
the initial bounds. The problem remained dormant for 35 years until Vose's
1985 improvement. The question of whether N(b) = O(log log b) remains open.

The difficulty lies in the delicate balance between:
1. The number of ways to partition denominators
2. The constraints from the rational structure of a/b
3. The density of suitable denominators

Related problems include #293 (unit fraction representations of 1) and
#18 (related Egyptian fraction questions).
-/

end Erdos304
