/-
  Erdős Problem #325: Sums of Three k-th Powers

  Let k ≥ 3 and f_{k,3}(x) denote the number of integers ≤ x which are
  the sum of three nonnegative k-th powers. Is it true that
    f_{k,3}(x) ≫ x^{3/k}?

  **Status**: OPEN - The main conjecture remains unresolved.

  **Historical Context**:
  For sums of TWO k-th powers, Mahler and Erdős proved in 1938 that
  f_{k,2}(x) ≫ x^{2/k}. The natural extension to three terms asks whether
  f_{k,3}(x) ≫ x^{3/k}, but this remains open.

  **Best Known Results**:
  For k = 3 (cubes), Wooley (2015) proved f_{3,3}(x) ≫ x^{0.917...}, which
  falls short of the conjectured x^{3/3} = x^1.

  References:
  - https://erdosproblems.com/325
  - Wooley, T.D. "Sums of three cubes, II" Acta Arith. (2015), 73-100
  - Erdős & Graham, "Old and New Problems in Combinatorial Number Theory" (1980)
-/

import Mathlib

open Asymptotics Filter

namespace Erdos325

/-!
## Core Definitions

We define the predicate for an integer being a sum of three k-th powers,
and the counting function f_{k,3}(x).
-/

/-- A natural number n is a sum of three k-th powers if there exist
nonnegative integers a, b, c such that a^k + b^k + c^k = n. -/
def IsSumThreePower (k n : ℕ) : Prop := ∃ a b c : ℕ, a ^ k + b ^ k + c ^ k = n

/-- The counting function f_{k,3}(x): the number of integers ≤ x
which are expressible as sums of three k-th powers. -/
noncomputable def cardIsSumThreePowerBelow (k x : ℕ) : ℕ :=
  {n ∈ Set.Iic x | IsSumThreePower k n}.ncard

/-!
## Basic Examples

We verify some simple cases of sums of three k-th powers.
-/

/-- 0 is a sum of three k-th powers (0^k + 0^k + 0^k = 0 for any k ≥ 1). -/
theorem zero_isSumThreePower (k : ℕ) (hk : 1 ≤ k) : IsSumThreePower k 0 := by
  use 0, 0, 0
  simp [Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)]

/-- 3 is a sum of three squares (1² + 1² + 1² = 3). -/
theorem three_isSumThreePower_two : IsSumThreePower 2 3 := by
  use 1, 1, 1
  native_decide

/-- 3 is a sum of three cubes (1³ + 1³ + 1³ = 3). -/
theorem three_isSumThreePower_three : IsSumThreePower 3 3 := by
  use 1, 1, 1
  native_decide

/-- 29 is a sum of three cubes (3³ + 1³ + 1³ = 27 + 1 + 1 = 29). -/
theorem twentynine_isSumThreePower_three : IsSumThreePower 3 29 := by
  use 3, 1, 1
  native_decide

/-!
## The Main Conjecture

The main question asks whether f_{k,3}(x) grows at least as fast as x^{3/k}.
In asymptotic notation: is x^{3/k} = O(f_{k,3}(x))?

This is equivalent to asking if there exists a constant c > 0 such that
f_{k,3}(x) ≥ c · x^{3/k} for all sufficiently large x.
-/

/-- **Erdős Problem #325**: For k ≥ 3, does f_{k,3}(x) ≫ x^{3/k}?

In Mathlib's asymptotic notation, this asks whether x^{3/k} = O(f_{k,3}(x)).

This remains OPEN. We state it as an axiom. -/
axiom erdos_325_conjecture : ∀ k : ℕ, 3 ≤ k →
    (fun x : ℕ => (x : ℝ) ^ (3 / k : ℝ)) =O[atTop]
    (fun x : ℕ => (cardIsSumThreePowerBelow k x : ℝ))

/-!
## Variants and Partial Results

Erdős also asked about a weaker form with an epsilon loss, and there
are known partial results for specific values of k.
-/

/-- A weaker variant: is f_{k,3}(x) ≫_ε x^{3/k - ε} for every ε > 0?

This is also OPEN. -/
axiom erdos_325_weaker : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 3 ≤ k →
    (fun x : ℕ => (x : ℝ) ^ ((3 / k : ℝ) - ε)) =O[atTop]
    (fun x : ℕ => (cardIsSumThreePowerBelow k x : ℝ))

/-- **Wooley's Theorem (2015)**: For sums of three cubes (k = 3),
f_{3,3}(x) ≫ x^{0.917}.

This is the best known bound for k = 3, falling short of the
conjectured x^1 = x^{3/3}.

We state this as an axiom since the proof is beyond Mathlib. -/
axiom wooley_three_cubes :
    (fun x : ℕ => (x : ℝ) ^ (0.917 : ℝ)) =O[atTop]
    (fun x : ℕ => (cardIsSumThreePowerBelow 3 x : ℝ))

/-!
## Context: The Two-Term Case

For comparison, the two-term case was solved by Mahler and Erdős in 1938.
They proved that f_{k,2}(x) ≫ x^{2/k}, where f_{k,2}(x) counts integers ≤ x
that are sums of TWO k-th powers.

The three-term extension remains elusive.
-/

/-- A number is a sum of two k-th powers. -/
def IsSumTwoPower (k n : ℕ) : Prop := ∃ a b : ℕ, a ^ k + b ^ k = n

/-- The counting function for sums of two k-th powers. -/
noncomputable def cardIsSumTwoPowerBelow (k x : ℕ) : ℕ :=
  {n ∈ Set.Iic x | IsSumTwoPower k n}.ncard

/-- **Mahler-Erdős Theorem (1938)**: f_{k,2}(x) ≫ x^{2/k}.

This is the analogue of the conjecture for two terms, and it IS proved.
We state it as an axiom since the proof requires analytic methods. -/
axiom mahler_erdos_two_powers : ∀ k : ℕ, 2 ≤ k →
    (fun x : ℕ => (x : ℝ) ^ (2 / k : ℝ)) =O[atTop]
    (fun x : ℕ => (cardIsSumTwoPowerBelow k x : ℝ))

end Erdos325
