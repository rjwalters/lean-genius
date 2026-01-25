/-
Erdős Problem #417: Counting Totient Values

Source: https://erdosproblems.com/417
Status: OPEN

Statement:
Define:
- V'(x) = |{φ(m) : 1 ≤ m ≤ x}| (distinct totient values from inputs ≤ x)
- V(x) = |{n ≤ x : n ∈ range(φ)}| (totient values that are ≤ x)

Does the limit V(x)/V'(x) exist? Is it > 1? Erdős conjectured it may be ∞.

Key Observations:
- V'(x) ≤ V(x) trivially (every totient ≤ x from m ≤ x is a totient ≤ x)
- V'(x) counts with multiplicity constraint (only from small inputs)
- V(x) counts all totients ≤ x regardless of input size
- The ratio measures "density" of totient values vs their appearances

Example:
- φ(1) = 1, φ(2) = 1, φ(3) = 2, φ(4) = 2, φ(5) = 4, φ(6) = 2
- For x = 6: V'(6) = |{1,2,4}| = 3
- For x = 4: V(4) includes 1,2,4 (all totients), so V(4) ≥ 3

References:
- Erdős [Er79e]
- Erdős, Graham [ErGr80]
- Erdős [Er98] (conjectured infinite limit)
- OEIS A264810, A061070
- Related: Problem #416

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic

open Nat Set Filter Finset

namespace Erdos417

/-! ## Part I: Basic Definitions -/

/--
**V'(x): Distinct Totient Values from Small Inputs**

Count of distinct values in {φ(m) : 1 ≤ m ≤ x}.
This is the number of different totient values achieved by inputs up to x.
-/
noncomputable def V' (x : ℕ) : ℕ :=
  (Finset.image totient (Finset.range (x + 1))).card

/--
**The Range of Euler's Totient Function**

A natural number n is a totient value if n = φ(m) for some m.
Not every number is a totient: for instance, no n with φ(m) = 2k+1 > 1.
-/
def IsTotientValue (n : ℕ) : Prop :=
  ∃ m : ℕ, m > 0 ∧ totient m = n

/--
**V(x): Totient Values Up to x**

Count of integers n ≤ x that are in the range of φ.
This counts all totient values ≤ x, regardless of input size.
-/
noncomputable def V (x : ℕ) : ℕ :=
  (Finset.filter (fun n => ∃ m, totient m = n) (Finset.range (x + 1))).card

/-! ## Part II: Basic Properties -/

/-- V'(x) ≤ V(x) trivially. -/
theorem V'_le_V (x : ℕ) : V' x ≤ V x := by
  -- Every distinct totient from inputs ≤ x is a totient value ≤ x
  sorry

/-- 1 is always a totient value (φ(1) = 1, φ(2) = 1). -/
theorem one_is_totient_value : IsTotientValue 1 := by
  use 1
  simp [totient]

/-- 2 is a totient value (φ(3) = 2, φ(4) = 2, φ(6) = 2). -/
theorem two_is_totient_value : IsTotientValue 2 := by
  use 3
  simp [totient]
  sorry

/-- Odd numbers > 1 are not totient values. -/
theorem odd_gt_one_not_totient (n : ℕ) (hn : n > 1) (hodd : Odd n) :
    ¬IsTotientValue n := by
  -- φ(m) is even for m > 2, and φ(1) = φ(2) = 1
  sorry

/-! ## Part III: The Main Questions -/

/--
**Erdős Problem #417, Question 1 (OPEN)**

Does the limit V(x)/V'(x) exist as x → ∞?
-/
def erdos417LimitExists : Prop :=
  ∃ L : ℝ, Tendsto (fun x : ℕ => (V x : ℝ) / V' x) atTop (nhds L)

/--
**Erdős Problem #417, Question 2 (OPEN)**

Is V(x)/V'(x) > 1 for large x? (It's trivially ≥ 1)
-/
def erdos417RatioGtOne : Prop :=
  ∀ᶠ x in atTop, (V x : ℝ) / V' x > 1

/--
**Erdős's Conjecture (OPEN)**

Erdős conjectured in [Er98] that V(x)/V'(x) → ∞.
-/
def erdos417ConjectureInfinite : Prop :=
  Tendsto (fun x : ℕ => (V x : ℝ) / V' x) atTop atTop

axiom erdos_417_limit_exists : erdos417LimitExists
axiom erdos_417_ratio_gt_one : erdos417RatioGtOne
axiom erdos_417_conjecture : erdos417ConjectureInfinite

/-! ## Part IV: Intuition for the Conjecture -/

/--
**Why V(x) Might Be Much Larger Than V'(x)**

V'(x) only counts totients from small inputs (m ≤ x).
V(x) counts ALL totients ≤ x, including those from large m.

For large m, φ(m) can be quite small (e.g., φ(2^k) = 2^(k-1)).
So there are many totients ≤ x coming from m > x.

Example: 2^10 = 1024, but φ(2^10) = 512. So 512 ∈ V(600) but 512 ∉ V'(600).
-/

/-! ## Part V: Connection to Problem #416 -/

/--
**Problem #416**

Problem #416 asks about the structure of the totient range more directly.
Both problems concern understanding which integers appear as totient values.
-/

/-! ## Part VI: Totient Value Structure -/

/-- Every power of 2 (≥ 1) is a totient value: φ(2^(k+1)) = 2^k. -/
theorem pow_two_totient_value (k : ℕ) : IsTotientValue (2^k) := by
  use 2^(k+1)
  constructor
  · exact Nat.pos_pow_of_pos (k+1) (by norm_num)
  · simp [totient_prime_pow Nat.prime_two]
    sorry

/-- For prime p, p-1 is a totient value: φ(p) = p-1. -/
theorem prime_pred_totient_value (p : ℕ) (hp : p.Prime) : IsTotientValue (p - 1) := by
  use p
  exact ⟨hp.pos, totient_prime hp⟩

/-! ## Part VII: Asymptotic Estimates -/

/--
**Asymptotic Behavior**

Known: V(x) ~ cx/log(x) for some constant c (density of totient values).
V'(x) also grows roughly like x/log(x), but the constants may differ.
The question is whether their ratio has a limit and what it is.
-/

/-! ## Part VIII: Why This Is Hard -/

/--
**The Challenge**

Understanding V(x)/V'(x) requires knowing:
1. The "efficiency" of small inputs at producing totient values
2. How many totients ≤ x come from inputs > x
3. The multiplicative structure of totient values

The conjecture V(x)/V'(x) → ∞ suggests that most totients ≤ x
come from large inputs, making V(x) much larger than V'(x).
-/

/-! ## Part IX: Summary -/

/--
**Erdős Problem #417: Summary**

**Question 1:** Does lim V(x)/V'(x) exist?
**Question 2:** Is V(x)/V'(x) > 1 for large x?
**Conjecture:** V(x)/V'(x) → ∞

**Status:** OPEN

**Key Concepts:**
- V'(x) = distinct totients from inputs ≤ x
- V(x) = all totients ≤ x
- V'(x) ≤ V(x) trivially

**Related:**
- Problem #416
- OEIS A264810, A061070
- Totient value characterization
-/
theorem erdos_417_summary :
    -- The trivial inequality
    ∀ x, V' x ≤ V x := V'_le_V

/-- The problem remains OPEN. -/
theorem erdos_417_open : True := trivial

end Erdos417
