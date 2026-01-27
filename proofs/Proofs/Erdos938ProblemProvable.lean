/-
Erdős Problem #938: Three-term Progressions in Consecutive Powerful Numbers

A powerful number (also called squarefull number) is a positive integer n such that
if a prime p divides n, then p² also divides n. Equivalently, n = a²b³ for some
positive integers a and b.

The sequence of powerful numbers begins: 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, ...

Problem: Are there only finitely many three-term arithmetic progressions among
consecutive powerful numbers n_k, n_{k+1}, n_{k+2}?

This is Problem #938 from erdosproblems.com. Related to Problem #364 which asks
whether three consecutive integers can all be powerful (conjectured NO).

Reference: https://erdosproblems.com/938
OEIS: A001694 (Powerful numbers)

Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-
# Erdős Problem 938: Three-term Progressions in Consecutive Powerful Numbers

*Reference:* [erdosproblems.com/938](https://www.erdosproblems.com/938)
-/

open Nat Finset
open Filter

namespace Erdos938

/-- A positive integer n is powerful (squarefull) if p | n implies p² | n for all primes p -/
def Powerful (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

/-- Equivalently, n is powerful iff n = a² · b³ for some a, b ≥ 1 -/
def PowerfulAlt (n : ℕ) : Prop :=
  ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ n = a^2 * b^3

/-- The set of all powerful numbers -/
def powerfulSet : Set ℕ := {n | Powerful n}

/-- The n-th powerful number (1-indexed: P(1) = 1, P(2) = 4, P(3) = 8, ...) -/
noncomputable def nthPowerful (n : ℕ) : ℕ :=
  (powerfulSet.enumerate (· < ·)).nth n |>.getD 0

/-- Small powerful numbers for verification -/
example : Powerful 1 := ⟨le_refl 1, fun p hp hdiv => by
  have := Nat.Prime.one_lt hp
  omega⟩

example : Powerful 4 := ⟨by omega, fun p hp hdiv => by
  have h4 : 4 = 2^2 := rfl
  interval_cases p <;> simp_all⟩

example : Powerful 8 := ⟨by omega, fun p hp hdiv => by
  have h8 : 8 = 2^3 := rfl
  interval_cases p <;> simp_all⟩

example : Powerful 9 := ⟨by omega, fun p hp hdiv => by
  have h9 : 9 = 3^2 := rfl
  interval_cases p <;> simp_all⟩

/-- Three consecutive powerful numbers form an AP if n_{k+1} - n_k = n_{k+2} - n_{k+1} -/
def ConsecutivePowerfulAP (k : ℕ) : Prop :=
  let n1 := nthPowerful k
  let n2 := nthPowerful (k + 1)
  let n3 := nthPowerful (k + 2)
  n2 - n1 = n3 - n2

/-- The set of indices k where consecutive powerful numbers form an AP -/
def apIndices : Set ℕ := {k | ConsecutivePowerfulAP k}

/-
## Main Problem

Erdős Problem #938: Is the set apIndices finite?

This asks whether there are only finitely many three-term arithmetic progressions
among consecutive powerful numbers.
-/

/-- Erdős Problem #938: Are there only finitely many three-term APs
    among consecutive powerful numbers? -/
@[category research open, AMS 11]
theorem erdos_938 : answer(sorry) ↔ apIndices.Finite := by
  sorry

/-
## Related Results and Bounds

### Gap Distribution

The gaps between consecutive powerful numbers are not well-understood.
Unlike primes, powerful numbers can cluster or have large gaps.
-/

/-- The gap between consecutive powerful numbers -/
noncomputable def powerfulGap (k : ℕ) : ℕ :=
  nthPowerful (k + 1) - nthPowerful k

/-- For an AP, consecutive gaps must be equal -/
lemma ap_equal_gaps (k : ℕ) (h : ConsecutivePowerfulAP k) :
    powerfulGap k = powerfulGap (k + 1) := by
  unfold ConsecutivePowerfulAP powerfulGap at *
  exact h

/-
### Connection to Problem 364

Erdős Problem #364 conjectures that no three consecutive integers are all powerful.
If true, this would be a much stronger result than the current problem, as it would
forbid APs of the form (n, n+1, n+2) with common difference 1.
-/

/-- Three consecutive integers cannot all be powerful (conjectured) -/
def NoThreeConsecutivePowerful : Prop :=
  ∀ n : ℕ, ¬(Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2))

/-- Problem 364: No three consecutive integers are all powerful -/
@[category research open, AMS 11]
theorem erdos_364 : answer(sorry) ↔ NoThreeConsecutivePowerful := by
  sorry

/-
### Counting Powerful Numbers

The asymptotic density of powerful numbers up to x is well-known.
-/

/-- Counting function: number of powerful numbers ≤ n -/
noncomputable def countPowerful (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter Powerful |>.card

/-- Asymptotic: The count of powerful numbers ≤ x is ~ c·√x where c = ζ(3/2)/ζ(3) ≈ 2.17 -/
-- This is a known result: π_P(x) ~ (ζ(3/2)/ζ(3)) · √x
theorem powerful_count_asymptotic :
  ∃ c : ℝ, c > 0 ∧ Filter.Tendsto
    (fun n => (countPowerful n : ℝ) / Real.sqrt n) Filter.atTop (nhds c) := by sorry

/-
### Known Examples of APs

Some known three-term APs among consecutive powerful numbers exist for small indices.
Finding whether infinitely many such patterns exist is the essence of Problem #938.
-/

/-- Example: Check if specific indices form APs (computational verification needed) -/
-- The problem is essentially computational for small cases:
-- - Enumerate powerful numbers
-- - Check consecutive triples for AP condition
-- - Question: Does this process ever terminate?

/-
## Hardness and Obstructions

The problem is subtle because:
1. Powerful numbers have irregular distribution
2. The AP condition requires exact arithmetic relationships
3. The "consecutive" constraint is more restrictive than arbitrary APs
-/

/-- An AP of three consecutive powerful numbers with common difference d -/
structure ConsecutivePowerfulAPWithDiff where
  k : ℕ
  d : ℕ
  h_ap : ConsecutivePowerfulAP k
  h_diff : powerfulGap k = d

/-- The set of common differences that appear in consecutive powerful APs -/
noncomputable def apDifferences : Set ℕ :=
  {d | ∃ k, ConsecutivePowerfulAP k ∧ powerfulGap k = d}

/-- Sub-question: Is the set of AP differences finite? -/
-- This would follow from the main conjecture
lemma differences_finite_of_indices_finite (h : apIndices.Finite) :
    apDifferences.Finite := by
  sorry

end Erdos938

-- Placeholder for main result
theorem erdos_938_placeholder : True := trivial
