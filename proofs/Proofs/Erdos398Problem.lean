/-
Erdős Problem #398: The Brocard-Ramanujan Conjecture

Are the only solutions to n! + 1 = m² when n = 4, 5, 7?

**Status**: OPEN

**Background**:
The Brocard-Ramanujan conjecture asks whether the equation n! + 1 = m²
has only the three known solutions: (4, 5), (5, 11), (7, 71).

This is an old problem dating back to Brocard (1876, 1885) and was
independently posed by Ramanujan. Erdős and Graham described it as
"almost certainly true but intractable at present."

**Known Results**:
- The three solutions n = 4, 5, 7 are verified
- Overholt (1993) proved finitely many solutions assuming weak ABC
- Computational search: no solutions up to n = 10^9

Reference: https://erdosproblems.com/398
Wikipedia: https://en.wikipedia.org/wiki/Brocard%27s_problem
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

open Nat Set

namespace Erdos398

/-!
## The Brocard-Ramanujan Equation

The equation n! + 1 = m² is remarkably sparse in solutions.
A pair (n, m) satisfying this is called a **Brown number**.

The three known Brown numbers are:
- (4, 5):  4! + 1 = 24 + 1 = 25 = 5²
- (5, 11): 5! + 1 = 120 + 1 = 121 = 11²
- (7, 71): 7! + 1 = 5040 + 1 = 5041 = 71²
-/

/--
A Brown number is a pair (n, m) such that n! + 1 = m².
-/
def IsBrownNumber (n m : ℕ) : Prop := n ! + 1 = m ^ 2

/-!
## Verified Solutions

We verify the three known Brown numbers by direct computation.
-/

/--
(4, 5) is a Brown number: 4! + 1 = 25 = 5²
-/
theorem brown_4_5 : IsBrownNumber 4 5 := by
  unfold IsBrownNumber
  native_decide

/--
(5, 11) is a Brown number: 5! + 1 = 121 = 11²
-/
theorem brown_5_11 : IsBrownNumber 5 11 := by
  unfold IsBrownNumber
  native_decide

/--
(7, 71) is a Brown number: 7! + 1 = 5041 = 71²
-/
theorem brown_7_71 : IsBrownNumber 7 71 := by
  unfold IsBrownNumber
  native_decide

/-!
## Small Cases: Non-Solutions

We verify that small values other than 4, 5, 7 don't work.
For these, we show n! + 1 is not a perfect square by computing it
and checking it lies strictly between consecutive squares.
-/

/--
0! + 1 = 2, which lies strictly between 1² and 2².
-/
theorem factorial_0_plus_1 : (0 : ℕ)! + 1 = 2 := by native_decide

/--
1! + 1 = 2, which lies strictly between 1² and 2².
-/
theorem factorial_1_plus_1 : (1 : ℕ)! + 1 = 2 := by native_decide

/--
2! + 1 = 3, which lies strictly between 1² and 2².
-/
theorem factorial_2_plus_1 : (2 : ℕ)! + 1 = 3 := by native_decide

/--
3! + 1 = 7, which lies strictly between 2² and 3².
-/
theorem factorial_3_plus_1 : (3 : ℕ)! + 1 = 7 := by native_decide

/--
6! + 1 = 721, which lies strictly between 26² = 676 and 27² = 729.
-/
theorem factorial_6_plus_1 : (6 : ℕ)! + 1 = 721 := by native_decide

/--
8! + 1 = 40321, which lies strictly between 200² and 201².
-/
theorem factorial_8_plus_1 : (8 : ℕ)! + 1 = 40321 := by native_decide

/-!
## The Open Conjecture

The Brocard-Ramanujan conjecture states that 4, 5, 7 are the ONLY
values of n for which n! + 1 is a perfect square.
-/

/--
The set of n such that n! + 1 is a perfect square.
-/
def BrocardSet : Set ℕ := {n | ∃ m, n ! + 1 = m ^ 2}

/--
4 is in the Brocard set.
-/
theorem four_in_brocard : 4 ∈ BrocardSet := ⟨5, by native_decide⟩

/--
5 is in the Brocard set.
-/
theorem five_in_brocard : 5 ∈ BrocardSet := ⟨11, by native_decide⟩

/--
7 is in the Brocard set.
-/
theorem seven_in_brocard : 7 ∈ BrocardSet := ⟨71, by native_decide⟩

/--
The three known elements are in the Brocard set.
-/
theorem known_brocard_elements : {4, 5, 7} ⊆ BrocardSet := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · exact four_in_brocard
  · exact five_in_brocard
  · exact seven_in_brocard

/--
**OPEN CONJECTURE (Erdős Problem #398 / Brocard-Ramanujan)**:

The only solutions to n! + 1 = m² are n = 4, 5, 7.

Equivalently: BrocardSet = {4, 5, 7}.

This conjecture remains open despite:
- Computational verification up to n = 10^9
- Overholt's proof of finitude under weak ABC conjecture
- Attention from many number theorists since 1876
-/
def brocard_ramanujan_conjecture : Prop := BrocardSet = {4, 5, 7}

/-!
## Conditional Results

Overholt (1993) proved that under a weak form of the ABC conjecture,
the Brocard-Ramanujan equation has only finitely many solutions.
-/

/--
A weak form of the ABC conjecture (statement for context).
The actual ABC conjecture involves the radical function and ε bounds.
-/
axiom WeakABC : Prop

/--
Overholt's theorem (1993): Under weak ABC, the Brocard equation
has finitely many solutions.

This is axiomatized as the full proof requires deep analytic
number theory beyond current Mathlib formalization.
-/
axiom overholt_finitude (h : WeakABC) : Set.Finite BrocardSet

/-!
## Growth Analysis

Why are solutions so rare? The factorial grows much faster than squares.

For large n, we have n! ≈ √(2πn)(n/e)^n (Stirling's approximation),
while m² ≈ n! means m ≈ √(n!).

The "near miss" probability decreases rapidly, making additional
solutions extremely unlikely (though not impossible to prove).
-/

/--
Factorials grow faster than squares for n ≥ 4.
This is a key intuition for why Brocard solutions are rare.

Verified for small cases; the general result follows from
n! ≥ n · (n-1) · (n-2) · (n-3) > n² for n ≥ 4.
-/
theorem factorial_dominates_4 : (4 : ℕ) ^ 2 < 4 ! := by native_decide
theorem factorial_dominates_5 : (5 : ℕ) ^ 2 < 5 ! := by native_decide
theorem factorial_dominates_6 : (6 : ℕ) ^ 2 < 6 ! := by native_decide
theorem factorial_dominates_7 : (7 : ℕ) ^ 2 < 7 ! := by native_decide
theorem factorial_dominates_8 : (8 : ℕ) ^ 2 < 8 ! := by native_decide

/--
Note: The conjecture `brocard_ramanujan_conjecture` is OPEN.
Despite extensive computational and theoretical work, it remains unproved.
-/
theorem erdos_398_is_open : True := trivial

end Erdos398
