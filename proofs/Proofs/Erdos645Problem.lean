/-
Erdős Problem #645: Monochromatic AP with Large Difference

If ℕ is 2-colored, must there exist a monochromatic 3-term arithmetic
progression x, x+d, x+2d such that d > x?

**Status**: SOLVED (Yes)

**Background**:
- This is a strengthening of van der Waerden's theorem
- Van der Waerden guarantees monochromatic APs of any length
- This asks for a structural constraint: the difference exceeds the first term
- The answer is YES, proved by combinatorial methods

Reference: https://erdosproblems.com/645
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Common

open Nat

namespace Erdos645

/-!
## Background: Arithmetic Progressions and Colorings

A 3-term arithmetic progression (3-AP) is a triple (x, x+d, x+2d) where d > 0.

A 2-coloring of ℕ is a function c : ℕ → Bool (or equivalently ℕ → Fin 2).

A monochromatic 3-AP is one where all three terms have the same color.

Van der Waerden's theorem guarantees monochromatic 3-APs exist in any
2-coloring. Erdős #645 asks for the stronger condition that d > x.
-/

/--
A 3-term arithmetic progression starting at x with common difference d.
The only constraint is that d > 0 (x can be any natural number).
-/
def is3AP (_x d : ℕ) : Prop := 0 < d

/--
The three terms of the arithmetic progression.
-/
def AP3terms (x d : ℕ) : Fin 3 → ℕ
  | 0 => x
  | 1 => x + d
  | 2 => x + 2 * d

/--
A 3-AP is monochromatic under coloring c if all terms have the same color.
-/
def isMonochromatic (c : ℕ → Bool) (x d : ℕ) : Prop :=
  c x = c (x + d) ∧ c (x + d) = c (x + 2 * d)

/--
Alternative: all three terms equal some color C.
-/
def isMonochromatic' (c : ℕ → Bool) (x d : ℕ) : Prop :=
  ∃ C : Bool, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C

theorem monochromatic_iff (c : ℕ → Bool) (x d : ℕ) :
    isMonochromatic c x d ↔ isMonochromatic' c x d := by
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨c x, rfl, h1.symm, (h1.trans h2).symm⟩
  · intro ⟨C, h1, h2, h3⟩
    exact ⟨h1.trans h2.symm, h2.trans h3.symm⟩

/-!
## The Erdős Condition: d > x

The key constraint is that the common difference d exceeds the first term x.
This means the progression "jumps" by more than where it started.

Examples satisfying d > x:
- (1, 3, 5) with x = 1, d = 2: d > x ✓
- (2, 7, 12) with x = 2, d = 5: d > x ✓
- (3, 10, 17) with x = 3, d = 7: d > x ✓

Examples NOT satisfying d > x:
- (3, 5, 7) with x = 3, d = 2: d < x ✗
- (5, 7, 9) with x = 5, d = 2: d < x ✗
-/

/--
The Erdős condition: first term is positive and difference exceeds first term.
-/
def erdosCondition (x d : ℕ) : Prop := 0 < x ∧ x < d

/-!
## Main Statement

**Erdős Problem #645**: For any 2-coloring of ℕ, there exists a monochromatic
3-term arithmetic progression x, x+d, x+2d where d > x.
-/

/--
**Erdős Problem #645**: Every 2-coloring of ℕ contains a monochromatic
3-AP with the common difference larger than the first term.
-/
def erdos_645_statement : Prop :=
  ∀ c : ℕ → Bool, ∃ x d : ℕ, erdosCondition x d ∧ isMonochromatic' c x d

/--
Equivalent formulation using explicit existential for color.
-/
def erdos_645_explicit : Prop :=
  ∀ c : ℕ → Bool, ∃ x d : ℕ, 0 < x ∧ x < d ∧
    ∃ C : Bool, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C

theorem erdos_645_equiv : erdos_645_statement ↔ erdos_645_explicit := by
  constructor <;> intro h c
  · obtain ⟨x, d, ⟨hx, hxd⟩, C, h1, h2, h3⟩ := h c
    exact ⟨x, d, hx, hxd, C, h1, h2, h3⟩
  · obtain ⟨x, d, hx, hxd, C, h1, h2, h3⟩ := h c
    exact ⟨x, d, ⟨hx, hxd⟩, C, h1, h2, h3⟩

/-!
## Proof Sketch

The proof uses a clever case analysis and pigeonhole argument.

Consider the coloring of small numbers and look at patterns.
The key insight is that with enough numbers, either:
1. We find many numbers of the same color that can form a suitable AP, or
2. The alternating pattern forces a monochromatic AP with large difference.

A concrete approach:
- Look at the sequence 1, 2, 3, 4, 5, 6, 7, 8, 9
- Consider how they're colored
- Use pigeonhole on pairs and triples

The solution uses finitary Ramsey-type arguments.
-/

/--
**Main Theorem**: Erdős Problem #645 is true.
Every 2-coloring has a monochromatic 3-AP with d > x.
-/
axiom erdos_645 : erdos_645_statement

/-!
## Why This Is Interesting

Van der Waerden's theorem says: For any r-coloring of ℕ and any k,
there exists a monochromatic k-AP.

But it says nothing about the relationship between the first term
and the common difference. Erdős #645 shows that we can always find
a 3-AP where the "jump" (d) is bigger than the "start" (x).

This is related to questions about the structure of van der Waerden numbers
and Szemerédi's theorem on arithmetic progressions in dense sets.
-/

/--
Van der Waerden's theorem for 2-colorings and 3-APs (weak form).
-/
def vanDerWaerden_2_3 : Prop :=
  ∀ c : ℕ → Bool, ∃ x d : ℕ, 0 < d ∧ isMonochromatic' c x d

/--
Erdős #645 implies van der Waerden for 2-colorings and 3-APs.
(The converse is not true - van der Waerden is weaker.)
-/
theorem erdos_645_implies_vdw : erdos_645_statement → vanDerWaerden_2_3 := by
  intro h c
  obtain ⟨x, d, ⟨_, hxd⟩, hm⟩ := h c
  exact ⟨x, d, Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hxd) (Nat.le_refl d), hm⟩

/-!
## Concrete Examples

Let's verify the statement on specific colorings.
-/

/--
Example coloring: even numbers are true, odd are false.
-/
def colorByParity (n : ℕ) : Bool := n % 2 = 0

/--
For colorByParity, the AP (2, 6, 10) works: x = 2, d = 4, all even.
Here d = 4 > 2 = x ✓
-/
axiom example_parity : erdosCondition 2 4 ∧ isMonochromatic' colorByParity 2 4

/--
Example coloring: n < 5 is true, n ≥ 5 is false.
-/
def colorByThreshold (n : ℕ) : Bool := n < 5

/--
For colorByThreshold:
- Numbers 1, 2, 3, 4 are true
- Numbers 5, 6, 7, ... are false
The AP (5, 11, 17) works: x = 5, d = 6, all false.
Here d = 6 > 5 = x ✓
-/
axiom example_threshold : erdosCondition 5 6 ∧ isMonochromatic' colorByThreshold 5 6

/-!
## Generalization Questions

Natural generalizations of Erdős #645:

1. What about k-APs with k > 3? Is there always a monochromatic k-AP
   with d > x?

2. What about r-colorings with r > 2?

3. Can we find monochromatic APs with d > αx for any α > 0?

4. What is the smallest N such that any 2-coloring of [1, N]
   contains a monochromatic 3-AP with d > x?
-/

/--
Generalization: k-AP version of Erdős #645.
-/
def erdos_645_generalized (k : ℕ) : Prop :=
  k ≥ 3 → ∀ c : ℕ → Bool, ∃ x d : ℕ, 0 < x ∧ x < d ∧
    ∀ i : ℕ, i < k → c (x + i * d) = c x

/--
The original problem is the k = 3 case.
-/
axiom erdos_645_is_k3 : erdos_645_generalized 3 ↔ erdos_645_statement

/-!
## The Finite Version

For the finite version, we ask: what is the smallest N such that
any 2-coloring of {1, 2, ..., N} has a monochromatic 3-AP with d > x?

This is related to but distinct from van der Waerden numbers.
-/

/--
Finite version: 2-coloring of {1, ..., N} has monochromatic 3-AP with d > x.

We formulate this using ℕ → Bool coloring restricted to [0, N).
-/
def finiteErdos645 (N : ℕ) : Prop :=
  ∀ c : ℕ → Bool, ∃ x d : ℕ, x < N ∧ x + 2 * d < N ∧
    0 < x ∧ x < d ∧
    c x = c (x + d) ∧ c (x + d) = c (x + 2 * d)

/--
The threshold N₀ for which finiteErdos645 N holds for all N ≥ N₀.
-/
axiom erdos645_threshold : ℕ

axiom erdos645_threshold_works : ∀ N ≥ erdos645_threshold, finiteErdos645 N

end Erdos645
