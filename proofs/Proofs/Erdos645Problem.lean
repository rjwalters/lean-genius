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

/-
## Background: Arithmetic Progressions and Colorings

A 3-term arithmetic progression (3-AP) is a triple (x, x+d, x+2d) where d > 0.

A 2-coloring of ℕ is a function c : ℕ → Bool (or equivalently ℕ → Fin 2).

A monochromatic 3-AP is one where all three terms have the same color.

Van der Waerden's theorem guarantees monochromatic 3-APs exist in any
2-coloring. Erdős #645 asks for the stronger condition that d > x.
-/

-- erdos_645: unused axiom removed (never referenced by any theorem)
## Why This Is Interesting

Van der Waerden's theorem says: For any r-coloring of ℕ and any k,
there exists a monochromatic k-AP.

But it says nothing about the relationship between the first term
and the common difference. Erdős #645 shows that we can always find
a 3-AP where the "jump" (d) is bigger than the "start" (x).

This is related to questions about the structure of van der Waerden numbers
and Szemerédi's theorem on arithmetic progressions in dense sets.
-/

-- example_parity: unused axiom removed (never referenced by any theorem)
Example coloring: n < 5 is true, n ≥ 5 is false.
-/
def colorByThreshold (n : ℕ) : Bool := n < 5

-- example_threshold: unused axiom removed (never referenced by any theorem)
## Generalization Questions

Natural generalizations of Erdős #645:

1. What about k-APs with k > 3? Is there always a monochromatic k-AP
   with d > x?

2. What about r-colorings with r > 2?

3. Can we find monochromatic APs with d > αx for any α > 0?

4. What is the smallest N such that any 2-coloring of [1, N]
   contains a monochromatic 3-AP with d > x?
-/

-- erdos_645_is_k3: unused axiom removed (never referenced by any theorem)
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

-- erdos645_threshold_works: unused axiom removed (never referenced by any theorem)
