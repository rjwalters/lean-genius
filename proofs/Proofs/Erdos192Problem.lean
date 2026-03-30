/-
Erdős Problem #192: Three-Term Arithmetic Progressions in Unit Vector Sequences

Source: https://erdosproblems.com/192
Status: SOLVED

Statement:
Let A = {a₁, a₂, ...} ⊂ ℝ^d be an infinite sequence where each successive difference
a_{i+1} - a_i is a positive unit vector (of the form (0,...,1,...,0)).
For which d must A contain a three-term arithmetic progression?

Answer: True for d ≤ 3, false for d ≥ 4.

The problem is equivalent to one on "abelian squares" in combinatorics on words.
Keränen (1992) constructed an infinite abelian-square-free word on 4 letters,
giving the counterexample for d = 4.

References:
- Erdős (1961): Original formulation
- Keränen (1992): Counterexample for d ≥ 4
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos192

/-
## Part I: Setup
-/

/--
A unit vector step sequence in ℤ^d: each step is a standard basis vector eᵢ.
We represent a walk as a sequence of directions (which coordinate to increment).
-/
def UnitVectorWalk (d : ℕ) := ℕ → Fin d

/--
The position after n steps of a unit vector walk starting at the origin.
Position at step n is the sum of unit vectors along each chosen direction.
-/
def walkPosition (d : ℕ) (w : UnitVectorWalk d) (n : ℕ) : Fin d → ℤ :=
  fun i => (Finset.range n).sum (fun k => if w k = i then 1 else 0)

/--
A three-term arithmetic progression in the walk: positions at indices i < j < k
with walkPosition(j) - walkPosition(i) = walkPosition(k) - walkPosition(j).
-/
def HasThreeTermAP (d : ℕ) (w : UnitVectorWalk d) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧
    ∀ c : Fin d, walkPosition d w j c - walkPosition d w i c =
                 walkPosition d w k c - walkPosition d w j c

/-
## Part II: The d ≤ 3 Case
-/

/--
**Theorem (d ≤ 3)**: Every infinite unit vector walk in ℤ^d for d ≤ 3
contains a three-term arithmetic progression.

This follows from the fact that every infinite word over a 3-letter alphabet
contains an abelian square.
-/
axiom three_term_ap_low_dim (d : ℕ) (hd : d ≤ 3) (w : UnitVectorWalk d) :
    HasThreeTermAP d w

/-
## Part III: The d ≥ 4 Counterexample
-/

/--
**Keränen's Theorem (1992)**: There exists an infinite unit vector walk in ℤ^4
with no three-term arithmetic progression.

Keränen constructed an infinite abelian-square-free word over a 4-letter alphabet,
which translates to a walk in ℤ^4 avoiding three-term APs.
-/
axiom keranen_counterexample :
    ∃ w : UnitVectorWalk 4, ¬HasThreeTermAP 4 w

/-
## Part IV: Complete Classification
-/

/--
**Erdős Problem #192: SOLVED**

The critical dimension is d = 3:
- d ≤ 3: every walk must contain a three-term AP
- d ≥ 4: there exist walks avoiding three-term APs

The threshold d = 3 corresponds to the fact that every infinite word over
3 letters contains an abelian square, but abelian-square-free words exist
over 4 letters.
-/
theorem erdos_192 :
    (∀ (w : UnitVectorWalk 3), HasThreeTermAP 3 w) ∧
    (∃ (w : UnitVectorWalk 4), ¬HasThreeTermAP 4 w) :=
  ⟨three_term_ap_low_dim 3 (by omega), keranen_counterexample⟩

end Erdos192
