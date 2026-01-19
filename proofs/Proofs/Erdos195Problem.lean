/-
Erdős Problem #195: Monotone Arithmetic Progressions in Permutations of ℤ

Source: https://erdosproblems.com/195
Status: OPEN

Statement:
What is the largest k such that in any permutation of ℤ there must exist
a monotone k-term arithmetic progression x₁ < x₂ < ... < xₖ?

Here "monotone" means the positions in the permutation are either
increasing (the values appear in the order they're listed) or decreasing.

Known Results:
- Geneson (2019): k ≤ 5
- Adenwalla (2022): k ≤ 4

Lower bounds:
- k ≥ 3 is trivially true (any three points form a 3-AP)
- So the answer is either 3 or 4

Related Problems:
- Problem #194: Asks about k-term APs with d|(a-d) condition
- Problem #196: Same question for permutations of ℕ instead of ℤ

References:
- [ErGr79] Erdős and Graham, "Old and new problems and results in combinatorial
           number theory"
- [Ge19] Geneson, "Forbidden arithmetic progressions in permutations of subsets
         of the integers", Discrete Math. (2019)
- [Ad22] Adenwalla, "Avoiding Monotone Arithmetic Progressions in Permutations
         of Integers", arXiv:2211.04451 (2022)
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs

open List

namespace Erdos195

/-
## Part I: Definitions
-/

/--
A permutation of ℤ is a bijection from ℤ to itself.
-/
def Permutation := ℤ ≃ ℤ

/--
An arithmetic progression of length k with first term a and common difference d.
-/
def ArithProg (a d : ℤ) (k : ℕ) : List ℤ :=
  (List.range k).map (fun i => a + d * i)

/--
A sequence is monotone increasing in a permutation if the positions
(the inverse permutation values) are strictly increasing.
That is, if π(x₁) < π(x₂) < ... < π(xₖ) where π is the permutation.
-/
def IsMonotoneIncreasing (π : Permutation) (xs : List ℤ) : Prop :=
  xs.Pairwise (fun x y => π x < π y)

/--
A sequence is monotone decreasing in a permutation if the positions
are strictly decreasing.
-/
def IsMonotoneDecreasing (π : Permutation) (xs : List ℤ) : Prop :=
  xs.Pairwise (fun x y => π x > π y)

/--
A sequence is monotone if it is either monotone increasing or decreasing.
-/
def IsMonotone (π : Permutation) (xs : List ℤ) : Prop :=
  IsMonotoneIncreasing π xs ∨ IsMonotoneDecreasing π xs

/--
There exists a monotone k-term AP in permutation π.
-/
def HasMonotoneAP (π : Permutation) (k : ℕ) : Prop :=
  ∃ (a d : ℤ), d ≠ 0 ∧ IsMonotone π (ArithProg a d k)

/--
**The Main Question:**
What is the largest k such that every permutation of ℤ has a monotone k-term AP?
-/
def maxMonotoneAPLength : ℕ := sorry  -- The answer is 3 or 4 (open)

/-
## Part II: Known Upper Bounds
-/

/--
**Geneson's Theorem (2019):**
Not every permutation of ℤ contains a monotone 6-term AP.
Equivalently: k ≤ 5.

Proof idea: Construct an explicit permutation avoiding monotone 6-APs.
-/
axiom geneson_upper_bound :
  ∃ (π : Permutation), ¬HasMonotoneAP π 6

/--
**Adenwalla's Improvement (2022):**
Not every permutation of ℤ contains a monotone 5-term AP.
Equivalently: k ≤ 4.

This improves Geneson's bound by one.
-/
axiom adenwalla_upper_bound :
  ∃ (π : Permutation), ¬HasMonotoneAP π 5

/-
## Part III: Lower Bounds
-/

/--
**Trivial Lower Bound:**
Every permutation of ℤ contains a monotone 3-term AP.

This follows from Ramsey theory: in any permutation, among any
three points in AP, they are either monotone or can be rearranged.
-/
axiom lower_bound_3 :
  ∀ (π : Permutation), HasMonotoneAP π 3

/--
**Current State of Knowledge:**
3 ≤ k ≤ 4

The exact value is unknown: is it 3 or 4?
-/
axiom current_bounds :
  3 ≤ maxMonotoneAPLength ∧ maxMonotoneAPLength ≤ 4

/-
## Part IV: Related Questions
-/

/--
**Problem #196 (ℕ version):**
Same question for permutations of ℕ instead of ℤ.
This is a related but distinct problem.
-/
def maxMonotoneAPLength_N : ℕ := sorry

/--
**Relationship between ℤ and ℕ versions:**
The ℕ version may have different bounds since ℕ is one-sided infinite.
-/
axiom Z_N_relationship :
  maxMonotoneAPLength_N ≤ maxMonotoneAPLength

/-
## Part V: Connection to van der Waerden
-/

/--
**Van der Waerden's Theorem:**
For any finite coloring of ℕ, there exist arbitrarily long monochromatic APs.

This is different from our problem:
- VdW: Colors are arbitrary, APs found by value
- Our problem: "Color" by position, APs found by monotonicity
-/

/--
The key difference: in our problem, we don't require the AP to be
"monochromatic" (all in same color/region), but rather "monotone"
(positions increasing or decreasing).
-/

/-
## Part VI: Open Questions
-/

/--
**Main Open Question:**
Is every permutation of ℤ guaranteed to contain a monotone 4-term AP?

If yes, then k = 4.
If no, then k = 3.
-/
def erdos195_main_question : Prop :=
  ∀ (π : Permutation), HasMonotoneAP π 4

/--
**Structural Question:**
What structural properties of a permutation determine whether it
avoids monotone k-APs?
-/

/--
**Construction Question:**
Can we explicitly construct a permutation avoiding monotone 4-APs?
Adenwalla showed one avoiding monotone 5-APs.
-/

/-
## Part VII: Summary
-/

/--
**Erdős Problem #195: OPEN**

Question: What is the largest k such that every permutation of ℤ
contains a monotone k-term AP?

Known: 3 ≤ k ≤ 4
- Lower bound 3: Trivial
- Upper bound 4: Adenwalla (2022), improving Geneson (2019)'s bound of 5

The gap between 3 and 4 remains open.
-/
theorem erdos_195 :
    (∀ π : Permutation, HasMonotoneAP π 3) ∧
    (∃ π : Permutation, ¬HasMonotoneAP π 5) := by
  constructor
  · exact lower_bound_3
  · exact adenwalla_upper_bound

/--
**Current State:**
- If erdos195_main_question is true, then k = 4
- If erdos195_main_question is false, then k = 3
-/
theorem erdos_195_dichotomy :
    (erdos195_main_question → maxMonotoneAPLength = 4) ∧
    (¬erdos195_main_question → maxMonotoneAPLength = 3) := by
  constructor
  · intro _
    sorry  -- Would follow from definition
  · intro _
    sorry  -- Would follow from definition

end Erdos195
