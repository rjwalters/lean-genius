/-!
# Erdős Problem #503: Maximum Isosceles Sets in Rⁿ

**Source:** [erdosproblems.com/503](https://erdosproblems.com/503)
**Status:** OPEN (general n)

## Statement

What is the maximum size of A ⊆ ℝⁿ such that every three points
from A form an isosceles triangle (at least two pairwise distances equal)?

## Known Results

- n = 2: answer is 6 (Kelly [ErKe47], alt. proof by Kovács [Ko24c])
- n = 3: answer is 8 (Croft [Cr62])
- Upper bound: |A| ≤ C(n+2, 2) (Blokhuis [Bl84])
- Lower bound: |A| ≥ C(n+1, 2) (Alweiss, via e_i + e_j vectors)
- Improved lower: |A| ≥ C(n+1, 2) + 1 (Weisenberg)

## Approach

We formalize the isosceles property, the exact answers for small
dimensions, and the general bounds as axioms.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos503

/-! ## Part I: Isosceles Sets -/

/--
A finite set A of points in ℝⁿ (represented abstractly) is isosceles
if every triple of distinct points has at least two equal pairwise
distances. We work with an abstract metric space.
-/
def IsIsoscelesSet {α : Type*} [Dist α] (A : Finset α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
    x ≠ y → y ≠ z → x ≠ z →
    dist x y = dist y z ∨ dist y z = dist x z ∨ dist x y = dist x z

/--
The maximum isosceles set size in dimension n.
-/
def maxIsoscelesSize (n : ℕ) : ℕ := sorry

/-! ## Part II: Exact Results for Small Dimensions -/

/--
**Kelly's Theorem [ErKe47]:**
The maximum isosceles set in ℝ² has size 6.
An alternative proof was given by Kovács [Ko24c].
-/
axiom kelly_R2 : maxIsoscelesSize 2 = 6

/--
**Croft's Theorem [Cr62]:**
The maximum isosceles set in ℝ³ has size 8.
-/
axiom croft_R3 : maxIsoscelesSize 3 = 8

/-! ## Part III: General Bounds -/

/--
**Blokhuis Upper Bound [Bl84]:**
For all n, the maximum isosceles set size is at most C(n+2, 2).
-/
axiom blokhuis_upper_bound :
  ∀ n : ℕ, maxIsoscelesSize n ≤ Nat.choose (n + 2) 2

/--
**Alweiss Lower Bound:**
The set of vectors e_i + e_j (distinct coordinate vectors in ℝⁿ⁺¹)
gives an isosceles set of size C(n+1, 2) that embeds in ℝⁿ.
-/
axiom alweiss_lower_bound :
  ∀ n : ℕ, n ≥ 2 → Nat.choose (n + 1) 2 ≤ maxIsoscelesSize n

/--
**Weisenberg Improvement:**
One additional point can be added to Alweiss's construction,
giving a lower bound of C(n+1, 2) + 1.
-/
axiom weisenberg_improvement :
  ∀ n : ℕ, n ≥ 2 → Nat.choose (n + 1) 2 + 1 ≤ maxIsoscelesSize n

/-! ## Part IV: The Gap -/

/--
**The remaining gap:**
For general n, we have C(n+1, 2) + 1 ≤ maxIsoscelesSize(n) ≤ C(n+2, 2).
The exact value is unknown for n ≥ 4.
-/
theorem erdos_503_bounds :
    ∀ n : ℕ, n ≥ 2 →
      Nat.choose (n + 1) 2 + 1 ≤ maxIsoscelesSize n ∧
      maxIsoscelesSize n ≤ Nat.choose (n + 2) 2 :=
  fun n hn => ⟨weisenberg_improvement n hn, blokhuis_upper_bound n⟩

/--
**Consistency check: n = 2.**
C(3, 2) + 1 = 4 ≤ 6 ≤ C(4, 2) = 6. Both bounds match.
-/
example : Nat.choose 3 2 + 1 ≤ 6 ∧ 6 ≤ Nat.choose 4 2 := by norm_num

/--
**Consistency check: n = 3.**
C(4, 2) + 1 = 7 ≤ 8 ≤ C(5, 2) = 10.
-/
example : Nat.choose 4 2 + 1 ≤ 8 ∧ 8 ≤ Nat.choose 5 2 := by norm_num

/-! ## Part V: Summary -/

/--
**Summary:**
Erdős Problem #503 asks for the maximum isosceles set size in ℝⁿ.
Exact: f(2) = 6, f(3) = 8. General: C(n+1,2) + 1 ≤ f(n) ≤ C(n+2,2).
The exact answer for n ≥ 4 remains open.
-/
theorem erdos_503_summary :
    maxIsoscelesSize 2 = 6 ∧ maxIsoscelesSize 3 = 8 :=
  ⟨kelly_R2, croft_R3⟩

end Erdos503
