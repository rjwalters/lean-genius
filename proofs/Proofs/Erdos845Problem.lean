/-
Erdős Problem #845: Sums of 3-Smooth Numbers with Bounded Ratio

Let C > 0. Consider integers n expressible as n = b₁ + ... + bₜ where:
- Each bᵢ = 2^kᵢ · 3^lᵢ (3-smooth numbers)
- b₁ < b₂ < ... < bₜ (strictly increasing)
- bₜ ≤ C · b₁ (bounded ratio between largest and smallest)

Erdős asked: Does this set of integers have density 0?

**Answer**: NO (DISPROVED)
- van Doorn and Everts (2025) proved ALL integers can be written this way with C = 6
- Therefore the set has density 1, not 0

**Bounds on optimal C**:
- Erdős and Lewin (1996): C > 2 is necessary
- van Doorn and Everts (2025): C ≥ 3 is necessary, C = 6 suffices
- Conjectured: C > 3¹⁰/2¹⁴ ≈ 3.604 may suffice

Reference: https://erdosproblems.com/845
-/

import Mathlib

namespace Erdos845

open Finset

/-
## 3-Smooth Numbers

A positive integer is 3-smooth if its only prime factors are 2 and 3.
These are exactly the numbers of the form 2^k · 3^l.
-/

/--
`isThreeSmooth n` holds if n is a positive 3-smooth number,
meaning n = 2^k · 3^l for some k, l ≥ 0.
-/
def isThreeSmooth (n : ℕ) : Prop :=
  ∃ k l : ℕ, n = 2 ^ k * 3 ^ l

/--
The function mapping pairs (k, l) to 3-smooth numbers 2^k · 3^l.
This parametrizes all positive 3-smooth numbers.
-/
def smoothNum (k l : ℕ) : ℕ := 2 ^ k * 3 ^ l

/-
## Bounded-Ratio Representations

We say an integer n has a C-bounded representation if it can be written
as a sum of distinct 3-smooth numbers b₁ < ... < bₜ with bₜ ≤ C · b₁.
-/

/--
`hasBoundedRep C n` holds if n can be written as a sum of distinct
3-smooth numbers b₁ < ... < bₜ where the ratio bₜ/b₁ is at most C.
-/
def hasBoundedRep (C : ℝ) (n : ℕ) : Prop :=
  ∃ (B : Finset (ℕ × ℕ)) (hne : B.Nonempty),
    let values := B.image (fun p => smoothNum p.1 p.2)
    n = values.sum id ∧
    (values.max' (hne.image _) : ℝ) ≤ C * (values.min' (hne.image _) : ℝ)

/-
## The Original Conjecture (DISPROVED)

Erdős conjectured that for any C > 0, the set of integers with
C-bounded representations has natural density 0.
-/

/--
The original Erdős conjecture: for any C > 0, the set of integers
expressible as C-bounded sums of 3-smooth numbers has density 0.

This conjecture is FALSE - van Doorn and Everts (2025) showed that
with C = 6, ALL positive integers have such representations.
-/
def erdosConjecture : Prop :=
  ∀ C > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ M ≥ N,
    ({n : ℕ | n < M ∧ hasBoundedRep C n}.ncard : ℝ) / M < ε

/-
## The Disproof

van Doorn and Everts (2025) proved that every positive integer has
a 6-bounded representation, completely disproving Erdős's conjecture.
-/

/--
van Doorn and Everts (2025): Every positive integer can be written as
a sum of distinct 3-smooth numbers b₁ < ... < bₜ with bₜ < 6b₁.

This disproves Erdős's conjecture: the set has density 1, not 0.

Reference: W. van Doorn and A. Everts, "Smooth sums with small spacings",
arXiv:2511.04585 (2025).
-/
axiom vanDoornEverts_universal : ∀ n : ℕ, 0 < n → hasBoundedRep 6 n

/--
Corollary: Erdős's conjecture is false.
Since all positive integers have 6-bounded representations, the set
has density 1, not 0 as conjectured.
-/
axiom erdosConjecture_false : ¬erdosConjecture

/-
## Lower Bounds on the Optimal Constant

What is the smallest C such that all large integers have C-bounded
representations? Call this optimal constant C*.
-/

/--
Erdős and Lewin (1996): The optimal constant C* satisfies C* > 2.
There exist arbitrarily large integers that cannot be written as
2-bounded sums of distinct 3-smooth numbers.

Reference: Erdős, P. and Lewin, M., "d-complete sequences of integers",
Math. Comp. (1996), 837-840.
-/
axiom erdosLewin_lowerBound : ∃ᶠ n in Filter.atTop, ¬hasBoundedRep 2 n

/--
van Doorn and Everts (2025): The optimal constant C* satisfies C* ≥ 3.
There exist arbitrarily large integers that cannot be written as
sums with ratio less than 3.

Reference: W. van Doorn and A. Everts, "Smooth sums with small spacings",
arXiv:2511.04585 (2025).
-/
axiom vanDoornEverts_lowerBound : ∃ᶠ n in Filter.atTop, ¬hasBoundedRep 3 n

/-
## Related Result: The "Silly Conjecture"

Erdős also made a simpler conjecture that every integer can be written
as a sum of distinct 3-smooth numbers where no summand divides another.
This was quickly proved by Jansen and others using induction.
-/

/--
A set of 3-smooth numbers is non-divisibility-free if no element
divides any other element in the set.
-/
def nonDivisible (B : Finset (ℕ × ℕ)) : Prop :=
  ∀ p q : ℕ × ℕ, p ∈ B → q ∈ B → p ≠ q →
    ¬(smoothNum p.1 p.2 ∣ smoothNum q.1 q.2)

/--
Every positive integer can be written as a sum of distinct 3-smooth
numbers where no summand divides any other (Jansen et al.).

This is the "silly conjecture" that Erdős mentioned, which turned out
to have a simple inductive proof.
-/
axiom sillyConjecture_true : ∀ n : ℕ, 0 < n →
  ∃ (B : Finset (ℕ × ℕ)), B.Nonempty ∧
    n = ∑ p ∈ B, smoothNum p.1 p.2 ∧
    nonDivisible B

/-
## Computational Examples

Small examples showing 3-smooth representations.
-/

/-- 1 = 2^0 · 3^0 is 3-smooth -/
theorem one_threeSmooth : isThreeSmooth 1 := ⟨0, 0, by norm_num⟩

/-- 6 = 2^1 · 3^1 is 3-smooth -/
theorem six_threeSmooth : isThreeSmooth 6 := ⟨1, 1, by norm_num⟩

/-- 12 = 2^2 · 3^1 is 3-smooth -/
theorem twelve_threeSmooth : isThreeSmooth 12 := ⟨2, 1, by norm_num⟩

/-- 7 = 1 + 2 + 4 = 2^0·3^0 + 2^1·3^0 + 2^2·3^0, a sum of 3-smooth numbers -/
example : 7 = smoothNum 0 0 + smoothNum 1 0 + smoothNum 2 0 := by
  simp only [smoothNum]
  norm_num

/-- 5 = 2 + 3, a sum of distinct 3-smooth numbers -/
example : 5 = smoothNum 1 0 + smoothNum 0 1 := by
  simp only [smoothNum]
  norm_num

end Erdos845
