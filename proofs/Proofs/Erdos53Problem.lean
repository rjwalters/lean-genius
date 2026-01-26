/-!
# Erdős Problem 53: Sums and Products of Distinct Elements

*Reference:* [erdosproblems.com/53](https://www.erdosproblems.com/53)

Let `A` be a finite set of integers. Is it true that for every `k`, if `|A|`
is sufficiently large (depending on `k`), then there are at least `|A|^k`
integers representable as sums or products of distinct elements of `A`?

This problem was posed by Erdős and Szemerédi (1983) and resolved affirmatively
by Chang (2003). Erdős and Szemerédi also proved an upper bound:
there exist arbitrarily large sets `A` where the count of representable
integers is at most `exp(c · (log |A|)² · log log |A|)`.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
## Section 1: Subset sums and products

We define the set of integers representable as a sum of distinct elements
of a finite set, and similarly for products.
-/

namespace Erdos53

open Finset

/-- The set of all sums of distinct elements (subsets) of a finite integer set. -/
def subsetSums (A : Finset ℤ) : Finset ℤ :=
  (A.powerset).image (fun S => S.sum id)

/-- The set of all products of distinct elements (nonempty subsets) of a finite integer set. -/
def subsetProducts (A : Finset ℤ) : Finset ℤ :=
  (A.powerset.filter (fun S => S.Nonempty)).image (fun S => S.prod id)

/-- The set of integers representable as either a sum or product of distinct elements. -/
def sumsOrProducts (A : Finset ℤ) : Finset ℤ :=
  subsetSums A ∪ subsetProducts A

/-!
## Section 2: The Erdős–Szemerédi conjecture (Problem 53)

For every `k`, if `|A|` is large enough, then `|sumsOrProducts A| ≥ |A|^k`.
-/

/-- Erdős Problem 53: For every k, there exists N₀ such that for any finite
    set A of integers with |A| ≥ N₀, the number of integers representable
    as sums or products of distinct elements of A is at least |A|^k. -/
def ErdosProblem53 : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ →
      (sumsOrProducts A).card ≥ A.card ^ k

/-!
## Section 3: Chang's theorem (2003)

Chang proved the conjecture affirmatively, resolving Problem 53.
-/

/-- Chang's theorem (2003): Erdős Problem 53 holds. -/
axiom chang_theorem : ErdosProblem53

/-!
## Section 4: The Erdős–Szemerédi upper bound

Erdős and Szemerédi showed that arbitrarily large sets exist where the count
of representable integers is bounded by `exp(c · (log |A|)² · log log |A|)`.
This shows the growth cannot be *too* fast.
-/

/-- There exists a constant c > 0 and arbitrarily large sets A where the
    number of representable integers is at most exp(c · (log |A|)² · log log |A|). -/
axiom erdos_szemeredi_upper_bound :
  ∃ c : ℕ, c ≥ 1 ∧
    ∀ N : ℕ, ∃ A : Finset ℤ, A.card ≥ N ∧
      (sumsOrProducts A).card ≤ A.card ^ (c * (Nat.log 2 A.card + 1))

/-!
## Section 5: Sum-product phenomena connection

This problem is closely related to the Erdős–Szemerédi sum-product conjecture
(Problem 52), which concerns `|A + A| + |A · A|` for a single set `A`.
The distinction is that Problem 53 asks about sums and products of *distinct*
elements (subsets), while Problem 52 concerns pairwise sums and products.
-/

/-- The sumset A + A. -/
def sumset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The product set A · A. -/
def productset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 * p.2)

/-- The sum-product conjecture (Problem 52) asserts that for every ε > 0,
    |A+A| + |A·A| ≥ |A|^{2-ε} for large enough |A|.
    This is a related but distinct problem. -/
def SumProductConjecture : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ →
      (sumset A).card + (productset A).card ≥ A.card ^ 2 / (A.card * εNum / εDen + 1)

/-!
## Section 6: Counting distinct-element representations

We can count how many integers have a representation as a sum of distinct
elements versus a product of distinct elements.
-/

/-- Count of integers representable as subset sums. -/
def subsetSumCount (A : Finset ℤ) : ℕ := (subsetSums A).card

/-- Count of integers representable as subset products. -/
def subsetProductCount (A : Finset ℤ) : ℕ := (subsetProducts A).card

/-- The union count is at least the subset sum count. -/
axiom sumsOrProducts_ge_sums (A : Finset ℤ) :
    (sumsOrProducts A).card ≥ subsetSumCount A

/-- The union count is at least the subset product count. -/
axiom sumsOrProducts_ge_products (A : Finset ℤ) :
    (sumsOrProducts A).card ≥ subsetProductCount A

end Erdos53
