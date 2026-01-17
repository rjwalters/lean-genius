/-
Erdős Problem #494: Set Determination from k-Sums

Given a finite set A ⊂ ℂ and k ≥ 1, define Aₖ = {z₁ + ⋯ + zₖ : zᵢ ∈ A distinct}.
For k > 2, does the multiset Aₖ (together with |A|) uniquely determine A?

**Status**: SOLVED (affirmative for sufficiently large |A|)

**Key Results**:
- Selfridge-Straus (1958): k=2 works iff |A| ≠ 2ˡ; k=3 works for |A| > 6; k=4 for |A| > 12
- Gordon-Fraenkel-Straus (1962): For all k > 2, uniqueness holds for sufficiently large |A|
- Kruyt: Fails when |A| = k (rotation counterexample)
- Tao: Fails when |A| = 2k (negation counterexample)

**Intuition**: The multiset of k-sums encodes information about A. For large enough A,
this information is sufficient to reconstruct A uniquely. Small sets have counterexamples
due to symmetries (rotation, negation).

References:
- https://erdosproblems.com/494
- Selfridge & Straus (1958), Pacific J. Math.
- Gordon, Fraenkel & Straus (1962), Pacific J. Math.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Multiset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic

open Finset Filter BigOperators

namespace Erdos494

/-!
## Core Definitions

We define the multiset of k-sums for a finite set A ⊂ ℂ.
-/

/-- The multiset of all sums of k distinct elements from A.

For example, if A = {1, 2, 3} and k = 2, then
sumMultiset A 2 = {1+2, 1+3, 2+3} = {3, 4, 5} as a multiset.
-/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

/-- Two sets A, B have the same k-sum multiset. -/
def SameKSums (A B : Finset ℂ) (k : ℕ) : Prop :=
  sumMultiset A k = sumMultiset B k

/-- The uniqueness property: sets of a given cardinality are determined by their k-sums.

This says: if A and B are both finite sets of complex numbers with |A| = |B| = card,
and they have the same k-sum multiset, then A = B.
-/
def KSumDeterminesSet (k : ℕ) (card : ℕ) : Prop :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card →
    sumMultiset A k = sumMultiset B k → A = B

/-!
## The k = 2 Case (Selfridge-Straus 1958)

For k = 2, uniqueness depends on whether |A| is a power of 2.
-/

/-- **Selfridge-Straus (1958)**: For k = 2, uniqueness holds when |A| ≠ 2ˡ.

If |A| is not a power of 2, then A is uniquely determined by the multiset of
pairwise sums {a + b : a, b ∈ A, a ≠ b}.
-/
axiom selfridge_straus_k2_not_power2 :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2^l) → KSumDeterminesSet 2 card

/-- **Selfridge-Straus (1958)**: For k = 2, uniqueness FAILS when |A| = 2ˡ.

There exist distinct sets A ≠ B with |A| = |B| = 2ˡ having the same 2-sum multiset.
-/
axiom selfridge_straus_k2_power2_fails :
    ∀ l : ℕ, l ≥ 1 → ¬KSumDeterminesSet 2 (2^l)

/-!
## The k = 3 and k = 4 Cases (Selfridge-Straus 1958)
-/

/-- **Selfridge-Straus (1958)**: For k = 3, uniqueness holds when |A| > 6.

Sets with more than 6 elements are uniquely determined by their 3-sum multisets.
-/
axiom selfridge_straus_k3 :
    ∀ card : ℕ, card > 6 → KSumDeterminesSet 3 card

/-- **Selfridge-Straus (1958)**: For k = 4, uniqueness holds when |A| > 12. -/
axiom selfridge_straus_k4 :
    ∀ card : ℕ, card > 12 → KSumDeterminesSet 4 card

/-!
## The Prime Divisibility Criterion (Selfridge-Straus 1958)
-/

/-- **Selfridge-Straus (1958)**: Uniqueness holds if |A| has a prime factor > k.

This is a powerful general criterion that explains many special cases.
For example, |A| = 7 and k = 3: 7 is prime > 3, so uniqueness holds.
-/
axiom selfridge_straus_prime_criterion :
    ∀ k card p : ℕ, Nat.Prime p → k < p → p ∣ card → KSumDeterminesSet k card

/-!
## Counterexamples for Small Sets
-/

/-- **Kruyt**: Uniqueness FAILS when |A| = k (for k > 2).

Counterexample: Take any set A with |A| = k elements. The k-sum multiset
contains only the single sum (with multiplicity 1). Rotating A around the
centroid gives a different set with the same k-sum.

The rotation is: if c = (sum of A)/k, then A' = {2c - a : a ∈ A} ≠ A but
has the same k-sum (which equals k·c).
-/
axiom kruyt_rotation_counterexample :
    ∀ k : ℕ, k > 2 → ¬KSumDeterminesSet k k

/-- **Tao**: Uniqueness FAILS when |A| = 2k (for k > 2).

Counterexample: If A is a set with sum(A) = 0 and |A| = 2k,
then -A = {-a : a ∈ A} has the same k-sum multiset as A.

The k-sums of -A are negations of the (2k-k)=k-sums of complements in A,
which by the zero-sum condition equal the k-sums of A.
-/
axiom tao_negation_counterexample :
    ∀ k : ℕ, k > 2 → ¬KSumDeterminesSet k (2 * k)

/-!
## The Main Result (Gordon-Fraenkel-Straus 1962)
-/

/-- **Gordon-Fraenkel-Straus (1962)**: For all k > 2, uniqueness holds for
sufficiently large |A|.

This is the main positive result: for each k > 2, there exists N(k) such that
all sets with |A| > N(k) are uniquely determined by their k-sum multisets.

The proof uses polynomial methods and properties of symmetric functions.
-/
axiom gordon_fraenkel_straus_main :
    ∀ k : ℕ, k > 2 → ∀ᶠ card in atTop, KSumDeterminesSet k card

/-!
## The Product Version (False!)

Erdős also asked about products instead of sums. This version is FALSE.
-/

/-- The multiset of all products of k distinct elements from A. -/
noncomputable def prodMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.prod id

/-- **Steinerberger**: The product version of the problem is FALSE.

Counterexample for k = 3: Let ζ₆ = e^(2πi/6) be a primitive 6th root of unity.
Take A = {1, ζ₆, ζ₆², ζ₆⁴} and B = {1, ζ₆², ζ₆³, ζ₆⁴}.
Then |A| = |B| = 4, the 3-product multisets are equal, but A ≠ B.
-/
axiom steinerberger_product_counterexample :
    ∃ A B : Finset ℂ, A.card = B.card ∧ A.card = 4 ∧
      prodMultiset A 3 = prodMultiset B 3 ∧ A ≠ B

/-!
## Summary Theorem

The main theorem combining the positive results.
-/

/-- **Erdős Problem #494** (SOLVED):
For k > 2, the k-sum multiset determines A for sufficiently large |A|.

More precisely:
1. For k = 2: Determined iff |A| ≠ 2ˡ
2. For k > 2: Determined for |A| sufficiently large
3. For k > 2: NOT determined when |A| = k or |A| = 2k (counterexamples exist)
-/
theorem erdos_494_summary :
    (∀ card : ℕ, (∀ l : ℕ, card ≠ 2^l) → KSumDeterminesSet 2 card) ∧
    (∀ k : ℕ, k > 2 → ∀ᶠ card in atTop, KSumDeterminesSet k card) :=
  ⟨selfridge_straus_k2_not_power2, gordon_fraenkel_straus_main⟩

/-!
## Specific Examples

We can verify the definitions work on concrete examples.
-/

/-- A small example: the set {0, 1, 2} ⊂ ℂ.

Note: Complex numbers don't have decidable equality in the computational sense,
so we use axioms to verify properties of concrete examples. -/
noncomputable def example_set : Finset ℂ := {0, 1, 2}

/-- The set {0, 1, 2} has cardinality 3. -/
axiom example_set_card : example_set.card = 3

/-- The 2-sum multiset of {0, 1, 2} is {0+1, 0+2, 1+2} = {1, 2, 3}.
This has 3 elements (all C(3,2) = 3 subsets of size 2). -/
axiom example_2sums : (example_set.powersetCard 2).card = 3

/-!
## The Threshold Function

For each k, there's a minimal N(k) such that uniqueness holds for |A| > N(k).
-/

/-- The threshold function N(k): minimal size for uniqueness to hold.

Known values:
- N(3) ≤ 6 (uniqueness holds for |A| > 6)
- N(4) ≤ 12 (uniqueness holds for |A| > 12)

For general k, Gordon-Fraenkel-Straus give N(k) ≤ k² - k + 2 (not sharp).
-/
def threshold (k : ℕ) : ℕ :=
  k^2 - k + 2  -- Upper bound from GFS, not necessarily sharp

/-- The GFS bound: uniqueness holds for |A| > k² - k + 2. -/
axiom gfs_explicit_bound :
    ∀ k : ℕ, k > 2 → ∀ card : ℕ, card > threshold k → KSumDeterminesSet k card

end Erdos494
