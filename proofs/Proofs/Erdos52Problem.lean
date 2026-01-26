/-!
# Erdős Problem #52: The Sum-Product Conjecture

For a finite set of integers A, is it true that for every ε > 0,
max(|A+A|, |A·A|) ≫ |A|^{2-ε}?

## Status: OPEN ($250 prize)

## References
- Erdős–Szemerédi, "A combinatorial theorem in group theory" (1983)
- Bloom, improved bound to |A|^{1270/951} (2025)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
## Section I: Sumset and Product Set
-/

/-- The sumset A + A: all pairwise sums of elements of A. -/
def sumset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The product set A · A: all pairwise products of elements of A. -/
def productset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 * p.2)

/-- The sum-product quantity: max(|A+A|, |A·A|). -/
noncomputable def sumProductMax (A : Finset ℤ) : ℕ :=
  max (sumset A).card (productset A).card

/-!
## Section II: The Sum-Product Conjecture
-/

/-- **Erdős Problem #52** (Erdős–Szemerédi Sum-Product Conjecture):
For every ε > 0, there exists a constant C such that for every finite
set A of integers with |A| ≥ 2,
  max(|A+A|, |A·A|) ≥ C · |A|^{2-ε}.

This is one of the most influential open problems in additive combinatorics. -/
def ErdosProblem52 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧
      ∀ A : Finset ℤ, A.card ≥ 2 →
        (sumProductMax A : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

/-!
## Section III: The Erdős–Szemerédi Theorem
-/

/-- Erdős and Szemerédi (1983) proved the first super-linear lower bound:
there exists c > 0 such that max(|A+A|, |A·A|) ≥ |A|^{1+c} for all
finite sets A with |A| ≥ 2. This was the foundational result. -/
axiom erdos_szemeredi_theorem :
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℤ, A.card ≥ 2 →
      (sumProductMax A : ℝ) ≥ (A.card : ℝ) ^ (1 + c)

/-!
## Section IV: Current Best Bound
-/

/-- Bloom (2025) proved the current best bound:
max(|A+A|, |A·A|) ≥ |A|^{1270/951 - o(1)} ≈ |A|^{1.335}.
We state this as: for every ε > 0, there exists N₀ such that for
|A| ≥ N₀, the bound max(|A+A|, |A·A|) ≥ |A|^{1270/951 - ε} holds. -/
axiom bloom_bound :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ →
      (sumProductMax A : ℝ) ≥ (A.card : ℝ) ^ (1270 / 951 - ε)

/-!
## Section V: Trivial Bounds
-/

/-- The sumset is at least as large as the original set. -/
axiom sumset_card_ge (A : Finset ℤ) (h : A.Nonempty) :
    A.card ≤ (sumset A).card

/-- The product set is at least as large as the original set
(when A contains no zero and has at least 2 elements). -/
axiom productset_card_ge (A : Finset ℤ)
    (h : A.card ≥ 2) (h0 : (0 : ℤ) ∉ A) :
    A.card ≤ (productset A).card

/-- Upper bound: both sumset and product set have at most |A|² elements. -/
axiom sumset_card_le (A : Finset ℤ) :
    (sumset A).card ≤ A.card * A.card

axiom productset_card_le (A : Finset ℤ) :
    (productset A).card ≤ A.card * A.card

/-!
## Section VI: Higher-Fold Generalizations
-/

/-- The m-fold sumset mA: all sums of m elements from A. -/
def mfoldSumset (A : Finset ℤ) : ℕ → Finset ℤ
  | 0 => {0}
  | (n + 1) => (mfoldSumset A n ×ˢ A).image (fun p => p.1 + p.2)

/-- The m-fold product set A^m: all products of m elements from A. -/
def mfoldProductset (A : Finset ℤ) : ℕ → Finset ℤ
  | 0 => {1}
  | (n + 1) => (mfoldProductset A n ×ˢ A).image (fun p => p.1 * p.2)

/-- Generalized conjecture: for m ≥ 2 and every ε > 0,
max(|mA|, |A^m|) ≥ C · |A|^{m-ε}. -/
def GeneralizedSumProduct (m : ℕ) : Prop :=
  m ≥ 2 →
  ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧
      ∀ A : Finset ℤ, A.card ≥ 2 →
        (max (mfoldSumset A m).card (mfoldProductset A m).card : ℝ) ≥
          C * (A.card : ℝ) ^ ((m : ℝ) - ε)

/-!
## Section VII: Connection to Problem 53
-/

/-- Problem 52 implies a weak form of Problem 53.
If max(|A+A|, |A·A|) is large, then A generates many sums or products.
Problem 53 (resolved by Chang 2003) asks about sums and products
of distinct subsets rather than pairwise operations. -/
axiom sum_product_implies_many_representations :
  ∀ A : Finset ℤ, A.card ≥ 2 →
    ((sumset A).card + (productset A).card : ℤ) ≥ A.card
