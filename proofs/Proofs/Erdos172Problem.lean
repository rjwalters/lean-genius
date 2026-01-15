/-
Erdős Problem #172: Monochromatic Sums and Products

Source: https://erdosproblems.com/172
Status: OPEN

Statement:
Is it true that in any finite coloring of ℕ there exist arbitrarily large finite
sets A such that all sums and products of distinct elements of A are the same color?

History:
- First asked by Hindman
- Hindman (1980): FALSE for infinite A with 7 colors
- Moreira (2017): TRUE for |A| = 2 (monochromatic {x, x+y, xy} exists)
- Alweiss (2023): TRUE for ℚ\{0} with arbitrarily large A

This combines Ramsey theory with the additive and multiplicative structure of ℕ.
-/

import Mathlib

open Finset

namespace Erdos172

/-! ## Core Definitions -/

/-- A **coloring** of ℕ with k colors. -/
def Coloring (k : ℕ) := ℕ → Fin k

/-- A set A is **sum-product monochromatic** under coloring c if all sums and
    products of distinct elements of A have the same color.

    More precisely: for any nonempty S ⊆ A, both ∑ S and ∏ S have color c₀. -/
def IsSumProductMonochromatic {k : ℕ} (c : Coloring k) (A : Finset ℕ) (c₀ : Fin k) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty →
    c (S.sum id) = c₀ ∧ c (S.prod id) = c₀

/-- Weaker version: just sums of pairs and products of pairs. -/
def IsPairwiseMonochromatic {k : ℕ} (c : Coloring k) (A : Finset ℕ) (c₀ : Fin k) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a ≠ b → c (a + b) = c₀) ∧
  (∀ a ∈ A, ∀ b ∈ A, a ≠ b → c (a * b) = c₀)

/-! ## The Main Conjecture -/

/-- **Erdős Problem #172** (OPEN): In any finite coloring of ℕ, there exist
    arbitrarily large monochromatic sum-product sets.

    Formally: for any k-coloring and any m, there exists A with |A| ≥ m
    such that all sums and products of subsets of A have the same color. -/
def Erdos172Conjecture : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1) (c : Coloring k) (m : ℕ),
    ∃ (A : Finset ℕ), A.card ≥ m ∧ ∃ c₀, IsSumProductMonochromatic c A c₀

/-- The problem is open. -/
theorem erdos_172_undecided : Erdos172Conjecture ∨ ¬Erdos172Conjecture :=
  Classical.em Erdos172Conjecture

/-! ## Known Positive Results -/

/-- **Moreira (2017)**: In any finite coloring, there exist x, y such that
    {x, x+y, xy} are all the same color.

    This is the |A| = 2 case of the conjecture (with A = {x, y} implicitly,
    and sums/products being x+y and xy). -/
axiom moreira_2017 :
  ∀ (k : ℕ) (hk : k ≥ 1) (c : Coloring k),
    ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ x ≠ y ∧
      c x = c (x + y) ∧ c x = c (x * y)

/-- **Alweiss (2023)**: The full conjecture holds over ℚ\{0}.

    For any finite coloring of ℚ\{0} and any m, there exist arbitrarily
    large sets A ⊆ ℚ\{0} with all sums and products monochromatic.

    This shows the conjecture is "almost true" - just needs to be restricted
    to integers. -/
axiom alweiss_2023_rationals :
  ∀ (k : ℕ) (hk : k ≥ 1) (c : ℚ → Fin k) (m : ℕ),
    ∃ (A : Finset ℚ), (∀ a ∈ A, a ≠ 0) ∧ A.card ≥ m ∧
      ∃ c₀, ∀ S : Finset ℚ, S ⊆ A → S.Nonempty →
        c (S.sum id) = c₀ ∧ c (S.prod id) = c₀

/-! ## Known Negative Results -/

/-- **Hindman (1980)**: The conjecture fails for INFINITE A.

    There exists a 7-coloring of ℕ such that no infinite set has all
    its sums and products monochromatic. -/
axiom hindman_1980_counterexample :
  ∃ (c : Coloring 7), ∀ (A : Set ℕ), A.Infinite →
    ¬∃ c₀, ∀ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A → S.Nonempty →
      c (S.sum id) = c₀ ∧ c (S.prod id) = c₀

/-! ## Simpler Variants -/

/-- The sum-only version (Schur's theorem style): monochromatic sums exist. -/
def SumMonochromatic {k : ℕ} (c : Coloring k) (A : Finset ℕ) (c₀ : Fin k) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → c (S.sum id) = c₀

/-- The product-only version: monochromatic products exist. -/
def ProductMonochromatic {k : ℕ} (c : Coloring k) (A : Finset ℕ) (c₀ : Fin k) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → c (S.prod id) = c₀

/-- Sum-product monochromatic implies both sum and product monochromatic. -/
theorem sum_product_implies_both {k : ℕ} {c : Coloring k} {A : Finset ℕ} {c₀ : Fin k}
    (h : IsSumProductMonochromatic c A c₀) :
    SumMonochromatic c A c₀ ∧ ProductMonochromatic c A c₀ := by
  constructor
  · intro S hS hne; exact (h S hS hne).1
  · intro S hS hne; exact (h S hS hne).2

/-! ## Examples -/

/-- Any singleton is trivially sum-product monochromatic. -/
theorem singleton_monochromatic {k : ℕ} (c : Coloring k) (n : ℕ) :
    IsSumProductMonochromatic c {n} (c n) := by
  intro S hS hne
  have hSeq : S = {n} := Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    ⟨hne, fun x hx => Finset.mem_singleton.mp (hS hx)⟩
  simp [hSeq]

/-- For the empty set, the property holds vacuously. -/
theorem empty_monochromatic {k : ℕ} (c : Coloring k) (c₀ : Fin k) :
    IsSumProductMonochromatic c ∅ c₀ := by
  intro S hS hne
  simp at hS
  exact absurd hS (Finset.Nonempty.ne_empty hne)

end Erdos172
