/-
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

/-
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

/-
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

/-
## Section III: The Erdős–Szemerédi Theorem
-/

/-- Erdős and Szemerédi (1983) proved the first super-linear lower bound:
there exists c > 0 such that max(|A+A|, |A·A|) ≥ |A|^{1+c} for all
finite sets A with |A| ≥ 2. This was the foundational result. -/
/-
## Section IV: Current Best Bound
-/

/-- Bloom (2025) proved the current best bound:
max(|A+A|, |A·A|) ≥ |A|^{1270/951 - o(1)} ≈ |A|^{1.335}.
We state this as: for every ε > 0, there exists N₀ such that for
|A| ≥ N₀, the bound max(|A+A|, |A·A|) ≥ |A|^{1270/951 - ε} holds. -/
/-
## Section V: Trivial Bounds
-/

/-- The sumset is at least as large as the original set.
    Proof: fix a₀ ∈ A; the map a ↦ a + a₀ injects A into sumset A. -/
theorem sumset_card_ge (A : Finset ℤ) (h : A.Nonempty) :
    A.card ≤ (sumset A).card := by
  obtain ⟨a₀, ha₀⟩ := h
  have hinj : Set.InjOn (· + a₀) (↑A) := fun a _ b _ hab => by linarith
  have hsub : Finset.image (· + a₀) A ⊆ sumset A := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [sumset, Finset.mem_image, Finset.mem_product]
    exact ⟨(a, a₀), ⟨ha, ha₀⟩, rfl⟩
  calc A.card = (Finset.image (· + a₀) A).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (sumset A).card := Finset.card_le_card hsub

/-- The product set is at least as large as the original set
    (when A contains no zero and has at least 2 elements).
    Proof: fix a₀ ∈ A with a₀ ≠ 0; the map a ↦ a * a₀ injects A into productset A. -/
theorem productset_card_ge (A : Finset ℤ)
    (h : A.card ≥ 2) (h0 : (0 : ℤ) ∉ A) :
    A.card ≤ (productset A).card := by
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a₀, ha₀⟩ := hne
  have ha₀_ne : a₀ ≠ 0 := fun heq => h0 (heq ▸ ha₀)
  have hinj : Set.InjOn (· * a₀) (↑A) :=
    fun a _ b _ hab => mul_right_cancel₀ ha₀_ne hab
  have hsub : Finset.image (· * a₀) A ⊆ productset A := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [productset, Finset.mem_image, Finset.mem_product]
    exact ⟨(a, a₀), ⟨ha, ha₀⟩, rfl⟩
  calc A.card = (Finset.image (· * a₀) A).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (productset A).card := Finset.card_le_card hsub

/-- Upper bound: both sumset and product set have at most |A|² elements.
    Follows from Finset.card_image_le since they are images of A ×ˢ A. -/
theorem sumset_card_le (A : Finset ℤ) :
    (sumset A).card ≤ A.card * A.card := by
  unfold sumset
  calc (A ×ˢ A).image (fun p => p.1 + p.2) |>.card
      ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product A A

theorem productset_card_le (A : Finset ℤ) :
    (productset A).card ≤ A.card * A.card := by
  unfold productset
  calc (A ×ˢ A).image (fun p => p.1 * p.2) |>.card
      ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product A A

/-
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

/-
## Section VII: Connection to Problem 53
-/

/-- Problem 52 implies a weak form of Problem 53.
If max(|A+A|, |A·A|) is large, then A generates many sums or products.
Problem 53 (resolved by Chang 2003) asks about sums and products
of distinct subsets rather than pairwise operations. -/
