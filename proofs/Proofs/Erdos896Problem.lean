/-
Erdős Problem #896: Unique Product Representations

For subsets A, B ⊆ {1, ..., N}, define F(A, B) as the number of products
m = ab (a ∈ A, b ∈ B) that have exactly one such representation.

Erdős (1972) asked to estimate max_{A,B} F(A,B).

Van Doorn established bounds:
  (1 + o(1)) N²/log N ≤ max F(A,B) ≪ N²/(log N)^δ (log log N)^{3/2}
where δ = 1 - (1 + log log 2)/log 2 ≈ 0.086.

Related to Problem #490 on multiplicative structure of product sets.

Reference: [Er72, p.81]
Source: https://erdosproblems.com/896

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
## Product Representations
-/

/-- The number of representations of m as a product ab with a ∈ A, b ∈ B. -/
noncomputable def reprCount (A B : Finset ℕ) (m : ℕ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 * p.2 = m)).card

/-- F(A,B) counts products with exactly one representation. -/
noncomputable def uniqueProductCount (A B : Finset ℕ) : ℕ :=
  ((A ×ˢ B).image (fun p => p.1 * p.2)).filter
    (fun m => reprCount A B m = 1) |>.card

/-- A and B are subsets of {1, ..., N}. -/
def SubsetsOfRange (A B : Finset ℕ) (N : ℕ) : Prop :=
  (∀ a ∈ A, a ∈ Finset.Icc 1 N) ∧ (∀ b ∈ B, b ∈ Finset.Icc 1 N)

/-
## Main Problem
-/

/-- The maximum of F(A,B) over all A, B ⊆ {1,...,N}.
    Defined as the supremum of uniqueProductCount over the finite set
    of all pairs of subsets. Since ℕ has OrderBot (⊥ = 0), Finset.sup
    returns 0 for N = 0 (no subsets) and the actual maximum otherwise. -/
noncomputable def maxUniqueProducts (N : ℕ) : ℕ :=
  (Finset.powerset (Finset.Icc 1 N) ×ˢ Finset.powerset (Finset.Icc 1 N)).sup
    (fun p : Finset ℕ × Finset ℕ => uniqueProductCount p.1 p.2)

/-- maxUniqueProducts N is achieved by some pair (A, B).
    Proof: The set of subset pairs is finite and nonempty (contains (∅, ∅)).
    By Finset.exists_max_image, the maximum is achieved. -/
theorem maxUniqueProducts_achieved (N : ℕ) :
    ∃ A B : Finset ℕ, SubsetsOfRange A B N ∧
      uniqueProductCount A B = maxUniqueProducts N := by
  unfold maxUniqueProducts
  set pairs := Finset.powerset (Finset.Icc 1 N) ×ˢ Finset.powerset (Finset.Icc 1 N)
  set f : Finset ℕ × Finset ℕ → ℕ := fun p => uniqueProductCount p.1 p.2
  have hne : pairs.Nonempty :=
    ⟨(∅, ∅), Finset.mem_product.mpr
      ⟨Finset.empty_mem_powerset _, Finset.empty_mem_powerset _⟩⟩
  obtain ⟨⟨A, B⟩, hmem, hmax⟩ := Finset.exists_max_image pairs f hne
  refine ⟨A, B, ?_, ?_⟩
  · -- SubsetsOfRange: (A, B) ∈ pairs means A, B ⊆ Icc 1 N
    exact ⟨Finset.mem_powerset.mp (Finset.mem_product.mp hmem).1,
           Finset.mem_powerset.mp (Finset.mem_product.mp hmem).2⟩
  · -- The sup equals f at the maximizer
    exact (le_antisymm
      (Finset.sup_le fun y hy => hmax y hy)
      (Finset.le_sup hmem)).symm

/-- Erdős Problem 896: Estimate max_{A,B ⊆ {1,...,N}} F(A,B).
    The problem asks for the asymptotic order of this maximum. -/
def ErdosProblem896 : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ N : ℕ, 2 ≤ N →
      C₁ * N ^ 2 / Real.log N ≤ maxUniqueProducts N ∧
      (maxUniqueProducts N : ℝ) ≤ C₂ * N ^ 2 / Real.log N

/-
## Van Doorn's Bounds

Van Doorn proved:
  (1 + o(1)) N²/log N ≤ max F(A,B) ≪ N²/(log N)^δ (log log N)^{3/2}
where δ = 1 - (1 + log log 2)/log 2 ≈ 0.086.

This leaves a gap: the lower bound is ~N²/log N but the upper bound is
only N²/(log N)^{0.086}(log log N)^{3/2}, which is much larger.
The conjecture is that the true order is N²/log N.
-/

/-- Van Doorn's lower bound: max F(A,B) ≥ (1 + o(1)) N²/log N. -/
def VanDoornLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * N ^ 2 / Real.log N ≤ (maxUniqueProducts N : ℝ)

/-- Van Doorn's upper bound: max F(A,B) ≪ N²/(log N)^δ (log log N)^{3/2}
    where δ = 1 - (1 + log log 2)/log 2 ≈ 0.086. -/
def VanDoornUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
      (maxUniqueProducts N : ℝ) ≤
        C * N ^ 2 / ((Real.log N) ^ ((1 : ℝ) - (1 + Real.log (Real.log 2)) / Real.log 2) *
          (Real.log (Real.log N)) ^ ((3 : ℝ)/2))

/-- Van Doorn's combined result. -/
axiom van_doorn_bounds : VanDoornLowerBound ∧ VanDoornUpperBound

/-
## Basic Properties
-/

/-- F(A, B) is at most |A| · |B| (trivial upper bound). -/
theorem uniqueProductCount_le_product (A B : Finset ℕ) :
    uniqueProductCount A B ≤ A.card * B.card := by
  unfold uniqueProductCount
  show (((A ×ˢ B).image (fun p => p.1 * p.2)).filter
        (fun m => reprCount A B m = 1)).card ≤ A.card * B.card
  calc (((A ×ˢ B).image (fun p => p.1 * p.2)).filter
        (fun m => reprCount A B m = 1)).card
      ≤ ((A ×ˢ B).image (fun p => p.1 * p.2)).card :=
        Finset.card_filter_le _ _
    _ ≤ (A ×ˢ B).card := Finset.card_image_le
    _ = A.card * B.card := Finset.card_product A B

/-- reprCount is symmetric: swapping A and B doesn't change the count. -/
theorem reprCount_comm (A B : Finset ℕ) (m : ℕ) :
    reprCount A B m = reprCount B A m := by
  unfold reprCount
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
    exact ⟨⟨h.1.2, h.1.1⟩, by rw [mul_comm]; exact h.2⟩
  · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro ⟨b, a⟩ h
    simp only [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨⟨a, b⟩, by simp [Finset.mem_filter, Finset.mem_product, h.1.2, h.1.1, mul_comm, h.2],
      by simp⟩

/-- F(A, B) = F(B, A) by commutativity of multiplication.
    The bijection (a,b) ↦ (b,a) maps A×B to B×A while preserving
    the product, so representation counts and unique product counts agree. -/
theorem uniqueProductCount_comm (A B : Finset ℕ) :
    uniqueProductCount A B = uniqueProductCount B A := by
  unfold uniqueProductCount
  -- The product image sets are equal (by mul_comm)
  have h_image : (A ×ˢ B).image (fun p => p.1 * p.2) =
      (B ×ˢ A).image (fun p => p.1 * p.2) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨ha, hb⟩, hab⟩
      exact ⟨b, a, ⟨hb, ha⟩, by rw [mul_comm]; exact hab⟩
    · rintro ⟨b, a, ⟨hb, ha⟩, hba⟩
      exact ⟨a, b, ⟨ha, hb⟩, by rw [mul_comm]; exact hba⟩
  -- reprCount is symmetric
  have h_repr : ∀ m, reprCount A B m = reprCount B A m := reprCount_comm A B
  -- The filtered sets are equal
  congr 1
  rw [h_image]
  ext m
  simp [h_repr]

/-- The empty set gives F = 0. -/
theorem uniqueProductCount_empty_left (B : Finset ℕ) :
    uniqueProductCount ∅ B = 0 := by
  simp [uniqueProductCount, reprCount]

/-- F(A, ∅) = 0 by commutativity. -/
theorem uniqueProductCount_empty_right (A : Finset ℕ) :
    uniqueProductCount A ∅ = 0 := by
  rw [uniqueProductCount_comm]; exact uniqueProductCount_empty_left A

/-- If m is not in the product set A·B, its representation count is 0. -/
theorem reprCount_zero_of_not_mem (A B : Finset ℕ) (m : ℕ)
    (hm : m ∉ (A ×ˢ B).image (fun p => p.1 * p.2)) :
    reprCount A B m = 0 := by
  unfold reprCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
  intro ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, not_and]
  intro hab heq
  exact hm (Finset.mem_image.mpr ⟨⟨a, b⟩, Finset.mem_product.mpr hab, heq⟩)

/-- F({a}, {b}) = 1 for singletons: exactly one product ab with unique
    representation. -/
theorem uniqueProductCount_singletons (a b : ℕ) :
    uniqueProductCount {a} {b} = 1 := by
  unfold uniqueProductCount reprCount
  simp [Finset.product_singleton_right, Finset.product_singleton_left,
        Finset.filter_singleton, Finset.image_singleton]

/-- maxUniqueProducts N ≥ 1 for N ≥ 1: singleton subsets {1}×{1} give F = 1. -/
theorem maxUniqueProducts_pos (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ maxUniqueProducts N := by
  unfold maxUniqueProducts
  apply Finset.le_sup
    (Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr
        (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)),
       Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr
        (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩))⟩)
  exact le_of_eq (uniqueProductCount_singletons 1 1).symm

/-
## Monotonicity and Bounds
-/

/-- maxUniqueProducts is monotone in N: enlarging the range gives more
    subset pairs to optimize over. -/
theorem maxUniqueProducts_mono {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    maxUniqueProducts N₁ ≤ maxUniqueProducts N₂ := by
  unfold maxUniqueProducts
  apply Finset.sup_le
  intro ⟨A, B⟩ hmem
  apply Finset.le_sup (f := fun p : Finset ℕ × Finset ℕ => uniqueProductCount p.1 p.2)
  simp only [Finset.mem_product, Finset.mem_powerset] at hmem ⊢
  exact ⟨hmem.1.trans (Finset.Icc_subset_Icc_right h),
         hmem.2.trans (Finset.Icc_subset_Icc_right h)⟩

/-- F(A,B) ≤ |A·B|: unique products are a subset of all products. -/
theorem uniqueProductCount_le_image_card (A B : Finset ℕ) :
    uniqueProductCount A B ≤ ((A ×ˢ B).image (fun p => p.1 * p.2)).card :=
  Finset.card_filter_le _ _

/-
## Gap Between Bounds and Conjecture

The lower bound ~N²/log N and upper bound ~N²/(log N)^{0.086} leave
a substantial gap. Erdős's original question asks for the exact
asymptotic order.
-/

/-- Conjecture: the exact order is N²/log N.
    If true, Van Doorn's lower bound would be tight. -/
def ExactOrderConjecture : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ N : ℕ, 2 ≤ N →
      C₁ * N ^ 2 / Real.log N ≤ (maxUniqueProducts N : ℝ) ∧
      (maxUniqueProducts N : ℝ) ≤ C₂ * N ^ 2 / Real.log N

/-- Van Doorn's lower bound implies the weaker form of the conjecture
    (the lower bound part). -/
theorem van_doorn_implies_lower :
    VanDoornLowerBound → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (1 - ε) * N ^ 2 / Real.log N ≤ (maxUniqueProducts N : ℝ) := by
  intro h ε hε
  exact h ε hε

/-- Summary of known results for Erdős Problem 896. -/
theorem erdos_896_summary :
    VanDoornLowerBound ∧ VanDoornUpperBound :=
  van_doorn_bounds
