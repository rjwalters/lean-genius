/-!
# Erdős Problem #896: Unique Product Representations

For subsets A, B ⊆ {1, ..., N}, define F(A, B) as the number of products
m = ab (a ∈ A, b ∈ B) that have exactly one such representation.

Erdős (1972) asked to estimate max_{A,B} F(A,B).

Van Doorn established bounds:
  (1 + o(1)) N²/log N ≤ max F(A,B) ≪ N²/(log N)^δ (log log N)^{3/2}
where δ ≈ 0.086.

Related to Problem #490 on multiplicative structure of product sets.

Reference: https://erdosproblems.com/896
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Product Representations -/

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

/-! ## Main Problem -/

/-- The maximum of F(A,B) over all A, B ⊆ {1,...,N}. -/
axiom maxUniqueProducts : ℕ → ℕ

/-- maxUniqueProducts N is achieved by some pair (A, B). -/
axiom maxUniqueProducts_achieved (N : ℕ) :
    ∃ A B : Finset ℕ, SubsetsOfRange A B N ∧
      uniqueProductCount A B = maxUniqueProducts N

/-- Erdős Problem 896: Estimate max_{A,B ⊆ {1,...,N}} F(A,B).
    The problem asks for the asymptotic order of this maximum. -/
def ErdosProblem896 : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ N : ℕ, 2 ≤ N →
      C₁ * N ^ 2 / Real.log N ≤ maxUniqueProducts N ∧
      (maxUniqueProducts N : ℝ) ≤ C₂ * N ^ 2 / Real.log N

/-! ## Van Doorn's Bounds -/

/-- Van Doorn's lower bound: max F(A,B) ≥ (1 + o(1)) N²/log N. -/
def VanDoornLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * N ^ 2 / Real.log N ≤ (maxUniqueProducts N : ℝ)

/-- Van Doorn's upper bound exponent δ ≈ 0.086. -/
noncomputable def vanDoornDelta : ℝ := 0.086

/-- Van Doorn's upper bound: max F(A,B) ≪ N²/(log N)^δ (log log N)^{3/2}. -/
def VanDoornUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
      (maxUniqueProducts N : ℝ) ≤
        C * N ^ 2 / ((Real.log N) ^ vanDoornDelta *
          (Real.log (Real.log N)) ^ (3/2 : ℝ))

/-- Van Doorn's combined result. -/
axiom van_doorn_bounds : VanDoornLowerBound ∧ VanDoornUpperBound

/-! ## Basic Properties -/

/-- F(A, B) is at most |A| · |B| (trivial upper bound). -/
theorem uniqueProductCount_le_product (A B : Finset ℕ) :
    uniqueProductCount A B ≤ A.card * B.card := by
  unfold uniqueProductCount
  calc ((A ×ˢ B).image (fun p => p.1 * p.2)).filter
        (fun m => reprCount A B m = 1) |>.card
      ≤ ((A ×ˢ B).image (fun p => p.1 * p.2)).card :=
        Finset.card_filter_le _ _
    _ ≤ (A ×ˢ B).card := Finset.card_image_le
    _ = A.card * B.card := Finset.card_product A B

/-- F(A, B) = F(B, A) by commutativity of multiplication. -/
axiom uniqueProductCount_comm (A B : Finset ℕ) :
    uniqueProductCount A B = uniqueProductCount B A

/-- The empty set gives F = 0. -/
theorem uniqueProductCount_empty_left (B : Finset ℕ) :
    uniqueProductCount ∅ B = 0 := by
  simp [uniqueProductCount, reprCount]

/-- For singleton A = {a} with a ∣ b for no b ∈ B sharing products,
    F({a}, B) relates to the distinctness of products ab. -/
axiom singleton_unique_count (a : ℕ) (B : Finset ℕ) (ha : 0 < a)
    (hinj : (B.image (· * a)).card = B.card) :
    uniqueProductCount {a} B = B.card

/-! ## Gap Between Bounds -/

/-- The gap between the lower and upper bounds suggests the true order
    might be N²/log N, but the exact exponent is unknown. -/
def ExactOrderConjecture : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ N : ℕ, 2 ≤ N →
      C₁ * N ^ 2 / Real.log N ≤ (maxUniqueProducts N : ℝ) ∧
      (maxUniqueProducts N : ℝ) ≤ C₂ * N ^ 2 / Real.log N
