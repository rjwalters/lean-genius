/-
# Erdős Problem #661 — Bipartite Distinct Distances

Do there exist point sets x₁,...,xₙ and y₁,...,yₙ in ℝ² such that
the number of distinct distances d(xᵢ,yⱼ) is o(n/√(log n))?

Let F(2n) be the minimum number of distinct bipartite distances
between two sets of n points, and f(2n) the minimum for 2n
general points. The question is whether F(2n) = o(f(2n)).

In ℝ⁴, Lenz showed all distances can be equal (two orthogonal
circles). In ℝ², the answer is unknown.

$50 reward.

Status: OPEN
Reference: https://erdosproblems.com/661
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/- ## Definition -/

/-- A point in ℝ². -/
def Point2 := ℝ × ℝ

/-- Squared Euclidean distance between two points. -/
def distSq (p q : Point2) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The set of distinct squared distances from a set X to a set Y. -/
noncomputable def bipartiteDistSet (X Y : Finset Point2) : Finset ℝ :=
  (X ×ˢ Y).image (fun p => distSq p.1 p.2)

/-- F(2n): the minimum number of distinct bipartite distances
    between two n-point sets in ℝ². Declared opaque since the
    exact values are unknown; properties are axiomatized below. -/
opaque minBipartiteDist : ℕ → ℕ := fun _ => 0

/-- f(2n): the minimum number of distinct distances among 2n
    points in ℝ². Declared opaque since the exact values are
    unknown; properties are axiomatized below. -/
opaque minDistinct2n : ℕ → ℕ := fun _ => 0

/- ## Properties of distSq -/

theorem distSq_nonneg (p q : Point2) : distSq p q ≥ 0 := by
  unfold distSq
  apply add_nonneg <;> apply sq_nonneg

theorem distSq_self (p : Point2) : distSq p p = 0 := by
  unfold distSq
  simp

theorem distSq_comm (p q : Point2) : distSq p q = distSq q p := by
  unfold distSq
  ring

/-- Squared distance is zero iff points are equal. -/
theorem distSq_eq_zero_iff (p q : Point2) : distSq p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold distSq at h
    have h1 : (p.1 - q.1) ^ 2 = 0 := by nlinarith [sq_nonneg (p.2 - q.2)]
    have h2 : (p.2 - q.2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1)]
    exact Prod.ext (sub_eq_zero.mp (sq_eq_zero_iff.mp h1))
                   (sub_eq_zero.mp (sq_eq_zero_iff.mp h2))
  · rintro rfl; exact distSq_self q

/-- Distinct points have positive squared distance. -/
theorem distSq_pos_of_ne {p q : Point2} (h : p ≠ q) : 0 < distSq p q := by
  rcases lt_or_eq_of_le (distSq_nonneg p q) with hlt | heq
  · exact hlt
  · exact absurd ((distSq_eq_zero_iff p q).mp heq.symm) h

/- ## Main Conjecture -/

/-- **Erdős Problem #661**: Is F(2n) = o(f(2n))?
    Equivalently, can bipartite arrangements achieve
    asymptotically fewer distinct distances than general
    point configurations? -/
axiom erdos_661_bipartite_advantage :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (minBipartiteDist n : ℝ) ≤ ε * (minDistinct2n n : ℝ)

/- ## Known Bounds -/

/-- **Guth–Katz (2015)**: f(2n) ≳ n/log n. The minimum number
    of distinct distances among 2n points is Ω(n/log n). -/
axiom guth_katz_lower :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (minDistinct2n n : ℝ) ≥ C * n / Real.log n

/-- **Lattice Upper Bound**: f(2n) ≲ n/√(log n) from the integer
    lattice. Thus the question asks if F(2n) = o(n/√(log n)). -/
axiom lattice_upper :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (minDistinct2n n : ℝ) ≤ C * n / Real.sqrt (Real.log n)

/- ## Basic Bounds -/

theorem bipartiteDistSet_card_le (X Y : Finset Point2) :
    (bipartiteDistSet X Y).card ≤ X.card * Y.card := by
  unfold bipartiteDistSet
  calc (X ×ˢ Y).image (fun p => distSq p.1 p.2) |>.card
      ≤ (X ×ˢ Y).card := Finset.card_image_le
    _ = X.card * Y.card := Finset.card_product X Y

/-- Bipartite distances are monotone under taking subsets. -/
theorem bipartiteDistSet_mono {X₁ X₂ Y₁ Y₂ : Finset Point2}
    (hX : X₁ ⊆ X₂) (hY : Y₁ ⊆ Y₂) :
    bipartiteDistSet X₁ Y₁ ⊆ bipartiteDistSet X₂ Y₂ := by
  unfold bipartiteDistSet
  exact Finset.image_subset_image (Finset.product_subset_product hX hY)

/- ## Higher Dimensions -/

/- **Lenz Construction (ℝ⁴)**: In ℝ⁴, place x₁,...,xₙ on one
    circle and y₁,...,yₙ on an orthogonal circle. Then
    d(xᵢ,yⱼ) = √2 for all i,j: only one bipartite distance. -/

/- ## Observations -/

/- **Connection to Problem #89**: The Erdős distinct distances
    problem (general case) is Problem #89. This bipartite variant
    asks whether the bipartite structure provides additional savings. -/

/- **$50 Reward**: Erdős offered $50 for resolving this problem. -/
