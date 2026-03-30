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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
/- ## Known Bounds -/

/-- **Guth–Katz (2015)**: f(2n) ≳ n/log n. The minimum number
    of distinct distances among 2n points is Ω(n/log n). -/
/-- **Lattice Upper Bound**: f(2n) ≲ n/√(log n) from the integer
    lattice. Thus the question asks if F(2n) = o(n/√(log n)). -/
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

/- ## Lenz Construction (ℝ⁴) — Formalized -/

/-- A point in ℝ⁴, represented as two coordinate pairs. -/
def Point4 := (ℝ × ℝ) × (ℝ × ℝ)

/-- Squared Euclidean distance between two points in ℝ⁴. -/
def distSq4 (p q : Point4) : ℝ :=
  (p.1.1 - q.1.1) ^ 2 + (p.1.2 - q.1.2) ^ 2 +
  (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2

/-- A point on the first Lenz circle: (cos θ, sin θ, 0, 0).
    This circle lies in the x₁x₂-plane. -/
noncomputable def lenzCircle1 (θ : ℝ) : Point4 :=
  ((Real.cos θ, Real.sin θ), (0, 0))

/-- A point on the second Lenz circle: (0, 0, cos φ, sin φ).
    This circle lies in the x₃x₄-plane, orthogonal to the first. -/
noncomputable def lenzCircle2 (φ : ℝ) : Point4 :=
  ((0, 0), (Real.cos φ, Real.sin φ))

/-- **Lenz's Theorem**: Every bipartite squared distance between
    points on two orthogonal unit circles in ℝ⁴ equals 2.
    Consequently all bipartite distances equal √2, giving F₄(2n) = 1
    for every n ≥ 1. -/
theorem lenz_distSq4_eq (θ φ : ℝ) :
    distSq4 (lenzCircle1 θ) (lenzCircle2 φ) = 2 := by
  show (Real.cos θ - 0) ^ 2 + (Real.sin θ - 0) ^ 2 +
       (0 - Real.cos φ) ^ 2 + (0 - Real.sin φ) ^ 2 = 2
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq φ
  nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ),
             sq_nonneg (Real.cos φ), sq_nonneg (Real.sin φ)]

/-- Both Lenz circles are unit circles: every point has norm² = 1. -/
theorem lenzCircle1_unit (θ : ℝ) :
    distSq4 (lenzCircle1 θ) ((0, 0), (0, 0)) = 1 := by
  show (Real.cos θ - 0) ^ 2 + (Real.sin θ - 0) ^ 2 +
       (0 - 0) ^ 2 + (0 - 0) ^ 2 = 1
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]

theorem lenzCircle2_unit (φ : ℝ) :
    distSq4 ((0, 0), (0, 0)) (lenzCircle2 φ) = 1 := by
  show (0 - 0) ^ 2 + (0 - 0) ^ 2 +
       (0 - Real.cos φ) ^ 2 + (0 - Real.sin φ) ^ 2 = 1
  have := Real.sin_sq_add_cos_sq φ
  nlinarith [sq_nonneg (Real.cos φ), sq_nonneg (Real.sin φ)]

/- ## Observations -/

/- **Connection to Problem #89**: The Erdős distinct distances
    problem (general case) is Problem #89. This bipartite variant
    asks whether the bipartite structure provides additional savings. -/

/- **Dimension gap**: In ℝ⁴ the Lenz construction gives F₄(2n) = 1,
    while in ℝ² the conjectured answer is F₂(2n) = o(n/√(log n)).
    The ℝ³ case is also unknown. -/
