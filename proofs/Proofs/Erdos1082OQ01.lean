/-
Erdős Problem #1082 OQ-01: Distinct Distances in General Position (n/2 Lower Bound)

This file extends the Erdős 1082 formalization with:
1. Proof that at most 3 points in ℝ² can be mutually equidistant
2. Infrastructure for counting distinct squared distances
3. Small case verification of the n/2 conjecture

Key Result: `no_four_equidistant` - 4 mutually equidistant points cannot exist in ℝ².
Proof uses the Lagrange identity: overdetermined perpendicular bisector constraints
in 2D lead to 3d⁴/4 = d⁴/4, contradiction.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Finset

namespace Erdos1082OQ01

set_option maxHeartbeats 800000

/-! ## Core Algebra: No 4 Equidistant Points in ℝ²

We work with raw real coordinates to avoid abstraction overhead. -/

/-- Squared Euclidean distance between two points in ℝ² -/
def distSq (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

theorem distSq_nonneg (p q : ℝ × ℝ) : 0 ≤ distSq p q := by
  unfold distSq; positivity

theorem distSq_comm (p q : ℝ × ℝ) : distSq p q = distSq q p := by
  unfold distSq; ring

theorem distSq_eq_zero_iff (p q : ℝ × ℝ) : distSq p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold distSq at h
    have hx : (p.1 - q.1) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    have hy : (p.2 - q.2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    ext <;> nlinarith [sq_abs (p.1 - q.1), sq_abs (p.2 - q.2)]
  · rintro rfl; unfold distSq; ring

theorem distSq_pos_of_ne {p q : ℝ × ℝ} (h : p ≠ q) : 0 < distSq p q := by
  rw [lt_iff_le_and_ne]
  exact ⟨distSq_nonneg p q, fun heq => h ((distSq_eq_zero_iff p q).mp heq.symm)⟩

/-! ## The Main Structural Theorem

**Theorem**: 4 mutually equidistant points cannot exist in ℝ².

We work with 6 real coordinates directly (u₀, u₁, v₀, v₁, δ₀, δ₁) representing
difference vectors, to avoid `set`/`subst_vars` overhead. -/

/-- Core algebraic lemma: the system of equations arising from 4 equidistant
points in ℝ² is inconsistent for d > 0.

Variables represent: u = b - a, v = c - a, δ = e - c.
Hypotheses encode: |u|² = |v|² = |u-v|² = |δ|² = d,
plus perpendicularity conditions from equal distances. -/
theorem equidistant_system_inconsistent
    (u₀ u₁ v₀ v₁ δ₀ δ₁ d : ℝ) (hd : 0 < d)
    -- |u|² = d (distance a-b)
    (hu : u₀ ^ 2 + u₁ ^ 2 = d)
    -- |v|² = d (distance a-c)
    (hv : v₀ ^ 2 + v₁ ^ 2 = d)
    -- |u-v|² = d (distance b-c)
    (huv : (u₀ - v₀) ^ 2 + (u₁ - v₁) ^ 2 = d)
    -- |δ|² = d (distance c-e)
    (hδ : δ₀ ^ 2 + δ₁ ^ 2 = d)
    -- δ ⊥ u (from perpendicular bisector of ab through e and c)
    (hperp : δ₀ * u₀ + δ₁ * u₁ = 0)
    -- (δ+v-u)·v = 0 (from perpendicular bisector of ac through e and b)
    (hperp2 : (δ₀ + v₀ - u₀) * v₀ + (δ₁ + v₁ - u₁) * v₁ = 0) :
    False := by
  -- Step 1: From equilateral triangle, u · v = d/2
  have dot_uv : u₀ * v₀ + u₁ * v₁ = d / 2 := by nlinarith
  -- Step 2: From hperp2 and hv and dot_uv, derive δ · v = -d/2
  have dot_δv : δ₀ * v₀ + δ₁ * v₁ = -d / 2 := by nlinarith
  -- Step 3: Lagrange identity for δ,u: |δ|²|u|² = (δ·u)² + (δ×u)²
  --   d² = 0 + (δ×u)², so (δ×u)² = d²
  have cross_δu : (δ₀ * u₁ - δ₁ * u₀) ^ 2 = d ^ 2 := by nlinarith
  -- Step 4: Lagrange identity for u,v: |u|²|v|² = (u·v)² + (u×v)²
  --   d² = d²/4 + (u×v)², so (u×v)² = 3d²/4
  have cross_uv : (u₀ * v₁ - u₁ * v₀) ^ 2 = 3 * d ^ 2 / 4 := by nlinarith
  -- Step 5: Vector identity (δ×u)(u×v) = (δ·u)(u·v) - (δ·v)|u|²
  have identity : (δ₀ * u₁ - δ₁ * u₀) * (u₀ * v₁ - u₁ * v₀) =
    (δ₀ * u₀ + δ₁ * u₁) * (u₀ * v₀ + u₁ * v₁) -
    (δ₀ * v₀ + δ₁ * v₁) * (u₀ ^ 2 + u₁ ^ 2) := by ring
  -- Substituting: = 0 · (d/2) - (-d/2) · d = d²/2
  have key : (δ₀ * u₁ - δ₁ * u₀) * (u₀ * v₁ - u₁ * v₀) = d ^ 2 / 2 := by
    rw [identity, hperp, dot_uv, dot_δv, hu]; ring
  -- Step 6: Square both sides and compare
  -- From key²: (δ×u)²·(u×v)² = d⁴/4
  -- From cross_δu · cross_uv: d² · 3d²/4 = 3d⁴/4
  -- But these equal the same product! So d⁴/4 = 3d⁴/4.
  have lhs : (δ₀ * u₁ - δ₁ * u₀) ^ 2 * (u₀ * v₁ - u₁ * v₀) ^ 2 = d ^ 4 / 4 := by
    have := mul_self_nonneg (δ₀ * u₁ - δ₁ * u₀)
    have := mul_self_nonneg (u₀ * v₁ - u₁ * v₀)
    nlinarith [sq_nonneg ((δ₀ * u₁ - δ₁ * u₀) * (u₀ * v₁ - u₁ * v₀) - d ^ 2 / 2)]
  have rhs : (δ₀ * u₁ - δ₁ * u₀) ^ 2 * (u₀ * v₁ - u₁ * v₀) ^ 2 = 3 * d ^ 4 / 4 := by
    rw [cross_δu, cross_uv]; ring
  -- d⁴/4 = 3d⁴/4 → d⁴ = 0 → d = 0, contradicting hd
  have h0 : d ^ 4 = 0 := by linarith
  have : d = 0 := by
    by_contra hne; exact absurd h0 (ne_of_gt (by positivity))
  linarith

/-- **No 4 equidistant points in ℝ²**: Given 4 distinct points in ℝ² with all 6
pairwise squared distances equal to d > 0, we reach a contradiction. -/
theorem no_four_equidistant (a b c e : ℝ × ℝ) (d : ℝ) (hd : 0 < d)
    (_hab : a ≠ b) (_hac : a ≠ c) (_hae : a ≠ e) (_hbc : b ≠ c) (_hbe : b ≠ e) (_hce : c ≠ e)
    (dab : distSq a b = d) (dac : distSq a c = d) (dbc : distSq b c = d)
    (dae : distSq a e = d) (dbe : distSq b e = d) (dce : distSq c e = d) : False := by
  unfold distSq at *
  -- Define difference vectors
  -- u = b - a, v = c - a, δ = e - c
  -- Derive: |u|² = d (note: (a-b)² = (b-a)²)
  have hu : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 = d := by nlinarith
  -- |v|² = d
  have hv : (c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2 = d := by nlinarith
  -- |u-v|² = d: note u-v = (b-a)-(c-a) = b-c
  have huv : (b.1 - a.1 - (c.1 - a.1)) ^ 2 + (b.2 - a.2 - (c.2 - a.2)) ^ 2 = d := by
    nlinarith
  -- |δ|² = d
  have hδ : (e.1 - c.1) ^ 2 + (e.2 - c.2) ^ 2 = d := by nlinarith
  -- δ · u = 0: from dae = dbe (both = d), expanding gives linear relation
  -- (a-e)² = (b-e)² and (a-c)² = (b-c)² [from dac=dbc]
  -- Subtracting gives 2(e-c)·(b-a) = 0
  have hperp : (e.1 - c.1) * (b.1 - a.1) + (e.2 - c.2) * (b.2 - a.2) = 0 := by nlinarith
  -- (δ+v-u)·v = 0: from dae = dce and dac = dbc
  have hperp2 : (e.1 - c.1 + (c.1 - a.1) - (b.1 - a.1)) * (c.1 - a.1) +
    (e.2 - c.2 + (c.2 - a.2) - (b.2 - a.2)) * (c.2 - a.2) = 0 := by nlinarith
  exact equidistant_system_inconsistent
    (b.1 - a.1) (b.2 - a.2) (c.1 - a.1) (c.2 - a.2) (e.1 - c.1) (e.2 - c.2) d hd
    hu hv huv hδ hperp hperp2

/-! ## Distinct Distance Counting Infrastructure -/

/-- The set of distinct squared distances from pairs in S -/
noncomputable def distinctDistSq (S : Finset (ℝ × ℝ)) : Finset ℝ :=
  S.offDiag.image (fun pq => distSq pq.1 pq.2)

/-- Any n ≥ 2 distinct points determine at least 1 distinct distance -/
theorem at_least_one_distance (S : Finset (ℝ × ℝ)) (h : 2 ≤ S.card) :
    1 ≤ (distinctDistSq S).card := by
  have ⟨p, hp, q, hq, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hmem : (p, q) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨hp, hq, hne⟩
  exact Finset.one_le_card.mpr ⟨_, Finset.mem_image.mpr ⟨(p, q), hmem, rfl⟩⟩

/-- The n/2 conjecture holds for n ≤ 3 (since ⌊n/2⌋ ≤ 1) -/
theorem conjecture_n_le_3 (S : Finset (ℝ × ℝ)) (h2 : 2 ≤ S.card) (h3 : S.card ≤ 3) :
    S.card / 2 ≤ (distinctDistSq S).card := by
  have : S.card / 2 ≤ 1 := by omega
  linarith [at_least_one_distance S h2]

/-! ## Summary

### Results Proved (Zero Sorries)
1. `equidistant_system_inconsistent`: The algebraic system from 4 equidistant
   points in ℝ² has no solution for d > 0 (Lagrange identity proof)
2. `no_four_equidistant`: 4 mutually equidistant points are impossible in ℝ²
3. `at_least_one_distance`: n ≥ 2 points → at least 1 distinct distance
4. `conjecture_n_le_3`: the n/2 conjecture for n ≤ 3

### Proof Technique
Given 4 equidistant points with common squared distance d:
- Perpendicular bisector conditions: δ·u = 0 and (δ+v-u)·v = 0
- Equilateral: u·v = d/2, giving δ·v = -d/2
- Lagrange identity: (δ×u)² = d², (u×v)² = 3d²/4
- Vector identity: (δ×u)(u×v) = d²/2
- Squaring: d⁴/4 = 3d⁴/4, so d = 0. Contradiction.

### Mathematical Significance
At most 3 points in ℝ² can be mutually equidistant → any n ≥ 4 points have ≥ 2
distinct distances → n/2 conjecture holds for n ≤ 5 (since ⌊n/2⌋ ≤ 2).
-/

end Erdos1082OQ01
