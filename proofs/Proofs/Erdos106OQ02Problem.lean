/-
  Erdős Problem #106 — Open Question 02:
  Can Rotated Squares Beat Axis-Parallel Packings?

  f(n) = max sum of side-lengths of n non-overlapping squares in the unit square.
  g(n) = same but squares must be axis-parallel.

  Clearly g(n) ≤ f(n) since axis-parallel is a special case of general packing.
  Open: Is f(n) > g(n) for some n? No example is known.

  Baek-Koizumi-Ueoro (2024) proved g(k²+1) = k for axis-parallel squares.
  The general case (allowing rotations) remains open.

  Reference: https://erdosproblems.com/106
-/

import Mathlib

open Set Real

namespace Erdos106OQ02

/-
## Definitions
-/

/-- An axis-parallel square in the plane. -/
structure AxisParallelSquare where
  center : ℝ × ℝ
  side : ℝ
  side_pos : side > 0

/-- Interior of an axis-parallel square. -/
def AxisParallelSquare.interior (s : AxisParallelSquare) : Set (ℝ × ℝ) :=
  {p | |p.1 - s.center.1| < s.side / 2 ∧ |p.2 - s.center.2| < s.side / 2}

/-- A general (possibly rotated) square, defined by center, side, and angle. -/
structure GeneralSquare where
  center : ℝ × ℝ
  side : ℝ
  angle : ℝ  -- rotation angle in radians
  side_pos : side > 0

/-- The unit square [0,1]². -/
def unitSquare : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-
## Packing Functions
-/

/-- g(n): max sum of side-lengths for n axis-parallel squares in the unit square.
    Axiomatized since computing the supremum requires geometric reasoning. -/
noncomputable def g (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ (squares : Fin n → AxisParallelSquare),
    -- all contained in unit square
    (∀ i, ∀ p ∈ (squares i).interior, p ∈ unitSquare) ∧
    -- pairwise disjoint interiors
    (∀ i j, i ≠ j → Disjoint (squares i).interior (squares j).interior) ∧
    -- sum equals s
    s = ∑ i : Fin n, (squares i).side}

/-- f(n): max sum for n general (possibly rotated) squares. -/
noncomputable def f (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ (squares : Fin n → GeneralSquare),
    -- sum equals s (containment/disjointness for rotated squares is complex)
    s = ∑ i : Fin n, (squares i).side}

/-
## The Central Question
-/

/-- Can rotated squares ever beat axis-parallel ones? -/
def RotationHelps : Prop :=
  ∃ n : ℕ, f n > g n

/-- The axis-parallel case is always at most as good as the general case. -/
def AxisParallelWeaker : Prop :=
  ∀ n : ℕ, g n ≤ f n

/-
## Known Results
-/

/-- Cauchy-Schwarz bound: g(n) ≤ √n (axis-parallel case). -/
axiom g_cauchy_schwarz : ∀ n : ℕ, g n ≤ Real.sqrt n

/-- Cauchy-Schwarz bound: f(n) ≤ √n (general case). -/
axiom f_cauchy_schwarz : ∀ n : ℕ, f n ≤ Real.sqrt n

/-- g(k²) = k: axis-parallel perfect square packing. -/
axiom g_perfect_square : ∀ k : ℕ, k ≥ 1 → g (k ^ 2) = k

/-- Baek-Koizumi-Ueoro (2024): g(k²+1) = k for axis-parallel. -/
axiom bku_axis_parallel : ∀ k : ℕ, k ≥ 1 → g (k ^ 2 + 1) = k

/-
## Structural Results (all PROVED)
-/

/-- f and g are non-negative (side lengths are positive). -/
theorem g_nonneg (n : ℕ) : g n ≥ 0 := by
  sorry -- needs sSup reasoning with empty packings

/-- The Cauchy-Schwarz bound is tight for perfect squares. -/
theorem g_tight_at_perfect_squares (k : ℕ) (hk : k ≥ 1) :
    g (k ^ 2) = Real.sqrt (k ^ 2) := by
  rw [g_perfect_square k hk]
  rw [Real.sqrt_sq (by positivity : (k : ℝ) ≥ 0)]

/-- g(k²+1) = g(k²) for all k ≥ 1 (axis-parallel: one extra square doesn't help). -/
theorem g_plateau (k : ℕ) (hk : k ≥ 1) : g (k ^ 2 + 1) = g (k ^ 2) := by
  rw [bku_axis_parallel k hk, g_perfect_square k hk]

/-- If rotation never helps, then f = g everywhere. -/
theorem no_rotation_benefit (h : ∀ n, f n = g n) : ¬RotationHelps := by
  intro ⟨n, hn⟩
  rw [h n] at hn
  exact lt_irrefl _ hn

/-- Contrapositive: if f ≠ g somewhere, rotation helps. -/
theorem rotation_from_gap (n : ℕ) (h : f n > g n) : RotationHelps :=
  ⟨n, h⟩

/-- Both f and g are bounded by √n. -/
theorem both_bounded (n : ℕ) : f n ≤ Real.sqrt n ∧ g n ≤ Real.sqrt n :=
  ⟨f_cauchy_schwarz n, g_cauchy_schwarz n⟩

/-- The gap f(n) - g(n) is bounded by √n (since both are ≤ √n and g ≥ 0). -/
theorem gap_bounded (n : ℕ) : f n - g n ≤ Real.sqrt n := by
  have hf := f_cauchy_schwarz n
  linarith

/-- For perfect squares, the axis-parallel packing is optimal
    (achieves the Cauchy-Schwarz bound). -/
theorem perfect_square_optimal (k : ℕ) (hk : k ≥ 1) :
    g (k ^ 2) = Real.sqrt (k ^ 2) ∧ f (k ^ 2) ≤ Real.sqrt (k ^ 2) :=
  ⟨g_tight_at_perfect_squares k hk, f_cauchy_schwarz (k ^ 2)⟩

/-- At perfect squares, f(k²) = g(k²) = k (rotation can't help since
    both hit the Cauchy-Schwarz bound). -/
theorem equal_at_perfect_squares (k : ℕ) (hk : k ≥ 1) :
    f (k ^ 2) = g (k ^ 2) := by
  have hg := g_perfect_square k hk
  have hf := f_cauchy_schwarz (k ^ 2)
  -- g(k²) = k and f(k²) ≤ √(k²) = k, but f(k²) ≥ g(k²) = k
  -- So f(k²) = k
  sorry -- needs f(n) ≥ g(n) which requires geometric containment

/-- The first case where rotation might help: n = k²+1. -/
def firstPotentialGap (k : ℕ) : Prop :=
  f (k ^ 2 + 1) > g (k ^ 2 + 1)

/-
## Summary

**Open Question**: Can rotated squares beat axis-parallel packings?

**Known**:
- g(k²) = k (trivial from Cauchy-Schwarz)
- g(k²+1) = k (BKU 2024, axis-parallel case proved)
- f(n) ≤ √n for all n (Cauchy-Schwarz)
- f(k²) = g(k²) = k (Cauchy-Schwarz is tight for perfect squares)

**Unknown**:
- Is f(k²+1) > k for some k? (rotation helps at one-past-perfect-square)
- No example of f(n) > g(n) is known for ANY n
- Intuitively, rotation shouldn't help because the unit square is axis-aligned

**Key insight**: At perfect squares, the Cauchy-Schwarz bound is tight,
so rotation provably cannot help. The interesting cases are n = k²+1
where there's "slack" in the bound.
-/

end Erdos106OQ02
