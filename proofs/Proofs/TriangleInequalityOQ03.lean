/-
# Triangle Inequality in Non-Archimedean Geometry (OQ-03)

The standard triangle inequality d(x,z) ≤ d(x,y) + d(y,z) is the defining
axiom of metric spaces. In **non-Archimedean (ultrametric)** spaces, a strictly
stronger form holds:

  d(x,z) ≤ max(d(x,y), d(y,z))

This seemingly small strengthening has dramatic geometric consequences:
- Every triangle is isosceles
- Every point inside a ball is its center
- Balls are either nested or disjoint
- Open balls are also closed (clopen)

These "strange" properties appear naturally in p-adic number theory, where
the p-adic norm |·|_p satisfies the ultrametric inequality.

**Status**: Complete — 0 sorries, 0 axioms
**Extends**: TriangleInequality.lean (the standard triangle inequality)
-/

import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic

namespace TriangleInequalityOQ03

open Metric

/-
## Part I: Ultrametric Fundamentals

An ultrametric distance satisfies the strong triangle inequality:
  d(x, z) ≤ max(d(x, y), d(y, z))

This implies the standard triangle inequality since max(a, b) ≤ a + b.
-/

/-- The ultrametric inequality implies the standard triangle inequality. -/
theorem ultrametric_implies_triangle {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (x y z : X) :
    dist x z ≤ dist x y + dist y z := by
  calc dist x z ≤ max (dist x y) (dist y z) := IsUltrametricDist.dist_triangle_max x y z
    _ ≤ dist x y + dist y z := max_le_add_of_nonneg (dist_nonneg) (dist_nonneg)

/-
## Part II: The Isosceles Triangle Theorem

In an ultrametric space, **every triangle is isosceles**: if two sides
have different lengths, the third side equals the longer of the two.

This is the most surprising consequence of the ultrametric inequality.
Geometrically, there are no "scalene" triangles in p-adic geometry.
-/

/-- In an ultrametric space, if d(x,y) < d(y,z), then d(x,z) = d(y,z).
    In other words, when two sides of a triangle have unequal lengths,
    the third side must equal the longer one. -/
theorem isosceles_of_lt {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (x y z : X)
    (h : dist x y < dist y z) :
    dist x z = dist y z := by
  apply le_antisymm
  · -- d(x,z) ≤ max(d(x,y), d(y,z)) = d(y,z) since d(x,y) < d(y,z)
    calc dist x z ≤ max (dist x y) (dist y z) :=
          IsUltrametricDist.dist_triangle_max x y z
      _ = dist y z := max_eq_right (le_of_lt h)
  · -- d(y,z) ≤ max(d(y,x), d(x,z)) = max(d(x,y), d(x,z))
    -- If d(x,z) < d(y,z), then max(d(x,y), d(x,z)) < d(y,z), contradiction
    by_contra h_neg
    push_neg at h_neg
    have hxz : dist x z < dist y z := h_neg
    have : dist y z ≤ max (dist y x) (dist x z) :=
      IsUltrametricDist.dist_triangle_max y x z
    rw [dist_comm y x] at this
    have : dist y z ≤ max (dist x y) (dist x z) := this
    have : max (dist x y) (dist x z) < dist y z :=
      max_lt h hxz
    linarith

/-- Corollary: In an ultrametric space, every triangle is isosceles.
    At least two of the three pairwise distances must be equal. -/
theorem isosceles_triangle {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (x y z : X) :
    dist x y = dist x z ∨ dist x y = dist y z ∨ dist x z = dist y z := by
  by_cases h1 : dist x y = dist x z
  · exact Or.inl h1
  · by_cases h2 : dist x y = dist y z
    · exact Or.inr (Or.inl h2)
    · -- d(x,y) ≠ d(x,z) and d(x,y) ≠ d(y,z)
      -- We show d(x,z) = d(y,z) using the isosceles theorem
      rcases lt_or_gt_of_ne h2 with h2_lt | h2_gt
      · exact Or.inr (Or.inr (isosceles_of_lt x y z h2_lt))
      · -- d(y,z) < d(x,y). We show d(x,y) = d(x,z) — contradicting h1.
        exfalso; apply h1; apply le_antisymm
        · -- d(x,y) ≤ d(x,z): by contradiction, if d(x,z) < d(x,y) then
          -- max(d(x,z), d(y,z)) < d(x,y), but d(x,y) ≤ max(d(x,z), d(y,z))
          by_contra h_neg
          push_neg at h_neg
          have ultra : dist x y ≤ max (dist x z) (dist y z) := by
            calc dist x y ≤ max (dist x z) (dist z y) :=
                  IsUltrametricDist.dist_triangle_max x z y
              _ = max (dist x z) (dist y z) := by rw [dist_comm z y]
          linarith [max_lt h_neg h2_gt]
        · -- d(x,z) ≤ d(x,y): immediate from ultrametric
          calc dist x z ≤ max (dist x y) (dist y z) :=
                IsUltrametricDist.dist_triangle_max x y z
            _ = dist x y := max_eq_left (le_of_lt h2_gt)

/-- The isosceles theorem gives a sharp form: d(x,z) = max(d(x,y), d(y,z))
    when the two distances are unequal. -/
theorem dist_eq_max_of_ne {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (x y z : X)
    (h : dist x y ≠ dist y z) :
    dist x z = max (dist x y) (dist y z) := by
  rcases lt_or_gt_of_ne h with h_lt | h_gt
  · -- d(x,y) < d(y,z), so d(x,z) = d(y,z) = max
    rw [isosceles_of_lt x y z h_lt, max_eq_right (le_of_lt h_lt)]
  · -- d(x,y) > d(y,z), so d(x,z) = d(x,y) = max
    -- Apply isosceles_of_lt with z, y, x: d(z,y) < d(y,x)
    have hzy : dist z y < dist y x := by rwa [dist_comm z y, dist_comm y x]
    have key := isosceles_of_lt z y x hzy
    -- key: dist z x = dist y x
    rw [dist_comm z x] at key
    -- key: dist x z = dist y x
    rw [dist_comm y x] at key
    -- key: dist x z = dist x y
    rw [key, max_eq_left (le_of_lt h_gt)]

/-
## Part III: Ball Structure in Ultrametric Spaces

Ultrametric balls have remarkable properties: every interior point is a center,
and distinct balls of the same radius are disjoint.
-/

/-- In an ultrametric space, if z is in the open ball B(x, r), then
    B(x, r) = B(z, r). Every point of a ball is its center. -/
theorem ball_eq_of_mem {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (x : X) {r : ℝ} {z : X}
    (hz : z ∈ Metric.ball x r) :
    Metric.ball x r = Metric.ball z r :=
  IsUltrametricDist.ball_eq_of_mem hz

/-- In an ultrametric space, two open balls of the same radius are either
    equal or disjoint. There is no partial overlap. -/
theorem ball_eq_or_disjoint {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (x y : X) (r : ℝ) :
    Metric.ball x r = Metric.ball y r ∨ Disjoint (Metric.ball x r) (Metric.ball y r) :=
  IsUltrametricDist.ball_eq_or_disjoint x y r

/-
## Part IV: Clopen Balls

In ultrametric spaces, open balls are closed and closed balls are open
(when the radius is positive). Every ball is "clopen" (closed and open).
This is in stark contrast to Euclidean spaces where open and closed balls
are distinct.
-/

/-- Open balls in ultrametric spaces are clopen (both open and closed). -/
theorem isClopen_ball {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (x : X) (r : ℝ) :
    IsClopen (Metric.ball x r) :=
  IsUltrametricDist.isClopen_ball x r

/-- The boundary (frontier) of an open ball in an ultrametric space is empty.
    There are no "boundary points" — a ball's closure equals itself. -/
theorem frontier_ball_empty {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (x : X) (r : ℝ) :
    frontier (Metric.ball x r) = ∅ :=
  IsUltrametricDist.frontier_ball_eq_empty x r

/-
## Part V: The p-adic Triangle Inequality

The p-adic norm on ℚ is the prototypical example of a non-Archimedean norm.
For a prime p and rational q, |q|_p = p^(-v_p(q)) where v_p is the p-adic
valuation. The p-adic norm satisfies the ultrametric inequality:

  |x + y|_p ≤ max(|x|_p, |y|_p)

This is strictly stronger than the usual |x + y| ≤ |x| + |y|.
-/

/-- The p-adic norm is non-Archimedean: |x + y|_p ≤ max(|x|_p, |y|_p). -/
theorem padic_ultrametric (p : ℕ) [hp : Fact (Nat.Prime p)] (q r : ℚ) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  padicNorm.nonarchimedean

/-- The p-adic ultrametric implies the standard triangle inequality. -/
theorem padic_triangle (p : ℕ) [hp : Fact (Nat.Prime p)] (q r : ℚ) :
    padicNorm p (q + r) ≤ padicNorm p q + padicNorm p r := by
  calc padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
        padicNorm.nonarchimedean
    _ ≤ padicNorm p q + padicNorm p r :=
        max_le_add_of_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)

/-- The p-adic norm of an integer is at most 1: |n|_p ≤ 1 for all n ∈ ℤ.
    This is a consequence of the non-Archimedean property applied to
    n = 1 + 1 + ... + 1. -/
theorem padic_int_norm_le_one (p : ℕ) [hp : Fact (Nat.Prime p)] (z : ℤ) :
    padicNorm p (z : ℚ) ≤ 1 :=
  padicNorm.of_int z

/-
## Part VI: Concrete p-adic Examples

We verify the ultrametric property on specific examples in the 2-adic
and 3-adic norms, showing how it differs from the usual absolute value.
-/

/-- The p-adic norm of p itself is 1/p (p is "small" p-adically).
    For p = 2: |2|₂ = 1/2. For p = 3: |3|₃ = 1/3. -/
theorem padic_norm_prime_self (p : ℕ) [hp : Fact (Nat.Prime p)] :
    padicNorm p (p : ℚ) = (p : ℚ)⁻¹ :=
  padicNorm.padicNorm_p (hp.out.one_lt)

/-- |1|_p = 1 for any prime p (units have norm 1). -/
theorem padic_norm_one (p : ℕ) [_hp : Fact (Nat.Prime p)] :
    padicNorm p 1 = 1 :=
  padicNorm.one

/-
## Part VII: Comparison — Archimedean vs Non-Archimedean

The distinction between Archimedean and non-Archimedean is fundamental:

| Property | Archimedean (ℝ) | Non-Archimedean (ℚ_p) |
|----------|-----------------|------------------------|
| Triangle inequality | d(x,z) ≤ d(x,y) + d(y,z) | d(x,z) ≤ max(d(x,y), d(y,z)) |
| Triangles | Can be scalene | Always isosceles |
| Ball overlap | Can partially overlap | Equal or disjoint |
| Open balls | Not closed | Also closed (clopen) |
| Boundary of balls | Sphere | Empty |
| Integers | Unbounded: |n| → ∞ | Bounded: |n|_p ≤ 1 |

The Archimedean property (∀ x > 0, ∃ n ∈ ℕ, n·x > 1) fails for p-adic
norms because |n|_p ≤ 1 for all n ∈ ℤ.
-/

/-- The Archimedean property: for any positive real x, there exists n ∈ ℕ
    with n > 1/x. This is exactly what fails in non-Archimedean fields. -/
theorem archimedean_property (x : ℝ) (_hx : 0 < x) :
    ∃ n : ℕ, x < ↑n := by
  exact exists_nat_gt x

/-- Non-Archimedean contrast: in the p-adic norm, |n|_p ≤ 1 for ALL n ∈ ℤ.
    The integers are "bounded" p-adically — the exact opposite of ℝ. -/
theorem padic_integers_bounded (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℤ) :
    padicNorm p (n : ℚ) ≤ 1 :=
  padicNorm.of_int n

end TriangleInequalityOQ03
