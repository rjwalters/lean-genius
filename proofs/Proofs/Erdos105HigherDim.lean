import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
# Erdős 105 in Higher Dimensions

## What This States
The higher-dimensional analogue of Erdős Problem #105:

Given n points A in R^d (not all in a single 2-flat) and f(n) obstacle
points B, must there exist a 2-flat containing ≥2 points of A and
avoiding all of B?

In d=2, the answer is known: the threshold is Θ(n) (Beck-Szemerédi-Trotter).
For d ≥ 3, the problem is OPEN. Szemerédi-Trotter doesn't directly
generalize, but Guth-Katz type bounds may apply.

## Status
This file formalizes the problem statement only.
No theorems about the answer — the problem is open.

## Connection to Erdos105Problem.lean
That file handles d=2 (lines). This file generalizes to d≥3 (2-flats).
-/

open scoped EuclideanGeometry

-- ============================================================
-- Definitions for the Higher-Dimensional Problem
-- ============================================================

variable (d : ℕ) (hd : 2 ≤ d)

/-- Points in R^d. -/
abbrev PointD (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A 2-flat (2-dimensional affine subspace) in R^d. -/
def TwoFlat (d : ℕ) := { S : AffineSubspace ℝ (PointD d) // S.direction.rank = 2 }

/-- A 2-flat is rich if it contains at least 2 points from A. -/
def TwoFlat.isRich (F : TwoFlat d) (A : Finset (PointD d)) : Prop :=
  2 ≤ (A.filter fun p => (p : PointD d) ∈ (F.val : Set (PointD d))).card

/-- A 2-flat is unblocked if it contains no points from B. -/
def TwoFlat.unblocked (F : TwoFlat d) (B : Finset (PointD d)) : Prop :=
  ∀ b ∈ B, (b : PointD d) ∉ (F.val : Set (PointD d))

/-- Points not all contained in a single 2-flat. -/
def NotCoplanar (A : Finset (PointD d)) : Prop :=
  ∀ F : TwoFlat d, ¬(∀ a ∈ A, (a : PointD d) ∈ (F.val : Set (PointD d)))

-- ============================================================
-- The Open Problem
-- ============================================================

/-- **Erdős 105 in R^d**: Does the threshold phenomenon persist?

For d=2, Beck and Szemerédi-Trotter proved: there exist constants
c₁, c₂ > 0 such that for any n points in general position, c₁·n
obstacles never suffice to block all rich lines, but c₂·n do.

For d ≥ 3, the question asks:
1. Does a similar threshold exist for rich 2-flats?
2. Is the threshold Θ(n) or a different function of n?
3. Does the Guth-Katz bound (on distinct distances) imply
   incidence bounds useful for this problem?

The Szemerédi-Trotter theorem (|incidences| ≤ O(n^{2/3}m^{2/3} + n + m))
is specific to points and lines in R^2. For 2-flats in R^d, the
relevant bounds come from the Guth-Katz framework and algebraic
methods (polynomial partitioning). -/
def erdos105_higher_dim_conjecture (d : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ A B : Finset (PointD d),
    A.card = n → (B.card : ℝ) ≤ c * n → NotCoplanar d A →
    ∃ F : TwoFlat d, F.isRich d A ∧ F.unblocked d B

/-
## What's Known

| Dimension | Result | Reference |
|-----------|--------|-----------|
| d = 2 | Threshold Θ(n) exists | Beck '83, Szemerédi-Trotter '83 |
| d = 2 | n-3 obstacles can block | Xichuan '24 |
| d ≥ 3 | OPEN | This problem |

## Infrastructure Needed

To make progress on d ≥ 3, one would need:
1. Incidence bounds for points and 2-flats in R^d
   (generalizing Szemerédi-Trotter)
2. Polynomial partitioning in R^d (Guth-Katz '15 framework)
3. Lower bounds on rich 2-flats from general position assumptions

None of these are currently in Mathlib.

## Possible Approaches

1. **Direct generalization**: Try to prove that cn obstacles
   cannot block all rich 2-flats, adapting the Beck/SzTr proof
   to use incidence bounds for 2-flats.

2. **Counterexample hunting**: Look for counterexamples in R^3
   where few obstacle points block all rich planes.

3. **Reduction to d=2**: Show that the d≥3 case reduces to
   the d=2 case by projecting onto a suitable 2D subspace.
-/

#check @erdos105_higher_dim_conjecture
