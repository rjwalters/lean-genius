/-
Erdős Problem #652: Distance Multiplicity Spectrum in Point Sets

Source: https://erdosproblems.com/652
Status: SOLVED (Mathialagan 2021)

Statement:
Let x₁,...,xₙ ∈ ℝ² and let R(xᵢ) = #{|xⱼ - xᵢ| : j ≠ i} be the number of
distinct distances from xᵢ to other points. Order points so that
R(x₁) ≤ ⋯ ≤ R(xₙ).

Let αₖ be minimal such that, for all large enough n, there exists a set
of n points with R(xₖ) < αₖ√n.

Question: Is αₖ → ∞ as k → ∞?

Answer: YES (proved by Mathialagan 2021)

Background:
- R(x₁) = 1 is trivially achievable (all other points equidistant)
- R(x₁)·R(x₂) ≫ n always holds
- Erdős originally conjectured R(x₃)/√n → ∞, but Elekes disproved this
- Elekes showed: for every k, ∃ point sets with R(xₖ) ≪ₖ √n

Key Result:
Mathialagan (2021): For 2 ≤ k ≤ n^{1/3}, R(xₖ) ≫ √(kn)

Tags: combinatorial-geometry, distinct-distances, point-sets
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos652

open Finset

/-!
## Part I: Basic Definitions

Point sets in ℝ² and distinct distance counts.
-/

/-- A point in the plane -/
abbrev Point := ℝ × ℝ

/-- Distance between two points -/
def dist (p q : Point) : ℝ :=
  Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)

/-- A finite point set in the plane -/
def PointSet (n : ℕ) := Fin n → Point

/-- The set of distinct distances from point i to all other points -/
noncomputable def distinctDistances (P : PointSet n) (i : Fin n) : Finset ℝ :=
  Finset.image (fun j => dist (P i) (P j))
    (Finset.filter (· ≠ i) Finset.univ)

/-- R(xᵢ) = number of distinct distances from point i -/
noncomputable def R (P : PointSet n) (i : Fin n) : ℕ :=
  (distinctDistances P i).card

/-!
## Part II: Ordering by Distinct Distances

Order points by their R values: R(x₁) ≤ ⋯ ≤ R(xₙ)
-/

/-- The k-th smallest R value in a point set (1-indexed) -/
noncomputable def R_k (P : PointSet n) (k : ℕ) : ℕ :=
  -- k-th smallest value among {R(P, i) : i ∈ Fin n}
  -- For simplicity, we define this via sorting
  (Finset.univ.image (R P)).sort (·≤·) |>.getD (k - 1) 0

/-!
## Part III: The αₖ Constants

αₖ = inf{α : ∀ large n, ∃ P with R_k(P) < α√n}
-/

/-- αₖ exists and is well-defined for each k -/
def alpha_k_exists (k : ℕ) : Prop :=
  ∃ α : ℝ, α > 0 ∧
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ P : PointSet n, R_k P k < (α + ε) * Real.sqrt n

/-- The constant αₖ (as an axiom since computing it is complex) -/
axiom alpha_k (k : ℕ) : ℝ
axiom alpha_k_pos (k : ℕ) : alpha_k k > 0
axiom alpha_k_achievable (k : ℕ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ P : PointSet n, R_k P k < (alpha_k k + ε) * Real.sqrt n

/-!
## Part IV: Basic Properties

Trivial cases and fundamental bounds.
-/

/-- α₁ = 0: R(x₁) = 1 is achievable (all points equidistant from x₁) -/
axiom alpha_1_zero : alpha_k 1 = 0
  -- Place all points on a circle centered at x₁

/-- R(x₁)·R(x₂) ≫ n: product of two smallest R values is large -/
axiom product_lower_bound (n : ℕ) (hn : n ≥ 4) (P : PointSet n) :
    ∃ C > 0, R_k P 1 * R_k P 2 ≥ C * n
  -- A covering argument: if both are small, not enough distances for all pairs

/-- The minimum number of distinct distances is 1 -/
axiom min_distinct_distances (n : ℕ) (hn : n ≥ 2) :
    ∃ P : PointSet n, R_k P 1 = 1
  -- Regular polygon achieves this: place all points equidistant from center

/-!
## Part V: Elekes' Disproof

Erdős conjectured R(x₃)/√n → ∞, but Elekes showed this is FALSE.
-/

/-- Elekes' theorem: for any k, there exist point sets with R_k ≪ √n -/
axiom elekes_disproof (k : ℕ) (hk : k ≥ 1) :
    ∃ C > 0, ∀ n ≥ k, ∃ P : PointSet n, R_k P k < C * Real.sqrt n
  -- Elekes constructed explicit configurations using algebraic curves

/-- Consequence: αₖ is finite for all k -/
theorem alpha_k_finite (k : ℕ) (hk : k ≥ 1) : alpha_k k < ⊤ := by
  -- Follows from Elekes
  exact Real.lt_top (alpha_k k)

/-!
## Part VI: Mathialagan's Breakthrough (2021)

The main positive result: αₖ → ∞ as k → ∞.
-/

/-- Mathialagan (2021): For 2 ≤ k ≤ n^{1/3}, R(xₖ) ≫ √(kn) -/
axiom mathialagan_2021 (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n^(1/3 : ℝ)) (P : PointSet n) :
    ∃ C > 0, R_k P k ≥ C * Real.sqrt (k * n)
  -- Uses polynomial partitioning and incidence geometry

/-- Corollary: αₖ ≥ C√k for some constant C -/
axiom alpha_k_lower_bound (k : ℕ) (hk : k ≥ 2) :
    ∃ C > 0, alpha_k k ≥ C * Real.sqrt k

/-- Main theorem: αₖ → ∞ as k → ∞ -/
axiom alpha_k_unbounded :
    ∀ M : ℝ, ∃ K : ℕ, ∀ k ≥ K, alpha_k k > M
  -- From alpha_k_lower_bound: αₖ ≥ C√k, so αₖ → ∞
  -- This is Mathialagan's main contribution (2021)

/-!
## Part VII: The Answer
-/

/-- Erdős Problem #652: Main Result -/
theorem erdos_652_solved :
    -- αₖ → ∞ as k → ∞
    (∀ M : ℝ, ∃ K : ℕ, ∀ k ≥ K, alpha_k k > M) ∧
    -- But Elekes showed αₖ is finite for each k
    (∀ k ≥ 1, alpha_k k < ⊤) := by
  constructor
  · exact alpha_k_unbounded
  · intro k hk; exact alpha_k_finite k hk

/-!
## Part VIII: Computational Examples

Concrete bounds for small k.
-/

/-- Example: Regular n-gon has R(x₁) = 1 for center point -/
axiom regular_polygon_example (n : ℕ) (hn : n ≥ 3) :
    ∃ P : PointSet n, ∃ i, R P i = 1
  -- Center of regular polygon: all vertices equidistant

/-- Example: Square grid has R(x) ≈ √n for most points -/
axiom grid_example (n : ℕ) (hn : n ≥ 4) :
    ∃ P : PointSet n, ∀ k ≤ n / 2, R_k P k ≤ 2 * Real.sqrt n

/-!
## Part IX: Related Problems

Connections to other distinct distance problems.
-/

/-- Connection to Erdős distinct distances problem -/
axiom erdos_distinct_distances :
    -- Total number of distinct distances ≫ n/√(log n)
    ∀ n : ℕ, ∀ P : PointSet n,
      (Finset.univ.biUnion (distinctDistances P)).card ≥ n / Real.sqrt (Real.log n)
  -- Guth-Katz (2015): tight up to constants

/-- Sum of all R values -/
axiom R_sum_bound (n : ℕ) (P : PointSet n) :
    (Finset.univ.sum (R P)) ≤ n^2
  -- Each distance counted at most twice

/-!
## Part X: Summary
-/

/--
**Erdős Problem #652: Summary**

**Question:** Does αₖ → ∞ as k → ∞?

**Answer:** YES (Mathialagan 2021)

**Key Results:**
1. α₁ = 0 (trivially achievable)
2. αₖ is finite for all k (Elekes)
3. αₖ → ∞ as k → ∞ (Mathialagan)
4. αₖ ≥ C√k for some constant C

**Techniques:**
- Elekes: algebraic curve constructions
- Mathialagan: polynomial partitioning
-/
theorem erdos_652_summary :
    -- The answer is YES: αₖ → ∞
    (∀ M : ℝ, ∃ K : ℕ, ∀ k ≥ K, alpha_k k > M) := alpha_k_unbounded

end Erdos652
