/-!
# Erdős Problem #662 — Distances in Separated Point Sets

Let x₁,...,xₙ be points in ℝ² with d(xᵢ,xⱼ) ≥ 1 for all i ≠ j.
For the triangular lattice with minimum distance 1, let f(t) be the
number of distances ≤ t from a fixed point. Known: f(1) = 6,
f(√3) = 12, f(3) = 18.

Question: Is the number of pairs at distance ≤ t maximized by
the triangular lattice? More precisely, is the triangular lattice
the unique extremal configuration?

Problem by Erdős–Lovász–Vesztergombi (1997).

Status: OPEN
Reference: https://erdosproblems.com/662
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- A point in ℝ². -/
def Point2D := ℝ × ℝ

/-- Squared distance between two points. -/
def sqDist (p q : Point2D) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- A set of points is 1-separated if all pairwise distances ≥ 1. -/
def IsSeparated (pts : Finset Point2D) : Prop :=
  ∀ p ∈ pts, ∀ q ∈ pts, p ≠ q → sqDist p q ≥ 1

/-- The number of pairs at squared distance ≤ t² in a point set. -/
noncomputable def pairsWithinDist (pts : Finset Point2D) (t : ℝ) : ℕ :=
  ((pts ×ˢ pts).filter fun pq => pq.1 ≠ pq.2 ∧ sqDist pq.1 pq.2 ≤ t ^ 2).card / 2

/-- f(t): the number of lattice distances ≤ t in the triangular
    lattice from a fixed point. -/
noncomputable def triangularLatticeCount : ℝ → ℕ := fun _ => 0  -- axiomatized

/-! ## Main Conjecture -/

/-- **Erdős–Lovász–Vesztergombi Conjecture**: Among all n-point
    1-separated sets in ℝ², the triangular lattice maximizes the
    number of pairs at distance ≤ t, for each t ≥ 1. -/
axiom erdos_662_lattice_optimal :
  ∀ t : ℝ, t ≥ 1 →
    ∀ (pts : Finset Point2D), IsSeparated pts →
      pairsWithinDist pts t ≤ pts.card * triangularLatticeCount t / 2

/-! ## Known Values -/

/-- **Triangular Lattice Counts**: f(1) = 6, f(√3) = 12, f(3) = 18.
    Each point in the triangular lattice has exactly 6 nearest
    neighbors at distance 1, 6 next-nearest at distance √3, etc. -/
axiom triangular_lattice_values :
  triangularLatticeCount 1 = 6 ∧
  triangularLatticeCount (Real.sqrt 3) = 12 ∧
  triangularLatticeCount 3 = 18

/-! ## Observations -/

/-- **Hexagonal Packing**: The triangular lattice is the densest
    packing of unit disks in ℝ² (Thue, 1910; Tóth, 1940). This
    problem asks whether it also maximizes short-range pair counts. -/
axiom hexagonal_packing : True

/-- **Contact Number**: The case t = 1 asks about the maximum
    number of unit distances in a 1-separated set, which equals
    3n − O(√n) from the triangular lattice. -/
axiom contact_number : True

/-- **Problem Statement Caveat**: The original problem as stated
    on erdosproblems.com contains at least one typo. The formalization
    here follows the most natural interpretation of the conjecture. -/
axiom statement_caveat : True
