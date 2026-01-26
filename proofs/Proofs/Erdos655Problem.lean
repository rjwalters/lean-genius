/-!
# Erdős Problem #655 — Distinct Distances with Concyclicity Restriction

Given n points in ℝ² such that no circle centered at any point contains
three or more other points (the "no-3-on-a-circle" condition), do the points
determine at least (1+c)n/2 distinct distances for some constant c > 0?

Known:
- Every point determines at least (n-1)/2 distinct distances
- The conjecture as stated is FALSE (equally-spaced points on a circle)
- Likely intended with stronger conditions (no 3 collinear, no 4 concyclic)

A problem of Erdős and Pach.

Reference: https://erdosproblems.com/655
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! ## Point Configurations and Distances -/

/-- A configuration of n points in ℝ² -/
def PointConfig (n : ℕ) := Fin n → EuclideanSpace ℝ (Fin 2)

/-- The set of distinct distances between pairs of points -/
noncomputable def distinctDistances (P : PointConfig n) : Finset ℝ :=
  (Finset.univ.product Finset.univ).image (fun (p : Fin n × Fin n) =>
    dist (P p.1) (P p.2)) |>.filter (· > 0)

/-- The number of distinct distances from a single point -/
noncomputable def distinctDistancesFrom (P : PointConfig n) (i : Fin n) : Finset ℝ :=
  (Finset.univ.image (fun j => dist (P i) (P j))).filter (· > 0)

/-! ## The Concyclicity Restriction -/

/-- No circle centered at any point xᵢ passes through 3 or more other points.
    Equivalently: for each i, at most 2 other points are equidistant from xᵢ. -/
def NoConcyclicTriple (P : PointConfig n) : Prop :=
  ∀ i : Fin n, ∀ r : ℝ, r > 0 →
    (Finset.univ.filter (fun j => j ≠ i ∧ dist (P i) (P j) = r)).card ≤ 2

/-- Stronger condition: no 4 points are concyclic (lie on a common circle) -/
def NoFourConcyclic (P : PointConfig n) : Prop :=
  ∀ (a b c d : Fin n),
    ({a, b, c, d} : Finset (Fin n)).card = 4 →
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
      dist center (P a) = r ∧ dist center (P b) = r ∧
      dist center (P c) = r ∧ dist center (P d) = r

/-! ## Basic Lower Bound -/

/-- Every point determines at least ⌈(n-1)/2⌉ distinct distances
    when no circle centered at it contains 3+ other points -/
axiom basic_distance_bound (n : ℕ) (hn : 2 ≤ n)
    (P : PointConfig n) (hP : Function.Injective P)
    (hC : NoConcyclicTriple P) (i : Fin n) :
  (n - 1) / 2 ≤ (distinctDistancesFrom P i).card

/-! ## Hunter's Counterexample -/

/-- Zach Hunter showed the conjecture as stated is false:
    n points equally spaced on a circle satisfy NoConcyclicTriple
    but determine only n/2 distinct distances (not (1+c)n/2) -/
axiom hunter_counterexample :
  ∀ε > 0, ∀ᶠ n in Filter.atTop,
    ∃ P : PointConfig n,
      Function.Injective P ∧ NoConcyclicTriple P ∧
      (distinctDistances P).card ≤ n / 2 + 1

/-! ## The Erdős–Pach Conjecture (Corrected Form) -/

/-- Erdős Problem 655 (Erdős–Pach, corrected): Under the stronger condition
    that no 4 points are concyclic (and no 3 collinear), do the points
    determine at least (1+c)n/2 distinct distances? -/
axiom ErdosProblem655_corrected (c : ℝ) (hc : c > 0) :
  ∀ᶠ n in Filter.atTop,
    ∀ P : PointConfig n,
      Function.Injective P → NoFourConcyclic P →
        (1 + c) * (n : ℝ) / 2 ≤ ((distinctDistances P).card : ℝ)
