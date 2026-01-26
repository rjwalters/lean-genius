/-!
# Erdős Problem #90 — The Unit Distance Problem

Given n points in the plane ℝ², what is the maximum number u(n) of pairs
at unit distance apart? Erdős (1946) conjectured u(n) = n^{1+O(1/log log n)}.

Known results:
- Upper bound: u(n) = O(n^{4/3}) (Spencer–Szemerédi–Trotter 1984)
- Lower bound: u(n) ≥ n^{1+c/log log n} for some c > 0 (lattice constructions)
- The upper bound cannot be improved by methods that work in general metrics (Valtr)

$500 prize offered by Erdős.

Reference: https://erdosproblems.com/90
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## Unit Distance Counting -/

/-- Count unordered pairs of distinct points at unit distance -/
noncomputable def unitDistancePairsCount (points : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (points.offDiag.filter (fun p => dist p.1 p.2 = 1)).card / 2

/-- The set of achievable unit distance counts for n-point configurations -/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistancePairsCount pts |
    (pts : Finset (EuclideanSpace ℝ (Fin 2))) (_ : pts.card = n)}

/-- The maximum number of unit distances among n points in the plane -/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)

/-! ## Trivial Bound -/

/-- The set of unit distance counts is bounded above by C(n,2),
    the total number of pairs -/
axiom unitDistanceCounts_bddAbove (n : ℕ) :
  BddAbove (unitDistanceCounts n)

/-! ## Spencer–Szemerédi–Trotter Upper Bound -/

/-- u(n) = O(n^{4/3}): the best known upper bound on unit distances.
    Proved by Spencer, Szemerédi, and Trotter (1984) using the
    Szemerédi–Trotter incidence theorem. -/
axiom spencer_szemeredi_trotter :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, 1 ≤ n →
      (maxUnitDistances n : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3)

/-! ## Lattice Lower Bound -/

/-- There exist n-point configurations with n^{1+c/log log n} unit distances
    for some constant c > 0, achieved by lattice-point constructions -/
axiom lattice_lower_bound :
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n in Filter.atTop,
      (n : ℝ) ^ (1 + c / Real.log (Real.log (n : ℝ))) ≤ (maxUnitDistances n : ℝ)

/-! ## The Erdős Conjecture -/

/-- Erdős Problem 90: u(n) = n^{1+O(1/log log n)}, i.e. the maximum number of
    unit distances among n points in ℝ² is at most n^{1+O(1/log log n)}.
    This would match the lattice lower bound up to the constant in the exponent.
    $500 prize. Open since 1946. -/
axiom ErdosProblem90 :
  ∃ C : ℝ, C > 0 ∧
    ∀ᶠ n in Filter.atTop,
      (maxUnitDistances n : ℝ) ≤ (n : ℝ) ^ (1 + C / Real.log (Real.log (n : ℝ)))

/-- Stronger form: u(n) = n^{1+o(1)}, meaning the exponent approaches 1.
    Erdős offered $300 (later $250) for this weaker conjecture. -/
axiom erdos_90_weak :
  ∀ ε : ℝ, ε > 0 →
    ∀ᶠ n in Filter.atTop,
      (maxUnitDistances n : ℝ) ≤ (n : ℝ) ^ (1 + ε)

/-! ## Valtr's Obstruction -/

/-- Valtr showed that there exists a metric on ℝ² (not Euclidean) where
    n points can have Θ(n^{4/3}) unit distances. This means any improvement
    over the n^{4/3} upper bound must use specific properties of Euclidean
    distance, not just the incidence structure. -/
axiom valtr_obstruction :
  ∃ (d : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ),
    (∀ x y, d x y = d y x) ∧ (∀ x y, 0 ≤ d x y) ∧
    (∀ x, d x x = 0) ∧
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ n in Filter.atTop,
        ∃ pts : Finset (EuclideanSpace ℝ (Fin 2)),
          pts.card = n ∧
          c * (n : ℝ) ^ ((4 : ℝ) / 3) ≤
            ((pts.offDiag.filter (fun p => d p.1 p.2 = 1)).card / 2 : ℝ)
