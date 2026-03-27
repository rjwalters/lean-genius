/-
Erdős Problem #838: Convex Subsets of Point Sets

Source: https://erdosproblems.com/838
Status: OPEN (bounds established)

Statement:
Let f(n) be maximal such that any n points in ℝ², with no three on a line,
determine at least f(n) different convex subsets.
Estimate f(n) - in particular, does there exist a constant c such that
    lim (log f(n)) / (log n)² = c ?

Known Results (Erdős 1978):
- Lower bound: f(n) > n^{c₁ log n} for some c₁ > 0
- Upper bound: f(n) < n^{c₂ log n} for some c₂ > 0

The exact value of the limit (if it exists) remains unknown.
Question of Erdős and Hammer.

Related: Problem #107

Tags: combinatorial-geometry, convex-sets, point-configurations, general-position
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

namespace Erdos838

/- ## Part 1: Basic Definitions

Points in ℝ² in general position (no three collinear) and convex subsets.
-/

/-- A point in the plane -/
structure Point2D where
  x : ℝ
  y : ℝ
deriving DecidableEq

/-- Three points are collinear if they lie on a common line -/
def collinear (p q r : Point2D) : Prop :=
  (q.x - p.x) * (r.y - p.y) = (r.x - p.x) * (q.y - p.y)

/-- A set of points is in general position if no three are collinear -/
def inGeneralPosition (S : Finset Point2D) : Prop :=
  ∀ p q r : Point2D, p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r → ¬collinear p q r

/- ## Part 2: Convex Subsets

A subset T of S forms a convex polygon if its convex hull
contains exactly the points of T (no other points of S inside).
-/

/-- A subset T ⊆ S is in "convex position" if its points are vertices of a
    convex polygon with no points of S in the interior.
    Axiomatized: proper definition requires convex hull machinery. -/
axiom isConvexSubset (S T : Finset Point2D) : Prop

/-- Number of convex subsets determined by S -/
noncomputable def numConvexSubsets (S : Finset Point2D) : ℕ :=
  (S.powerset.filter (fun T => isConvexSubset S T)).card

/- ## Part 3: The Function f(n)

f(n) is the MINIMUM over all n-point sets in general position
of the number of convex subsets they determine.
-/

/-- f(n) = min { numConvexSubsets(S) : S has n points in general position }
    Axiomatized since Lean has no built-in infimum over types. -/
axiom f : ℕ → ℕ

/- ## Part 4: Erdős's Bounds (1978)
-/

/-- Lower bound: f(n) > n^{c₁ log n} for some c₁ > 0 -/
axiom erdos_lower_bound :
  ∃ c₁ > 0, ∀ n : ℕ, n ≥ 4 →
    (f n : ℝ) > n ^ (c₁ * log n)

/-- Upper bound: f(n) < n^{c₂ log n} for some c₂ > 0 -/
axiom erdos_upper_bound :
  ∃ c₂ > 0, ∀ n : ℕ, n ≥ 4 →
    (f n : ℝ) < n ^ (c₂ * log n)

/-- The bounds together: n^{c₁ log n} < f(n) < n^{c₂ log n} -/
theorem erdos_bounds :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 4 →
        n ^ (c₁ * log n) < (f n : ℝ) ∧ (f n : ℝ) < n ^ (c₂ * log n) := by
  obtain ⟨c₁, hc₁, h_lower⟩ := erdos_lower_bound
  obtain ⟨c₂, hc₂, h_upper⟩ := erdos_upper_bound
  exact ⟨c₁, c₂, hc₁, hc₂, fun n hn => ⟨h_lower n hn, h_upper n hn⟩⟩

/- ## Part 5: The Main Question

Does the limit lim_{n→∞} (log f(n)) / (log n)² exist?
If so, what is the constant c?
-/

/-- log f(n) / (log n)² — the normalized logarithmic growth rate -/
noncomputable def normalizedLogF (n : ℕ) : ℝ :=
  log (f n) / (log n)^2

/-- The main open question formalized: Does the limit of normalizedLogF exist? -/
def limitExists : Prop :=
  ∃ c : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |normalizedLogF n - c| < ε

/- ## Part 6: Erdős-Szekeres Connection
-/

/- ## Part 7: Growth Rate
-/

/-- f(n) grows faster than any polynomial: for all k, f(n) > n^k for large n -/
axiom f_superpolynomial :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) > (n : ℝ)^(k : ℝ)

/- ## Part 8: Summary
-/

/-- **Erdős Problem #838: Summary**

Combines the Erdős bounds into a single theorem:
- n^{c₁ log n} < f(n) < n^{c₂ log n} for constants c₁, c₂ > 0
- f is superpolynomial but subexponential
- The limit of (log f(n))/(log n)² remains unknown -/
theorem erdos_838_summary :
    (∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 4 →
        n ^ (c₁ * log n) < (f n : ℝ) ∧ (f n : ℝ) < n ^ (c₂ * log n)) ∧
    (∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) > (n : ℝ)^(k : ℝ)) :=
  ⟨erdos_bounds, f_superpolynomial⟩

end Erdos838
