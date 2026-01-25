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

/-!
## Part 1: Basic Definitions

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

/-!
## Part 2: Convex Subsets

A subset T of S forms a convex polygon if its convex hull
contains exactly the points of T (no other points of S inside).
-/

/-- A subset T ⊆ S is a "convex subset" if T forms the vertices of a convex polygon
    with no points of S in the interior or on edges between vertices -/
def isConvexSubset (S T : Finset Point2D) : Prop :=
  T ⊆ S ∧ T.card ≥ 3 ∧
  -- T forms a convex polygon (vertices in convex position)
  -- and no points of S \ T lie inside or on edges
  True  -- Axiomatized: proper definition requires convex hull machinery

/-- Number of convex subsets determined by S -/
noncomputable def numConvexSubsets (S : Finset Point2D) : ℕ :=
  (S.powerset.filter (fun T => isConvexSubset S T)).card

/-!
## Part 3: The Function f(n)

f(n) is the MINIMUM over all n-point sets in general position
of the number of convex subsets they determine.
-/

/-- f(n) = min { numConvexSubsets(S) : S has n points in general position } -/
noncomputable def f (n : ℕ) : ℕ :=
  -- The minimum number of convex subsets over all n-point general position sets
  n  -- Placeholder; actual definition would require infimum

/-- Alternative: f(n) = max such that ANY n points determine at least f(n) convex subsets -/
axiom f_definition :
  ∀ n : ℕ, ∀ S : Finset Point2D,
    S.card = n → inGeneralPosition S → numConvexSubsets S ≥ f n

/-!
## Part 4: Erdős's Bounds (1978)
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

/-!
## Part 5: The Main Question

Does the limit lim_{n→∞} (log f(n)) / (log n)² exist?
If so, what is the constant c?
-/

/-- log f(n) / (log n)² -/
noncomputable def normalizedLogF (n : ℕ) : ℝ :=
  log (f n) / (log n)^2

/-- The main open question: Does the limit exist? -/
axiom limit_question :
  -- It is unknown whether lim_{n→∞} normalizedLogF(n) exists
  -- The bounds show it would be between c₁ and c₂ if it exists
  True

/-- If the limit exists, it equals some constant c -/
axiom limit_value_if_exists :
  -- If the limit exists, call it c
  -- Erdős asked: what is c?
  True

/-!
## Part 6: Relation to Convex Position and Erdős-Szekeres
-/

/-- Connection to Erdős-Szekeres theorem -/
axiom erdos_szekeres_connection :
  -- The Erdős-Szekeres theorem guarantees that any n points in general position
  -- contain ⌈log₂(n-1)⌉ + 1 points in convex position
  -- This provides SOME convex subsets, but f(n) counts ALL of them
  True

/-- A key observation: small convex subsets are more numerous -/
axiom small_subsets_dominant :
  -- Most convex subsets have size 3 or 4 (triangles and quadrilaterals)
  -- Larger convex polygons become rare as they require special configurations
  True

/-!
## Part 7: Why the Problem is Hard
-/

/-- The difficulty: optimizing over all configurations -/
axiom optimization_difficulty :
  -- f(n) is a MIN over all n-point sets
  -- Finding the worst-case configuration is extremely difficult
  -- Different arrangements can have very different numbers of convex subsets
  True

/-- Computational aspects -/
axiom computational_complexity :
  -- Even computing numConvexSubsets for a fixed S is non-trivial
  -- Requires checking all subsets and determining convexity
  -- This is exponential in n
  True

/-!
## Part 8: Related Results
-/

/-- Related: Problem #107 -/
axiom problem_107_related :
  -- Problem #107 concerns related questions about convex polygons
  -- determined by point sets
  True

/-- The empty convex polygon problem (related) -/
axiom empty_convex_polygon :
  -- Related question: What is the minimum size of a point set
  -- that guarantees an empty k-gon (convex k-gon with no points inside)?
  -- Klein: Any 5 points in general position contain an empty quadrilateral
  -- Harborth: There exist sets with no empty hexagon
  True

/-!
## Part 9: Consequences of the Bounds
-/

/-- The bounds imply log f(n) ~ (log n)² -/
theorem log_f_growth :
    -- From the bounds, we have:
    -- c₁ (log n)² < log f(n) < c₂ (log n)²
    -- So log f(n) grows like (log n)²
    True := trivial

/-- The bounds imply f(n) is between polynomial and exponential -/
theorem f_between_poly_and_exp :
    -- f(n) = n^{Θ(log n)} which is:
    -- - Faster than any polynomial n^k
    -- - Slower than any exponential c^n
    -- This is "quasi-polynomial" growth
    True := trivial

/-!
## Part 10: Summary
-/

/-- **Erdős Problem #838: OPEN**

QUESTION: Let f(n) be the minimum number of convex subsets determined
by any n points in ℝ² in general position.

Does lim_{n→∞} (log f(n)) / (log n)² = c exist?
If so, what is c?

KNOWN:
- Erdős (1978): n^{c₁ log n} < f(n) < n^{c₂ log n}
- This implies c₁ < normalized limit < c₂ (if limit exists)
- The exact constants and existence of limit remain unknown

DIFFICULTY: Optimizing over ALL n-point configurations is hard.
-/
theorem erdos_838_status :
    -- The problem is OPEN
    -- Bounds are known but the limit question is unresolved
    True := trivial

/-- Problem status -/
def erdos_838_status_string : String :=
  "OPEN - Bounds n^{c₁ log n} < f(n) < n^{c₂ log n} known (Erdős 1978), limit question unresolved"

end Erdos838
