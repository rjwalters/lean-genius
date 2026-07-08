/-
Erdős Problem #504: Maximum Angle in Point Sets (Blumenthal's Problem)

Source: https://erdosproblems.com/504
Status: SOLVED (Sendov, 1993)

Statement:
Let α_n be the supremum of all 0 ≤ α ≤ π such that in every set A ⊂ ℝ²
of n points there exist three distinct points x, y, z ∈ A such that the
angle ∠xyz (at vertex y) is at least α.

Determine α_n.

Solution (Sendov, 1993):
- α_N = π(1 - 1/n) for 2^{n-1} + 2^{n-3} < N ≤ 2^n
- α_N = π(1 - 1/(2n-1)) for 2^{n-1} < N ≤ 2^{n-1} + 2^{n-3}

Historical Development:
- Szekeres (1941): Initial bounds
- Erdős-Szekeres (1960): Proved α_{2^n} = α_{2^{n}-1} = π(1 - 1/n)
- Sendov (1992): Disproved the broader Erdős-Szekeres conjecture
- Sendov (1993): Complete solution

Key Insight:
The optimal configurations are related to vertices of regular polygons.
For 2^n points, the regular 2^n-gon achieves the minimum maximum angle.

References:
- Szekeres (1941)
- Erdős-Szekeres (1960)
- Sendov (1992, 1993)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull

open Real Set

namespace Erdos504

/- ## Part I: Basic Definitions -/

/--
**Angle Between Three Points**

Given three distinct points x, y, z ∈ ℝ², the angle ∠xyz is the angle
at vertex y formed by rays yx and yz.

The angle is measured in radians and lies in [0, π].
-/
noncomputable def angle (x y z : ℝ × ℝ) : ℝ :=
  let v1 := (x.1 - y.1, x.2 - y.2)
  let v2 := (z.1 - y.1, z.2 - y.2)
  let dot := v1.1 * v2.1 + v1.2 * v2.2
  let norm1 := Real.sqrt (v1.1^2 + v1.2^2)
  let norm2 := Real.sqrt (v2.1^2 + v2.2^2)
  if norm1 = 0 ∨ norm2 = 0 then 0
  else Real.arccos (dot / (norm1 * norm2))

/- ## Part II: Maximum Angle in a Point Set -/

/--
**Maximum Angle in a Finite Set**

Given a finite set A of points in ℝ², the maximum angle is the largest
angle ∠xyz that can be formed with three distinct points x, y, z ∈ A.
-/
noncomputable axiom maxAngleInSet (A : Finset (ℝ × ℝ)) : ℝ

/- ## Part III: The α_n Function -/

/--
**The α_n Function**

α_n = inf { maxAngleInSet(A) : A ⊂ ℝ², |A| = n }

This is the infimum of the maximum angle over all n-point sets.
Equivalently, it's the supremum of α such that every n-point set
contains three points forming an angle ≥ α.
-/
noncomputable def alphaN (n : ℕ) : ℝ :=
  ⨅ (A : Finset (ℝ × ℝ)) (_ : A.card = n), maxAngleInSet A

/- ## Part IV: Small Cases -/

/- ## Part V: Erdős-Szekeres Results (1960) -/

/--
**Erdős-Szekeres Theorem (1960)**

For powers of 2, the minimum maximum angle is achieved by regular polygons:
α_{2^n} = α_{2^n - 1} = π(1 - 1/n)
-/

/-- The formula for 2^n points per Erdős-Szekeres. -/
noncomputable def erdosSzekeresFormula (n : ℕ) : ℝ := π * (1 - 1 / n)

/- ## Part VI: Sendov's Complete Solution (1993) -/

/--
**Sendov's Formula (1993)**

The complete determination of α_N:

1. For 2^{n-1} + 2^{n-3} < N ≤ 2^n:
   α_N = π(1 - 1/n)

2. For 2^{n-1} < N ≤ 2^{n-1} + 2^{n-3}:
   α_N = π(1 - 1/(2n-1))

This was proved by Sendov in 1993, settling the problem completely.
-/

/-- Sendov's formula for the "upper range". -/
noncomputable def sendovUpperFormula (n : ℕ) : ℝ := π * (1 - 1 / n)

/-- Sendov's formula for the "lower range". -/
noncomputable def sendovLowerFormula (n : ℕ) : ℝ := π * (1 - 1 / (2 * n - 1))

/--
**Sendov's Theorem (1993) - Upper Range**

For 2^{n-1} + 2^{n-3} < N ≤ 2^n, we have α_N = π(1 - 1/n).
-/
axiom sendov_upper (n N : ℕ) (hn : n ≥ 3)
    (hLower : 2^(n-1) + 2^(n-3) < N) (hUpper : N ≤ 2^n) :
    alphaN N = sendovUpperFormula n

/--
**Sendov's Theorem (1993) - Lower Range**

For 2^{n-1} < N ≤ 2^{n-1} + 2^{n-3}, we have α_N = π(1 - 1/(2n-1)).
-/
axiom sendov_lower (n N : ℕ) (hn : n ≥ 3)
    (hLower : 2^(n-1) < N) (hUpper : N ≤ 2^(n-1) + 2^(n-3)) :
    alphaN N = sendovLowerFormula n

/- ## Part VII: Counterexample to Erdős-Szekeres Conjecture -/

/--
**Sendov's Counterexample (1992)**

Erdős and Szekeres conjectured that α_N = π(1 - 1/n) for all N
with 2^{n-1} < N ≤ 2^n. Sendov disproved this in 1992.

The counterexample shows that in the range 2^{n-1} < N ≤ 2^{n-1} + 2^{n-3},
the optimal value is different: α_N = π(1 - 1/(2n-1)).

**Derived, not assumed.** This is now a *theorem*: it is an immediate consequence
of `sendov_lower`. Take `n = 3`, `N = 5` (so `2^{n-1} = 4 < 5 ≤ 5 = 2^{n-1}+2^{n-3}`):
`sendov_lower` gives `α₅ = π(1 - 1/5)`, whereas the Erdős–Szekeres formula predicts
`π(1 - 1/3)`, and `π(1 - 1/5) ≠ π(1 - 1/3)` since `π ≠ 0` and `4/5 ≠ 2/3`. -/
theorem erdos_szekeres_conjecture_false :
    ∃ n N : ℕ, n ≥ 3 ∧ 2^(n-1) < N ∧ N ≤ 2^n ∧
    alphaN N ≠ erdosSzekeresFormula n := by
  refine ⟨3, 5, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [sendov_lower 3 5 (by norm_num) (by norm_num) (by norm_num),
    sendovLowerFormula, erdosSzekeresFormula]
  intro h
  have h2 : (1 - 1 / (2 * (3 : ℝ) - 1)) = (1 - 1 / (3 : ℝ)) := by
    push_cast at h
    exact mul_left_cancel₀ Real.pi_ne_zero h
  norm_num at h2

/- ## Part VIII: Optimal Configurations -/

/--
**Regular Polygon Configuration**

The vertices of a regular n-gon achieve the minimum maximum angle
for certain values of N related to powers of 2.

For a regular n-gon, the maximum angle formed by three vertices is
related to the central angle and inscribed angle theorems.
-/
def regularNGonVertices (n : ℕ) : Finset (ℝ × ℝ) :=
  Finset.image (fun k => (Real.cos (2 * π * k / n), Real.sin (2 * π * k / n)))
    (Finset.range n)

/- ## Part IX: Connection to Convex Position -/

/--
**Convex vs General Position**

The problem considers all point sets, not just convex position.
Interestingly, the optimal configurations achieving α_N are often
in convex position (vertices of convex polygons).
-/

/-- A finite set is in **convex position** if every one of its points is a vertex of
its convex hull — equivalently, no point lies in the convex hull of the others.

Formerly an opaque `axiom … : Prop` (an undefined predicate); now a genuine
definition, so it no longer counts as an assumption. -/
def isConvexPosition (A : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ A, a ∉ convexHull ℝ ((A.erase a : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))

/- ## Part X: Summary -/

/--
**Erdős Problem #504: Summary**

**Question:** Determine α_n, the supremum of angles α such that every
n-point set in ℝ² contains three points forming angle ≥ α.

**Status:** SOLVED (Sendov, 1993)

**Solution:**
- For 2^{n-1} + 2^{n-3} < N ≤ 2^n: α_N = π(1 - 1/n)
- For 2^{n-1} < N ≤ 2^{n-1} + 2^{n-3}: α_N = π(1 - 1/(2n-1))

**History:**
- Szekeres (1941): Initial bounds
- Erdős-Szekeres (1960): Formula for powers of 2
- Sendov (1992): Disproved the Erdős-Szekeres conjecture
- Sendov (1993): Complete solution
-/
theorem erdos_504_summary :
    -- The Sendov upper range formula
    (∀ n N : ℕ, n ≥ 3 → 2^(n-1) + 2^(n-3) < N → N ≤ 2^n →
      alphaN N = π * (1 - 1 / n)) ∧
    -- The Sendov lower range formula
    (∀ n N : ℕ, n ≥ 3 → 2^(n-1) < N → N ≤ 2^(n-1) + 2^(n-3) →
      alphaN N = π * (1 - 1 / (2 * n - 1))) ∧
    -- The Erdős-Szekeres conjecture is false
    (∃ n N : ℕ, n ≥ 3 ∧ 2^(n-1) < N ∧ N ≤ 2^n ∧
      alphaN N ≠ erdosSzekeresFormula n) :=
  ⟨fun n N hn hL hU => sendov_upper n N hn hL hU,
   fun n N hn hL hU => sendov_lower n N hn hL hU,
   erdos_szekeres_conjecture_false⟩

end Erdos504
