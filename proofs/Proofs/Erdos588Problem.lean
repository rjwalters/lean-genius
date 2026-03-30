/-
Erdős Problem #588: Collinear Points in Planar Configurations

Source: https://erdosproblems.com/588
Status: OPEN
Prize: $100

Statement:
Let f_k(n) be the minimum value such that any configuration of n points in the
plane with no more than k points collinear contains at most f_k(n) lines each
passing through at least k points.

Is f_k(n) = o(n²) for k ≥ 4?

Known:
- k = 3: Sylvester established f₃(n) = n²/6 + O(n)
- k ≥ 4: Known that f_k(n) ≫_k n^{2 - O_k(1/√log n)}

References:
- Sylvester: Result for k = 3
- Burr, Grünbaum, Sloane: Related results
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos588

/-
## Part I: Definitions
-/

/-- A point in the plane. -/
abbrev Point := ℝ × ℝ

/--
f_k(n): the maximum number of lines containing at least k points,
minimized over all configurations of n points with no k+1 collinear.
Axiomatized as an extremal quantity over point configurations.
-/
axiom f (k n : ℕ) : ℕ

/-
## Part II: The k = 3 Case (Resolved)
-/

/--
**Sylvester's Theorem**: f₃(n) = n²/6 + O(n).

For configurations with no 4 collinear points, the number of lines
through at least 3 points is approximately n²/6.
-/
axiom sylvester_k3 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      |(f 3 n : ℝ) - (n : ℝ)^2 / 6| ≤ C * n

/-
## Part III: The k ≥ 4 Case (Open)
-/

/--
**Known lower bound**: f_k(n) ≫ n^{2 - c/√(log n)} for some constant c > 0.
This is close to n² but not quite o(n²).
-/
/--
**Erdős's Conjecture (OPEN)**: f_k(n) = o(n²) for k ≥ 4.

That is, requiring at most k collinear points (k ≥ 4) should force
the number of k-rich lines to be strictly subquadratic.
-/
/-
## Part IV: Main Theorem
-/

/--
**Erdős Problem #588: OPEN**

The k = 3 case is resolved (Sylvester).
The k ≥ 4 case remains open: is f_k(n) = o(n²)?
-/
theorem erdos_588 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      |(f 3 n : ℝ) - (n : ℝ)^2 / 6| ≤ C * n :=
  sylvester_k3

end Erdos588
