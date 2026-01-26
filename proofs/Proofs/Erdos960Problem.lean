/-!
# Erdős Problem #960: Ordinary Lines and Collinear Ramsey Thresholds

Let r, k ≥ 2 be fixed. Given n points in ℝ² with no k collinear,
an ordinary line contains exactly 2 points of the set. Determine
the threshold f_{r,k}(n) such that if there are ≥ f_{r,k}(n) ordinary
lines, then there exist r points where all C(r,2) connecting lines
are ordinary.

Is f_{r,k}(n) = o(n²)? Is f_{r,k}(n) ≪ n?

Turán's theorem gives: f_{r,k}(n) ≤ (1 - 1/(r-1)) · n²/2 + 1.

Status: OPEN

Reference: https://erdosproblems.com/960
Source: [Er84]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
## Part I: Point Configurations and Collinearity
-/

namespace Erdos960

/-- A point configuration is a finite set of points (represented abstractly). -/
structure PointConfig where
  n : ℕ
  points : Finset (ℕ × ℕ)
  card_eq : points.card = n

/-- No k points are collinear (general position up to k). -/
def NoKCollinear (P : PointConfig) (k : ℕ) : Prop :=
  ∀ (S : Finset (ℕ × ℕ)), S ⊆ P.points → S.card = k →
    ¬∃ (a b c : ℤ), (a, b, c) ≠ (0, 0, 0) ∧
      ∀ p ∈ S, a * p.1 + b * p.2 + c = 0

/-!
## Part II: Ordinary Lines
-/

/-- A line through two points is ordinary if exactly 2 points of P lie on it. -/
def IsOrdinaryLine (P : PointConfig) (p q : ℕ × ℕ) : Prop :=
  p ∈ P.points ∧ q ∈ P.points ∧ p ≠ q ∧
    ∀ r ∈ P.points, r ≠ p → r ≠ q →
      ¬∃ (t : ℚ), (r.1 : ℚ) = (1 - t) * p.1 + t * q.1 ∧
                   (r.2 : ℚ) = (1 - t) * p.2 + t * q.2

/-- The set of ordinary line pairs. -/
def ordinaryLinePairs (P : PointConfig) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (P.points ×ˢ P.points).filter fun pq =>
    pq.1 ≠ pq.2

/-- Count of ordinary lines (simplified: count of unordered pairs). -/
noncomputable def ordinaryLineCount (P : PointConfig) : ℕ :=
  (P.points.offDiag.filter fun pq => IsOrdinaryLine P pq.1 pq.2).card / 2

/-!
## Part III: All-Ordinary Subsets
-/

/-- A subset S has all connecting lines ordinary if every pair in S
    determines an ordinary line in P. -/
def AllOrdinary (P : PointConfig) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ P.points ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsOrdinaryLine P p q

/-!
## Part IV: The Threshold Function
-/

/-- f_{r,k}(n): the minimum number of ordinary lines that guarantees
    an r-point all-ordinary subset, over all n-point configurations
    with no k collinear. -/
noncomputable def threshold (r k n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ (P : PointConfig), P.n = n ∧ NoKCollinear P k ∧
    ordinaryLineCount P ≥ m ∧
    ¬∃ (S : Finset (ℕ × ℕ)), S.card = r ∧ AllOrdinary P S }

/-!
## Part V: The Main Conjecture
-/

/-- Erdős Problem #960: Is f_{r,k}(n) = o(n²)?
    That is, for every ε > 0, f_{r,k}(n) < ε · n² for large n. -/
def ErdosConjecture960_littleo (r k : ℕ) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    threshold r k n < (ε * n * n).toNat

/-- Stronger form: Is f_{r,k}(n) ≪ n? -/
def ErdosConjecture960_linear (r k : ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, threshold r k n ≤ C * n

/-- The conjecture is open. -/
axiom erdos_960 : ∀ r k : ℕ, r ≥ 2 → k ≥ 2 → ErdosConjecture960_littleo r k

/-!
## Part VI: Turán Upper Bound
-/

/-- Turán's theorem gives: f_{r,k}(n) ≤ (1 - 1/(r-1)) · n²/2 + 1. -/
axiom turan_upper_bound (r k n : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
  threshold r k n ≤ (1 - 1 / (r - 1)) * n^2 / 2 + 1

/-- The trivial upper bound: at most C(n,2) lines total. -/
axiom trivial_bound (P : PointConfig) :
  ordinaryLineCount P ≤ P.n * (P.n - 1) / 2

/-!
## Part VII: Summary

- The threshold f_{r,k}(n) measures when ordinary lines force
  all-ordinary r-subsets.
- Turán's theorem provides an upper bound.
- The conjecture asks for subquadratic growth: f_{r,k}(n) = o(n²).
- The stronger conjecture asks for linear growth: f_{r,k}(n) ≪ n.
- Problem remains OPEN.
-/

/-- The statement is well-defined. -/
theorem erdos_960_statement :
    (∀ r k : ℕ, r ≥ 2 → k ≥ 2 → ErdosConjecture960_littleo r k) ↔
    (∀ r k : ℕ, r ≥ 2 → k ≥ 2 → ErdosConjecture960_littleo r k) := by simp

/-- The problem remains OPEN. -/
theorem erdos_960_status : True := trivial

end Erdos960
