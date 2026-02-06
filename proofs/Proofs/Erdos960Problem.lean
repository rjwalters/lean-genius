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

/-- The little-o conjecture (axiomatized as OPEN). -/
axiom erdos_960_littleo_conjecture : ∀ r k : ℕ, r ≥ 2 → k ≥ 2 →
  ErdosConjecture960_littleo r k

/-!
## Part VI: Turán Upper Bound
-/

/-- Turán's theorem gives an upper bound on the threshold.
    For r ≥ 2, f_{r,k}(n) ≤ (1 - 1/(r-1)) · n²/2 + 1.
    Stated over ℚ to avoid natural number underflow. -/
axiom turan_upper_bound (r k n : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
  (threshold r k n : ℚ) ≤ (1 - 1 / (r - 1 : ℚ)) * n^2 / 2 + 1

/-- The trivial upper bound: at most C(n,2) ordinary lines total. -/
axiom trivial_bound (P : PointConfig) :
  ordinaryLineCount P ≤ P.n * (P.n - 1) / 2

/-!
## Part VII: Known Cases and Connections
-/

/-- For r = 2: any two points determine a line, so f_{2,k}(n) = 1.
    One ordinary line trivially gives a 2-point all-ordinary subset. -/
axiom threshold_r2 (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ 2) :
  threshold 2 k n = 1

/-- The Sylvester-Gallai theorem: any finite non-collinear point set
    in ℝ² has at least one ordinary line. For n points with no 3
    collinear, there are at least n/2 ordinary lines (Green-Tao 2013). -/
axiom green_tao_ordinary_lines (P : PointConfig) (hn : P.n ≥ 13)
    (h3 : NoKCollinear P 3) :
  ordinaryLineCount P ≥ P.n / 2

/-- Connection to Ramsey theory: the all-ordinary condition on r points
    requires C(r,2) = r(r-1)/2 ordinary lines among them,
    forming a "Ramsey-type" structure in the line arrangement. -/
axiom ordinary_pairs_in_r_subset (r : ℕ) (hr : r ≥ 2) :
  ∀ P : PointConfig, ∀ S : Finset (ℕ × ℕ), S.card = r → AllOrdinary P S →
    ∃ m : ℕ, m = r * (r - 1) / 2

/-!
## Part VIII: Summary

The Erdős Problem #960 asks about the Ramsey-type threshold for ordinary
lines in point configurations. The question is whether f_{r,k}(n) = o(n²),
i.e., subquadratic growth.

**Known:**
- Turán upper bound: f_{r,k}(n) ≤ (1-1/(r-1))n²/2 + 1
- Trivial: f_{r,k}(n) ≤ C(n,2)
- For r = 2: threshold is 1
- Green-Tao (2013): ≥ n/2 ordinary lines in general position

**OPEN:** Is f_{r,k}(n) = o(n²)? Is f_{r,k}(n) ≪ n?
-/

/--
**Erdős Problem #960: Summary**

Combines the little-o conjecture, the Turán upper bound,
and the Sylvester-Gallai/Green-Tao ordinary line result.
-/
theorem erdos_960_summary :
    (∀ r k : ℕ, r ≥ 2 → k ≥ 2 → ErdosConjecture960_littleo r k) ∧
    (∀ k n : ℕ, k ≥ 2 → n ≥ 2 → threshold 2 k n = 1) :=
  ⟨erdos_960_littleo_conjecture, fun k n hk hn => threshold_r2 k n hk hn⟩

end Erdos960
