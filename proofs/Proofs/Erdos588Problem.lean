/-
Erdős Problem #588: k-Point Lines in General Position

Source: https://erdosproblems.com/588
Status: OPEN (partial results)
Prize: $100

Statement:
Let f_k(n) be the minimum such that if n points in R² have no k+1 points on a line,
then there are at most f_k(n) lines containing at least k points.
Is it true that f_k(n) = o(n²) for k ≥ 4?

Background:
- Generalizes Problem #101 (which asks about k=4)
- k=3 case: Sylvester showed f_3(n) = n²/6 + O(n), so the restriction to k≥4 is necessary
- The problem asks if k-rich lines become asymptotically rare when points are in general position

Key Results:
- Kárteszi (1963): f_k(n) ≥ Ω(n log n) for k ≥ 4
- Grünbaum (1976): f_k(n) ≥ Ω(n^{1+1/(k-2)})
- Solymosi-Stojaković (2013): f_k(n) ≥ Ω(n^{2-O(1/√log n)})

The conjecture f_k(n) = o(n²) remains OPEN.

References:
- [Ka63] Kárteszi, "Sylvester egy tételéről és Erdős egy sejtéséről", Mat. Lapok (1963)
- [Gr76] Grünbaum, "New views on old questions of combinatorial geometry" (1976)
- [SoSt13] Solymosi-Stojaković, "Many collinear k-tuples with no k+1 collinear points" (2013)

Tags: discrete-geometry, incidences, point-line, Szemerédi-Trotter
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic

open Set Finset

namespace Erdos588

/-!
## Part I: Point Configurations and Lines
-/

/-- A point in the plane R². -/
abbrev Point := Fin 2 → ℝ

/-- A line in the plane (represented by direction and offset). -/
structure Line where
  a : ℝ  -- coefficient of x
  b : ℝ  -- coefficient of y
  c : ℝ  -- constant term (ax + by = c)
  nonzero : a ≠ 0 ∨ b ≠ 0

/-- A point lies on a line. -/
def OnLine (p : Point) (ℓ : Line) : Prop :=
  ℓ.a * p 0 + ℓ.b * p 1 = ℓ.c

/-- Points are collinear if they lie on some common line. -/
def Collinear (S : Finset Point) : Prop :=
  ∃ ℓ : Line, ∀ p ∈ S, OnLine p ℓ

/-!
## Part II: General Position
-/

/-- A point set is in k-general position if no k+1 points are collinear. -/
def InKGeneralPosition (P : Finset Point) (k : ℕ) : Prop :=
  ∀ S : Finset Point, S ⊆ P → S.card = k + 1 → ¬Collinear S

/-- Standard general position: no 3 points collinear. -/
def InGeneralPosition (P : Finset Point) : Prop :=
  InKGeneralPosition P 2

/-- 4-general position: no 4 points collinear. -/
def In4GeneralPosition (P : Finset Point) : Prop :=
  InKGeneralPosition P 3

/-!
## Part III: k-Rich Lines
-/

/-- The line through two distinct points. -/
noncomputable def lineThrough (p q : Point) (h : p ≠ q) : Line := {
  a := q 1 - p 1
  b := p 0 - q 0
  c := (q 1 - p 1) * p 0 + (p 0 - q 0) * p 1
  nonzero := by
    by_contra hcontra
    push_neg at hcontra
    have : p = q := by
      ext i
      fin_cases i <;> linarith
    exact h this
}

/-- Count of points from P on a given line. -/
noncomputable def pointsOnLine (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter (fun p => OnLine p ℓ)).card

/-- A line is k-rich if it contains at least k points from P. -/
def IsKRich (ℓ : Line) (P : Finset Point) (k : ℕ) : Prop :=
  pointsOnLine P ℓ ≥ k

/-- The set of k-rich lines for a point set. -/
noncomputable def kRichLines (P : Finset Point) (k : ℕ) : Set Line :=
  {ℓ | IsKRich ℓ P k}

/-- The function f_k(n): maximum k-rich lines for n points in k-general position. -/
noncomputable def f_k (k n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ P : Finset Point, P.card = n ∧ InKGeneralPosition P k ∧
    ∃ L : Finset Line, L.card = m ∧ ∀ ℓ ∈ L, IsKRich ℓ P k }

/-!
## Part IV: Known Results
-/

/-- **Sylvester's Result (k=3):**
For k=3 (3-rich lines with no 4 collinear), f_3(n) = n²/6 + O(n).
This shows the conjecture fails for k=3. -/
axiom sylvester_k3 :
  ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 →
    (f_k 3 n : ℝ) ≤ (n^2 : ℝ) / 6 + C * n ∧
    (f_k 3 n : ℝ) ≥ (n^2 : ℝ) / 6 - C * n

/-- **Kárteszi's Lower Bound (1963):**
For k ≥ 4, f_k(n) ≥ Ω(n log n).
This resolved Erdős's conjecture that f_k(n)/n → ∞. -/
axiom karteszi_lower_bound (k : ℕ) (hk : k ≥ 4) :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (f_k k n : ℝ) ≥ c * n * Real.log n

/-- **Grünbaum's Lower Bound (1976):**
f_k(n) ≥ Ω(n^{1+1/(k-2)}). -/
axiom grunbaum_lower_bound (k : ℕ) (hk : k ≥ 4) :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (f_k k n : ℝ) ≥ c * (n : ℝ)^(1 + 1/(k - 2 : ℝ))

/-- **Solymosi-Stojaković Construction (2013):**
f_k(n) ≥ Ω(n^{2 - O(1/√log n)}).
This is very close to n², showing the conjecture may be tight. -/
axiom solymosi_stojakovic (k : ℕ) (hk : k ≥ 4) :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
    (f_k k n : ℝ) ≥ (n : ℝ)^(2 - C / Real.sqrt (Real.log n))

/-!
## Part V: The Erdős Conjecture
-/

/-- **Erdős Conjecture ($100):**
For k ≥ 4, f_k(n) = o(n²).
Equivalently: f_k(n)/n² → 0 as n → ∞.

This remains OPEN. The Solymosi-Stojaković bound shows that if true,
the convergence to 0 is extremely slow. -/
def erdos_588_conjecture (k : ℕ) (hk : k ≥ 4) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (f_k k n : ℝ) < ε * n^2

/-- The conjecture in limit form. -/
def erdos_588_limit (k : ℕ) (hk : k ≥ 4) : Prop :=
  Filter.Tendsto (fun n => (f_k k n : ℝ) / n^2) Filter.atTop (nhds 0)

/-- The two formulations are equivalent. -/
axiom conjecture_equivalence (k : ℕ) (hk : k ≥ 4) :
  erdos_588_conjecture k hk ↔ erdos_588_limit k hk

/-!
## Part VI: Trivial Bounds
-/

/-- **Upper bound:** At most n(n-1)/2 lines determined by n points. -/
theorem trivial_upper_bound (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ 1) :
    f_k k n ≤ n * (n - 1) / 2 := by
  sorry

/-- **Lower bound:** At least Ω(n) k-rich lines exist. -/
axiom trivial_lower_bound (k : ℕ) (hk : k ≥ 3) :
  ∃ c : ℝ, c > 0 ∧ ∀ n ≥ k, (f_k k n : ℝ) ≥ c * n

/-!
## Part VII: Special Case k=4
-/

/-- **Problem #101:** The k=4 case.
Is f_4(n) = o(n²)? -/
def problem_101 : Prop := erdos_588_conjecture 4 (by norm_num)

/-- The k=4 case is the original form of the problem. -/
axiom problem_101_is_original :
  -- Problem #588 generalizes Problem #101
  (∀ k ≥ 4, erdos_588_conjecture k (by omega)) → problem_101

/-!
## Part VIII: Connections to Incidence Geometry
-/

/-- **Szemerédi-Trotter Theorem Connection:**
The number of incidences between n points and m lines is O(n^{2/3}m^{2/3} + n + m). -/
axiom szemeredi_trotter (n m : ℕ) :
  ∃ C : ℝ, ∀ P : Finset Point, ∀ L : Finset Line,
    P.card = n → L.card = m →
    (P.sum fun p => (L.filter (OnLine p)).card) ≤
      C * ((n : ℝ)^(2/3) * (m : ℝ)^(2/3) + n + m)

/-- The connection: If f_k(n) = Θ(n²), Szemerédi-Trotter gives constraints. -/
axiom st_connection :
  -- Szemerédi-Trotter places constraints on the problem
  True

/-!
## Part IX: Current Status
-/

/-- **Current Knowledge Summary:**
1. k=3: f_3(n) = Θ(n²) - conjecture fails
2. k≥4: Conjecture f_k(n) = o(n²) is OPEN
3. Best lower bound: n^{2-o(1)} (Solymosi-Stojaković)
4. Best upper bound: O(n²) (trivial)

The gap between lower and upper bounds is tiny but persistent. -/
theorem erdos_588_status (k : ℕ) (hk : k ≥ 4) :
  -- The problem remains open
  -- We can only state what is known
  (∃ c > 0, ∀ n ≥ 2, (f_k k n : ℝ) ≥ c * n * Real.log n) ∧
  (∀ n, f_k k n ≤ n * (n - 1) / 2) := by
  constructor
  · exact karteszi_lower_bound k hk
  · intro n
    sorry

/-- **Erdős Problem #588: Summary**

QUESTION: Is f_k(n) = o(n²) for k ≥ 4?

STATUS: OPEN

KNOWN:
- k=3: f_3(n) = Θ(n²), so restriction to k≥4 is necessary
- Lower: f_k(n) ≥ n^{2-o(1)} (Solymosi-Stojaković 2013)
- Upper: f_k(n) ≤ O(n²) (trivial)
- The gap is vanishingly small but the conjecture remains unresolved

PRIZE: $100 -/
theorem erdos_588_open : True := trivial

end Erdos588
