/-
Erdős Problem #669: k-Point Lines - Exact and At-Least Counts

Source: https://erdosproblems.com/669
Status: OPEN (k=3 solved, general k open)

Statement:
Let F_k(n) = max lines through at least k points of any n-point set in R².
Let f_k(n) = max lines through exactly k points of any n-point set in R².
Estimate f_k(n) and F_k(n). In particular, determine lim F_k(n)/n² and lim f_k(n)/n².

Known Results:
- k=2: f_2(n) = F_2(n) = C(n,2) (trivially)
- k=3: The classical "Orchard Problem" of Sylvester
  - Burr-Grünbaum-Sloane (1974): f_3(n) = n²/6 - O(n) and F_3(n) = n²/6 - O(n)
- Trivial upper bound: F_k(n) ≤ C(n,2)/C(k,2) = n²/(k(k-1)) + O(n)
- Conjecture: lim f_k(n)/n² = lim F_k(n)/n² = 1/(k(k-1)) for all k ≥ 2

References:
- [BGS74] Burr, Grünbaum, Sloane, "The orchard problem", Geom. Dedicata (1974)
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

open Set Finset Nat

namespace Erdos669

/- ## Part I: Point and Line Definitions -/

/-- A point in the plane R². -/
abbrev Point := Fin 2 → ℝ

/-- A line in the plane (ax + by = c with (a,b) ≠ (0,0)). -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nonzero : a ≠ 0 ∨ b ≠ 0

/-- A point lies on a line. -/
def OnLine (p : Point) (ℓ : Line) : Prop :=
  ℓ.a * p 0 + ℓ.b * p 1 = ℓ.c

/-- Count of points from P on line ℓ. -/
noncomputable def pointsOnLine (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter (fun p => OnLine p ℓ)).card

/- ## Part II: f_k and F_k Functions -/

/-- A line passes through exactly k points. -/
def ExactlyKPoints (ℓ : Line) (P : Finset Point) (k : ℕ) : Prop :=
  pointsOnLine P ℓ = k

/-- A line passes through at least k points. -/
def AtLeastKPoints (ℓ : Line) (P : Finset Point) (k : ℕ) : Prop :=
  pointsOnLine P ℓ ≥ k

/-- f_k(n): Max lines with exactly k points from any n-point set. -/
noncomputable def f_k (k n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ P : Finset Point, P.card = n ∧
    ∃ L : Finset Line, L.card = m ∧ ∀ ℓ ∈ L, ExactlyKPoints ℓ P k }

/-- F_k(n): Max lines with at least k points from any n-point set. -/
noncomputable def F_k (k n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ P : Finset Point, P.card = n ∧
    ∃ L : Finset Line, L.card = m ∧ ∀ ℓ ∈ L, AtLeastKPoints ℓ P k }

/- ## Part III: The Orchard Problem (k=3) -/

/-- The Orchard Problem asks whether f_3(n) and F_3(n) are both n²/6 - O(n). -/
def orchardProblem : Prop :=
  ∃ C₁ C₂ : ℝ, ∀ n : ℕ, n ≥ 3 →
    |f_k 3 n - (n^2 : ℕ) / 6| ≤ C₁ * n ∧
    |F_k 3 n - (n^2 : ℕ) / 6| ≤ C₂ * n

/-- **Burr-Grünbaum-Sloane Theorem (1974):**
f_3(n) = n²/6 - O(n) and F_3(n) = n²/6 - O(n).
This resolves the Orchard Problem completely. -/
/-- The asymptotic limit for k=3: both f_3(n)/n² and F_3(n)/n² tend to 1/6. -/
axiom k3_limit :
  Filter.Tendsto (fun n => (f_k 3 n : ℝ) / n^2) Filter.atTop (nhds (1/6)) ∧
  Filter.Tendsto (fun n => (F_k 3 n : ℝ) / n^2) Filter.atTop (nhds (1/6))

/- ## Part IV: Trivial Upper Bound -/

/-- **Trivial upper bound:** F_k(n) ≤ C(n,2)/C(k,2).
Each line with ≥ k points contributes at least C(k,2) pairs,
and there are at most C(n,2) pairs total. -/
/-- The limiting ratio: lim F_k(n)/n² ≤ 1/(k(k-1)). -/
/- ## Part V: The General Conjecture -/

/-- **Conjecture:** The limits equal 1/(k(k-1)) for all k ≥ 2. -/
def limit_conjecture (k : ℕ) (hk : k ≥ 2) : Prop :=
  Filter.Tendsto (fun n => (f_k k n : ℝ) / n^2) Filter.atTop (nhds (1 / (k * (k - 1)))) ∧
  Filter.Tendsto (fun n => (F_k k n : ℝ) / n^2) Filter.atTop (nhds (1 / (k * (k - 1))))

/-- For k=3, the conjecture gives 1/6, which matches BGS. -/
theorem k3_matches : 1 / (3 * (3 - 1)) = 1 / 6 := by norm_num

/-- The k=3 case of the conjecture holds (follows from BGS). -/
theorem k3_conjecture_true : limit_conjecture 3 (by norm_num) :=
  k3_limit

/- ## Part VI: Optimal Configurations -/

/-- **Optimal Configurations:**
Configurations achieving f_3(n) = n²/6 - O(n) exist.
Often derived from projective plane constructions (e.g., points of PG(2,q)). -/
/- ## Part VII: Summary -/

/-- **Erdős Problem #669: OPEN (k=3 solved)**

The essential picture:
- k=3 (Orchard Problem): SOLVED by BGS (1974), both limits = 1/6
- General k: OPEN, conjectured limits = 1/(k(k-1))
- Upper bound: F_k(n)/n² ≤ 1/(k(k-1)) + o(1) -/
theorem erdos_669_summary :
    -- k=3 limit exists and equals 1/6
    (Filter.Tendsto (fun n => (f_k 3 n : ℝ) / n^2) Filter.atTop (nhds (1/6))) ∧
    (Filter.Tendsto (fun n => (F_k 3 n : ℝ) / n^2) Filter.atTop (nhds (1/6))) :=
  k3_limit

end Erdos669
