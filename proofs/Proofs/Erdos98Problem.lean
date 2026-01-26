/-!
# Erdős Problem #98 — Distinct Distances in General Position

Let h(n) be the minimum number of distinct distances determined by n points
in ℝ² with no three collinear and no four concyclic. Does h(n)/n → ∞?

Known:
- Erdős could not prove h(n) ≥ n
- Pach: h(n) < n^{log₂ 3} ≈ n^{1.585}
- Erdős–Füredi–Pach: h(n) < n · exp(c√(log n))

Reference: https://erdosproblems.com/98
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## General Position Conditions -/

/-- A point configuration in ℝ² -/
def PointConfig (n : ℕ) := Fin n → EuclideanSpace ℝ (Fin 2)

/-- No three points are collinear -/
def NoThreeCollinear (P : PointConfig n) : Prop :=
  ∀ (i j k : Fin n),
    ({i, j, k} : Finset (Fin n)).card = 3 →
    ¬∃ (a b c : ℝ), (a, b, c) ≠ (0, 0, 0) ∧
      a * (P i 0) + b * (P i 1) + c = 0 ∧
      a * (P j 0) + b * (P j 1) + c = 0 ∧
      a * (P k 0) + b * (P k 1) + c = 0

/-- No four points are concyclic -/
def NoFourConcyclic (P : PointConfig n) : Prop :=
  ∀ (a b c d : Fin n),
    ({a, b, c, d} : Finset (Fin n)).card = 4 →
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
      dist center (P a) = r ∧ dist center (P b) = r ∧
      dist center (P c) = r ∧ dist center (P d) = r

/-- A configuration is in general position: injective, no 3 collinear, no 4 concyclic -/
def InGeneralPosition (P : PointConfig n) : Prop :=
  Function.Injective P ∧ NoThreeCollinear P ∧ NoFourConcyclic P

/-! ## Distinct Distances -/

/-- The number of distinct distances in a configuration -/
noncomputable def numDistinctDistances (P : PointConfig n) : ℕ :=
  ((Finset.univ.product Finset.univ).image
    (fun (p : Fin n × Fin n) => dist (P p.1) (P p.2))
  |>.filter (· > 0)).card

/-- h(n): minimum distinct distances over all general-position configurations -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {numDistinctDistances P |
    (P : PointConfig n) (_ : InGeneralPosition P)}

/-! ## Known Upper Bounds -/

/-- Pach's bound: h(n) < n^{log₂ 3} -/
axiom pach_upper_bound :
  ∀ᶠ n in Filter.atTop,
    (h n : ℝ) < (n : ℝ) ^ (Real.log 3 / Real.log 2)

/-- Erdős–Füredi–Pach improved bound: h(n) < n · exp(c√(log n)) -/
axiom efp_upper_bound :
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n in Filter.atTop,
      (h n : ℝ) < (n : ℝ) * Real.exp (c * Real.sqrt (Real.log (n : ℝ)))

/-! ## The Erdős Conjecture -/

/-- Erdős Problem 98: h(n)/n → ∞, i.e. points in general position
    (no 3 collinear, no 4 concyclic) determine superlinearly many
    distinct distances. Open — Erdős could not even prove h(n) ≥ n. -/
axiom ErdosProblem98 :
  Filter.Tendsto (fun n => (h n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop

/-- Weaker open question: h(n) ≥ n for all large n? Even this is unknown. -/
axiom erdos_98_weak :
  ∀ᶠ n in Filter.atTop, n ≤ h n

/-! ## Connection to the General Distinct Distances Problem -/

/-- Without the general-position assumption, the Guth–Katz theorem gives
    Ω(n/log n) distinct distances for any n points. General position
    should give more, but the quantitative improvement is unknown. -/
axiom guth_katz_comparison :
  ∃ c : ℝ, c > 0 ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (P : PointConfig n),
      Function.Injective P →
        c * (n : ℝ) / Real.log (n : ℝ) ≤ (numDistinctDistances P : ℝ)
