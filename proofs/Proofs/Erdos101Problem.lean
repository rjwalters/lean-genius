/-!
# Erdős Problem #101 — Four-Point Lines from Planar Point Sets

Given n points in ℝ² with no five collinear, prove that the number
of lines containing exactly four of the points is o(n²).

Erdős conjectured the true order is Θ(n^{3/2}), based on Grünbaum's
construction achieving ≫ n^{3/2} four-point lines. However, Solymosi
and Stojaković disproved this by constructing sets with n^{2−O(1/√(log n))}
four-point lines.

The o(n²) upper bound remains open.

Status: OPEN ($100)
Reference: https://erdosproblems.com/101
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A planar point set: a finite collection of points in ℝ². -/
structure PlanarPointSet where
  points : Finset (ℝ × ℝ)
  size_pos : points.card > 0

/-- Three points are collinear if the signed area determinant vanishes. -/
def collinear (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- A point set has no five collinear if no five distinct points are collinear. -/
def NoFiveCollinear (P : PlanarPointSet) : Prop :=
  ∀ a b c d e : ℝ × ℝ,
    a ∈ P.points → b ∈ P.points → c ∈ P.points →
    d ∈ P.points → e ∈ P.points →
    a ≠ b → a ≠ c → a ≠ d → a ≠ e →
    b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
    ¬(collinear a b c ∧ collinear a b d ∧ collinear a b e)

/-- Count of lines through exactly four points of P. -/
noncomputable def fourPointLineCount (P : PlanarPointSet) : ℕ :=
  (P.points.powerset.filter (fun S =>
    S.card = 4 ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p)).card

/-! ## Main Conjecture -/

/-- **Erdős Problem #101**: the number of four-point lines is o(n²).
    For any ε > 0, eventually fourPointLineCount(P) < ε · n². -/
axiom erdos_101_conjecture :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ P : PlanarPointSet,
      NoFiveCollinear P → P.points.card ≥ N₀ →
        (fourPointLineCount P : ℝ) < ε * (P.points.card : ℝ) ^ 2

/-! ## Known Results -/

/-- **Grünbaum's Lower Bound**: there exist point sets with no five collinear
    achieving ≫ n^{3/2} four-point lines. -/
axiom grunbaum_lower_bound :
  ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, ∃ P : PlanarPointSet,
      NoFiveCollinear P ∧ P.points.card ≥ N ∧
        (fourPointLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ (3/2 : ℝ)

/-- **Solymosi–Stojaković**: configurations exist with n^{2−O(1/√(log n))}
    four-point lines, disproving Erdős's Θ(n^{3/2}) conjecture. -/
axiom solymosi_stojakovic_lower :
  ∀ C : ℝ, C > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ P : PlanarPointSet,
      NoFiveCollinear P ∧ P.points.card = n ∧
        (fourPointLineCount P : ℝ) ≥ (n : ℝ) ^ (2 - C / Real.sqrt (Real.log n))

/-- **Trivial Upper Bound**: at most C(n,2) = n(n−1)/2 lines are determined
    by n points, so the four-point line count is O(n²). -/
axiom trivial_upper_bound :
  ∀ P : PlanarPointSet,
    fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 2

/-! ## Related Observations -/

/-- **Collinear Triples**: Burr–Grünbaum–Sloane and Füredi–Palásti constructed
    sets with ~n²/6 collinear triples but no four-point lines. -/
axiom collinear_triples_no_four :
  ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, ∃ P : PlanarPointSet,
      NoFiveCollinear P ∧ P.points.card ≥ N ∧
        fourPointLineCount P = 0

/-- **Szemerédi–Trotter Bound**: the number of incidences between n points
    and m lines is O(n^{2/3} m^{2/3} + n + m). Relevant to bounding
    four-point lines via incidence geometry. -/
axiom szemeredi_trotter (n m : ℕ) :
  ∃ C : ℝ, C > 0 ∧
    ∀ P : PlanarPointSet, P.points.card = n →
      True  -- full incidence bound omitted; stated for context
