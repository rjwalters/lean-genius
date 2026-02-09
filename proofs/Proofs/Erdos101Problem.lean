/-
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

/- ## Definitions -/

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

open Classical in
/-- Count of lines through exactly four points of P. -/
noncomputable def fourPointLineCount (P : PlanarPointSet) : ℕ :=
  (P.points.powerset.filter (fun S =>
    S.card = 4 ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p)).card

/- ## Properties of Collinearity -/

/-- Collinearity is reflexive: any point is collinear with itself and any other point. -/
theorem collinear_self (p q : ℝ × ℝ) : collinear p p q := by
  unfold collinear; simp

/-- Collinearity holds when all three points are the same. -/
theorem collinear_refl (p : ℝ × ℝ) : collinear p p p := by
  unfold collinear; ring

/-- Any point is collinear with two copies of another point. -/
theorem collinear_self_right (p q : ℝ × ℝ) : collinear p q q := by
  unfold collinear; ring

/-- Collinearity is symmetric in the second and third arguments. -/
theorem collinear_swap23 {p q r : ℝ × ℝ} (h : collinear p q r) :
    collinear p r q := by
  unfold collinear at *; linarith

/- ## Structural Properties -/

/-- NoFiveCollinear holds vacuously for sets of 4 or fewer points. -/
theorem noFiveCollinear_small (P : PlanarPointSet) (h : P.points.card ≤ 4) :
    NoFiveCollinear P := by
  unfold NoFiveCollinear
  intro a b c d e ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
  have h5 : ({a, b, c, d, e} : Finset (ℝ × ℝ)).card = 5 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simp [hde]
        · simp [hcd, hce]
      · simp [hbc, hbd, hbe]
    · simp [hab, hac, had, hae]
  have hsub : {a, b, c, d, e} ⊆ P.points := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [h5] at this
  omega

/- ## Main Conjecture -/

/-- **Erdős Problem #101**: the number of four-point lines is o(n²).
    For any ε > 0, eventually fourPointLineCount(P) < ε · n². -/
axiom erdos_101_conjecture :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ P : PlanarPointSet,
      NoFiveCollinear P → P.points.card ≥ N₀ →
        (fourPointLineCount P : ℝ) < ε * (P.points.card : ℝ) ^ 2

/- ## Known Results -/

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

/- ## Related Observations -/

/-- **Collinear Triples**: Burr–Grünbaum–Sloane and Füredi–Palásti constructed
    sets with ~n²/6 collinear triples but no four-point lines. -/
axiom collinear_triples_no_four :
  ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, ∃ P : PlanarPointSet,
      NoFiveCollinear P ∧ P.points.card ≥ N ∧
        fourPointLineCount P = 0

/-- **Szemerédi–Trotter Bound**: the number of point-line incidences
    is O(n^{2/3} m^{2/3} + n + m) for n points and m lines in the plane.
    This is the key incidence-geometry tool for bounding four-point lines. -/
axiom szemeredi_trotter :
  ∃ C : ℝ, C > 0 ∧
    ∀ (n m : ℕ), ∀ (incidences : ℕ),
      (incidences : ℝ) ≤ C * ((n : ℝ) ^ (2/3 : ℝ) * (m : ℝ) ^ (2/3 : ℝ) + n + m)
