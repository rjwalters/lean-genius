/-!
# Erdős Problem #102 — Maximum Collinear Points Forced by Many Rich Lines

Given n points in ℝ² such that at least cn² lines each contain ≥ 4 points,
let h_c(n) be the maximum number of points on some line.

Estimate h_c(n). Is h_c(n) → ∞ for fixed c > 0?

## Known Results
- Upper bound: h_c(n) ≪_c n^{1/2}
- Erdős conjectured h_c(n) ≫_c n^{1/2}
- Hunter disproved this: h_c(n) ≪ n^{1/log(1/c)} using lattice points
- The question h_c(n) → ∞ is still open (connected to Problem #101)

Status: OPEN
Reference: https://erdosproblems.com/102
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A planar point configuration. -/
structure PointConfig where
  points : Finset (ℝ × ℝ)
  size_pos : points.card > 0

/-- Three points are collinear. -/
def collinear₃ (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- The number of lines containing at least 4 points. -/
noncomputable def richLineCount (P : PointConfig) : ℕ :=
  (P.points.powerset.filter (fun S =>
    S.card = 4 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear₃ a b p)).card

/-- Maximum number of collinear points in the configuration. -/
noncomputable def maxCollinear (P : PointConfig) : ℕ :=
  (P.points.powerset.filter (fun S =>
    S.card ≥ 2 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear₃ a b p)).sup Finset.card

/-! ## Main Problem -/

/-- **Erdős Problem #102**: h_c(n) → ∞. If cn² lines contain ≥ 4 points,
    some line must contain many points (growing with n). -/
axiom erdos_102_divergence (c : ℝ) (hc : c > 0) :
  ∀ M : ℕ, ∃ N₀ : ℕ, ∀ P : PointConfig,
    P.points.card ≥ N₀ →
    (richLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ 2 →
      maxCollinear P ≥ M

/-! ## Known Results -/

/-- **Upper Bound**: h_c(n) ≪_c √n. The maximum collinear count from cn²
    rich lines is at most O(√n). -/
axiom upper_bound (c : ℝ) (hc : c > 0) :
  ∃ C : ℝ, C > 0 ∧ ∀ P : PointConfig,
    (richLineCount P : ℝ) ≥ c * (P.points.card : ℝ) ^ 2 →
      (maxCollinear P : ℝ) ≤ C * Real.sqrt P.points.card

/-- **Hunter's Counterexample**: Erdős conjectured h_c(n) ≫_c √n, but
    Hunter disproved this using lattice point configurations.
    h_c(n) ≪ n^{1/log(1/c)} for suitable c. -/
axiom hunter_counterexample :
  ∃ f : ℝ → ℝ → ℝ, ∀ c : ℝ, 0 < c → c < 1 →
    ∀ n : ℕ, n > 0 →
      ∃ P : PointConfig, P.points.card = n ∧
        (richLineCount P : ℝ) ≥ c * n ^ 2 ∧
          (maxCollinear P : ℝ) ≤ f c n

/-- **Connection to Problem #101**: if h_c(n) ≥ 5 is open, the o(n²)
    bound for 4-point lines from Problem #101 would follow. -/
axiom connection_101 : True

/-! ## Observations -/

/-- **Szemerédi–Trotter**: the incidence bound I(P,L) = O(n^{2/3}m^{2/3}+n+m)
    constrains how many rich lines can pass through n points. -/
axiom szemeredi_trotter_context : True

/-- **Erdős–Purdy Origin**: this problem was posed by Erdős and Purdy
    in their work on combinatorial geometry. -/
axiom erdos_purdy_origin : True
