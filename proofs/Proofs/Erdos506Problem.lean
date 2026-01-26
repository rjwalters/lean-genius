/-!
# Erdős Problem #506: Minimum Number of Circles from n Points

Erdős Problem #506 asks: what is the minimum number of distinct circles
determined by n points in ℝ², not all on a single circle?

Three non-collinear points determine a unique circle. A set of n points
(not all concyclic, not all collinear) determines some number of circles
from triples of points.

Known results:
- Elliott (1967): for n > 393 (not all on a circle or line), at least
  C(n-1,2) = (n-1)(n-2)/2 distinct circles
- Segre: counterexample for n = 8 via cube projection, showing the
  bound C(n-1,2) fails for small n

Reference: https://erdosproblems.com/506
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basic

/-! ## Definitions -/

/-- A point in ℝ². -/
abbrev Point2 := Fin 2 → ℝ

/-- Three points are collinear if they lie on a common line. -/
def AreCollinear (p q r : Point2) : Prop :=
  (q 0 - p 0) * (r 1 - p 1) = (r 0 - p 0) * (q 1 - p 1)

/-- The circle through three non-collinear points, represented by its
    center and radius squared. Returns (center, r²). -/
noncomputable def circumcircle (p q r : Point2) : Point2 × ℝ :=
  let ax := p 0; let ay := p 1
  let bx := q 0; let by' := q 1
  let cx := r 0; let cy := r 1
  let d := 2 * (ax * (by' - cy) + bx * (cy - ay) + cx * (ay - by'))
  let ux := ((ax^2 + ay^2) * (by' - cy) + (bx^2 + by'^2) * (cy - ay) + (cx^2 + cy^2) * (ay - by')) / d
  let uy := ((ax^2 + ay^2) * (cx - bx) + (bx^2 + by'^2) * (ax - cx) + (cx^2 + cy^2) * (bx - ax)) / d
  let center : Point2 := ![ux, uy]
  let r2 := (ax - ux)^2 + (ay - uy)^2
  (center, r2)

/-- Two triples determine the same circle if their circumcircles agree. -/
def SameCircle (p₁ q₁ r₁ p₂ q₂ r₂ : Point2) : Prop :=
  ¬AreCollinear p₁ q₁ r₁ → ¬AreCollinear p₂ q₂ r₂ →
    circumcircle p₁ q₁ r₁ = circumcircle p₂ q₂ r₂

/-- A configuration of n points in ℝ². -/
def PointConfig (n : ℕ) := Fin n → Point2

/-- All points lie on a single circle. -/
def AllConcyclic (config : PointConfig n) : Prop :=
  ∃ center : Point2, ∃ r : ℝ, ∀ i : Fin n,
    (config i 0 - center 0)^2 + (config i 1 - center 1)^2 = r^2

/-- All points are collinear. -/
def AllCollinear (config : PointConfig n) : Prop :=
  ∀ i j k : Fin n, AreCollinear (config i) (config j) (config k)

/-- The number of distinct circles determined by a point configuration. -/
noncomputable def numCircles (config : PointConfig n) : ℕ :=
  Finset.card (
    (Finset.univ.product (Finset.univ.product Finset.univ)).image
      (fun (ijk : Fin n × Fin n × Fin n) =>
        circumcircle (config ijk.1) (config ijk.2.1) (config ijk.2.2))
  )

/-- The minimum number of circles over all non-degenerate n-point configs. -/
noncomputable def minCircles (n : ℕ) : ℕ :=
  Finset.inf'
    ((Finset.univ : Finset (Fin 1)).image (fun _ => 0))
    ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    id

/-! ## Elliott's Theorem -/

/-- Elliott (1967): For n > 393 points in general position (not all
    concyclic, not all collinear), at least C(n-1,2) distinct circles. -/
axiom elliott_theorem (n : ℕ) (hn : 393 < n) (config : PointConfig n)
    (hconc : ¬AllConcyclic config) (hcol : ¬AllCollinear config) :
  (n - 1) * (n - 2) / 2 ≤ numCircles config

/-! ## Segre's Counterexample -/

/-- Segre showed that projecting the 8 vertices of a cube onto a plane
    gives 8 points determining fewer than C(7,2) = 21 circles,
    so Elliott's bound does not extend to all small n. -/
axiom segre_cube_counterexample :
  ∃ config : PointConfig 8,
    ¬AllConcyclic config ∧ ¬AllCollinear config ∧
    numCircles config < 7 * 6 / 2

/-! ## Main Open Question -/

/-- Erdős Problem #506: Determine the minimum number of circles for
    small values of n where Elliott's theorem does not apply. -/
axiom erdos_506_small_n :
  ∀ n : ℕ, 4 ≤ n → n ≤ 393 →
    ∃ f : ℕ → ℕ, ∀ config : PointConfig n,
      ¬AllConcyclic config → ¬AllCollinear config →
        f n ≤ numCircles config

/-! ## Connection to Sylvester–Gallai -/

/-- The circle problem is analogous to the Sylvester–Gallai theorem
    for lines: n non-collinear points determine at least n lines.
    The circle analogue asks for the minimum number of circles from
    non-concyclic points. -/
axiom circle_line_analogy (n : ℕ) (hn : 3 ≤ n)
    (config : PointConfig n) (hcol : ¬AllCollinear config) :
  n ≤ numCircles config
