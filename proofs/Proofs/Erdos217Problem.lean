/-
Erdős Problem #217: Point Configurations with Triangular Distance Multiplicities

Source: https://erdosproblems.com/217
Status: OPEN

Statement:
For which n are there n points in ℝ², no three on a line and no four on a circle,
which determine n-1 distinct distances such that (in some ordering) the i-th distance
occurs exactly i times?

An isosceles triangle with its center gives n = 4. Pomerance constructed examples
for n = 5. Palásti proved such configurations exist for all n ≤ 8. Erdős believed
the property fails for sufficiently large n.

References:
- Erdős: Original problem
- Pomerance: Construction for n = 5
- Palásti: Constructions for n ≤ 8
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Erdos217

/-
## Part I: Definitions
-/

/-- A point configuration in the plane. -/
abbrev PointConfig (n : ℕ) := Fin n → ℝ × ℝ

/-- The squared distance between two points. -/
def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1)^2 + (p.2 - q.2)^2

/-- No three points are collinear. -/
def NoThreeCollinear (n : ℕ) (P : PointConfig n) : Prop :=
  ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
    ¬((P j).1 - (P i).1) * ((P k).2 - (P i).2) =
      ((P k).1 - (P i).1) * ((P j).2 - (P i).2)

/--
The distance multiplicity property: there exist n-1 distinct distances d₁ < ... < d_{n-1}
such that dᵢ occurs exactly i times among the pairwise distances.
-/
def HasTriangularMultiplicity (n : ℕ) (P : PointConfig n) : Prop :=
  ∃ dists : Fin (n - 1) → ℝ,
    (∀ i j : Fin (n - 1), i ≠ j → dists i ≠ dists j) ∧
    (∀ i : Fin (n - 1), (Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ sqDist (P p.1) (P p.2) = (dists i)^2)).card = (i : ℕ) + 1)

/-
## Part II: Known Constructions
-/

/-- For n = 4: an isosceles triangle with center works. -/
axiom example_n_eq_4 : ∃ P : PointConfig 4,
    NoThreeCollinear 4 P ∧ HasTriangularMultiplicity 4 P

/-- Pomerance's construction for n = 5. -/
axiom pomerance_n_eq_5 : ∃ P : PointConfig 5,
    NoThreeCollinear 5 P ∧ HasTriangularMultiplicity 5 P

/-- Palásti: configurations exist for all n ≤ 8. -/
/-
## Part III: Erdős's Conjecture
-/

/--
**Erdős's Conjecture (OPEN)**: For all sufficiently large n, no such
configuration exists. The property should fail eventually.
-/
/-
## Part IV: Main Result
-/

/--
**Erdős Problem #217: OPEN**

Known: configurations exist for n ≤ 8.
Conjecture: impossible for large n.
-/
theorem erdos_217 :
    (∃ P : PointConfig 4, NoThreeCollinear 4 P ∧ HasTriangularMultiplicity 4 P) ∧
    (∃ P : PointConfig 5, NoThreeCollinear 5 P ∧ HasTriangularMultiplicity 5 P) :=
  ⟨example_n_eq_4, pomerance_n_eq_5⟩

end Erdos217
