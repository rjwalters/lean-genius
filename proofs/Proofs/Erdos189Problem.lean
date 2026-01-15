/-
  Erdős Problem #189: Rectangles of Every Area in Colored ℝ²

  Source: https://erdosproblems.com/189
  Status: DISPROVED (solved with answer False)

  Statement:
  If ℝ² is finitely coloured, must there exist some colour class which
  contains the vertices of a rectangle of every area?

  **Answer**: NO - disproved by Kovač (2023)

  Kovač provided an explicit 25-color scheme such that no color class
  contains the vertices of a rectangle of area 1.

  Related results:
  - Graham (1980): TRUE for right-angled triangles
  - FALSE for rhombuses (easy to see)
  - OPEN for parallelograms

  Reference: Kovač, V., "Coloring and density theorems for configurations
  of a given volume", arXiv:2309.09973 (2023)
-/

import Mathlib

open Affine EuclideanGeometry

namespace Erdos189

/-! ## Core Definitions -/

/-- The Euclidean plane ℝ². -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A finite coloring of the plane using n colors. -/
def FiniteColoring (n : ℕ) := Plane → Fin n

/-- Four points form a rectangle if they form a quadrilateral with
    three consecutive right angles (which implies the fourth). -/
def IsRectangle (a b c d : Plane) : Prop :=
  -- a-b perpendicular to b-c and b-c perpendicular to c-d
  inner (a - b) (c - b) = 0 ∧
  inner (b - c) (d - c) = 0 ∧
  -- Form a proper quadrilateral (non-degenerate)
  a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a

/-- The area of a rectangle with vertices a, b, c, d where a-b and b-c
    are perpendicular sides. -/
noncomputable def rectangleArea (a b c d : Plane) : ℝ :=
  ‖a - b‖ * ‖b - c‖

/-- A color class contains rectangle vertices of area A if there exist
    four points of that color forming a rectangle with that area. -/
def HasRectangleOfArea (coloring : FiniteColoring n) (color : Fin n) (A : ℝ) : Prop :=
  ∃ a b c d : Plane, coloring a = color ∧ coloring b = color ∧
    coloring c = color ∧ coloring d = color ∧
    IsRectangle a b c d ∧ rectangleArea a b c d = A

/-- A color class contains rectangles of every positive area. -/
def HasRectanglesOfEveryArea (coloring : FiniteColoring n) (color : Fin n) : Prop :=
  ∀ A > 0, HasRectangleOfArea coloring color A

/-- The Erdős Problem 189 statement: For any finite coloring of ℝ²,
    some color class contains rectangles of every area. -/
def Erdos189Statement : Prop :=
  ∀ n > 0, ∀ coloring : FiniteColoring n,
    ∃ color : Fin n, HasRectanglesOfEveryArea coloring color

/-! ## Main Result -/

/--
**Erdős Problem 189 (DISPROVED)**

The statement is FALSE: There exists a finite coloring of ℝ² such that
no color class contains the vertices of a rectangle of every area.

Specifically, Kovač (2023) constructed an explicit 25-coloring where no
color class contains the vertices of any rectangle of area 1.

We axiomatize this since the construction requires:
1. Defining the specific 25-coloring (partition of ℝ² into Jordan measurable regions)
2. Proving no monochromatic rectangle of area 1 exists
-/
axiom kovac_counterexample :
  ∃ (coloring : FiniteColoring 25),
    ∀ color : Fin 25, ¬ HasRectangleOfArea coloring color 1

/-- The main theorem: Erdős Problem 189 is FALSE. -/
theorem erdos_189_is_false : ¬ Erdos189Statement := by
  intro h
  -- Get the counterexample coloring
  obtain ⟨coloring, hno⟩ := kovac_counterexample
  -- By the problem statement, some color has rectangles of every area
  have ⟨color, hcolor⟩ := h 25 (by norm_num) coloring
  -- In particular, that color has rectangles of area 1
  have h1 := hcolor 1 (by norm_num)
  -- But Kovač showed no color has rectangles of area 1
  exact hno color h1

/-! ## Related Results -/

/--
**Graham's Theorem (1980)**: For right-angled triangles, the answer is YES.

For any finite coloring of ℝ², some color class contains the vertices
of a right-angled triangle of every area.
-/
axiom graham_triangles :
  ∀ n > 0, ∀ coloring : FiniteColoring n,
    ∃ color : Fin n, ∀ A > 0, ∃ a b c : Plane,
      coloring a = color ∧ coloring b = color ∧ coloring c = color ∧
      inner (a - b) (c - b) = 0 ∧ -- right angle at b
      (1/2) * ‖a - b‖ * ‖c - b‖ = A

/--
**Squares are also false**: The statement fails even more strongly for squares.
This is "easy to see" according to Graham.
-/
axiom squares_also_false :
  ∃ (n : ℕ) (coloring : FiniteColoring n),
    ∀ color : Fin n, ∃ A > 0, ¬ ∃ a b c d : Plane,
      coloring a = color ∧ coloring b = color ∧
      coloring c = color ∧ coloring d = color ∧
      IsRectangle a b c d ∧
      ‖a - b‖ = ‖b - c‖ ∧ -- square condition
      rectangleArea a b c d = A

/--
**Parallelograms remain open**: As of January 2025, the analogous question
for parallelograms (instead of rectangles) is still unsolved.
-/
def ParallelogramQuestion : Prop :=
  ∀ n > 0, ∀ coloring : FiniteColoring n,
    ∃ color : Fin n, ∀ A > 0, ∃ a b c d : Plane,
      coloring a = color ∧ coloring b = color ∧
      coloring c = color ∧ coloring d = color ∧
      -- Parallelogram: opposite sides parallel
      (a - b) = (d - c) ∧
      -- Area A (using cross product formula)
      |det ![a - b, a - d]| = A

/-! ## Historical Notes

The problem was posed by Graham in 1980, who showed the triangle case is true.
The rectangle case remained open for over 40 years until Kovač's elegant
counterexample in 2023.

Kovač's construction is remarkably simple: a 25-coloring where each color
forms a Jordan measurable region. The key insight is that the coloring can
be designed to avoid monochromatic rectangles of any fixed area.

The parallelogram case remains one of the interesting open problems in
combinatorial geometry.

Key references:
- Graham (1980): "On partitions of Eⁿ", J. Combin. Theory Ser. A
- Kovač (2023): "Coloring and density theorems for configurations of a given volume"
-/

end Erdos189
