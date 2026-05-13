import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Concyclicity Determinant — Scaffold (OQ-03 / S2)

## What This File Contains

S2 SCAFFOLD for `product-of-segments-of-chords-oq-03`:

1. Coordinate-form definition `concyclicityDetCoords` of the classical $4\times 4$
   concyclicity determinant (Möbius / Berger, *Geometry I*, Theorem 10.7.6).
2. `Vec2`-level wrapper `concyclicityDet` accessing the two coordinates of each
   `EuclideanSpace ℝ (Fin 2)` point.
3. Numerical sanity check on the unit-square vertices ($\Delta = 0$), provable
   by `simp [Matrix.det_fin_four]; ring` on the coordinate form.
4. Statement of the main bidirectional criterion
   `concyclicityDet_eq_zero_iff_concyclic`, with `sorry` (closed in S3 + S4).

Subsequent sessions (S3, S4, S5, S6) discharge the sorry and bridge the result
back to `Proofs/ProductOfSegmentsOfChords.lean` line 468
(`converse_product_implies_concyclic_axiom`).

See `research/problems/product-of-segments-of-chords-oq-03/state.md` for the
multi-session plan.
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace

namespace ProductOfSegmentsOfChordsOQ03

/-- 2D Euclidean point type, matching the parent file's convention
(`Proofs/ProductOfSegmentsOfChords.lean` line 55). -/
abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

/-! ## Part 1: Coordinate-form determinant -/

/-- The $4 \times 4$ concyclicity determinant in raw coordinates.

For four points $P_i = (x_i, y_i) \in \mathbb{R}^2$,
$$\Delta = \det
\begin{pmatrix}
  x_1^2 + y_1^2 & x_1 & y_1 & 1 \\
  x_2^2 + y_2^2 & x_2 & y_2 & 1 \\
  x_3^2 + y_3^2 & x_3 & y_3 & 1 \\
  x_4^2 + y_4^2 & x_4 & y_4 & 1
\end{pmatrix}.$$

Classical fact: $\Delta = 0$ iff $P_1, P_2, P_3, P_4$ are concyclic (or collinear). -/
def concyclicityDetCoords
    (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) : ℝ :=
  Matrix.det !![x₁^2 + y₁^2, x₁, y₁, 1;
                x₂^2 + y₂^2, x₂, y₂, 1;
                x₃^2 + y₃^2, x₃, y₃, 1;
                x₄^2 + y₄^2, x₄, y₄, 1]

/-! ## Part 2: `Vec2`-level wrapper -/

/-- The concyclicity determinant on `Vec2 = EuclideanSpace ℝ (Fin 2)` points,
accessing coordinates via `P 0` and `P 1`. -/
def concyclicityDet (P₁ P₂ P₃ P₄ : Vec2) : ℝ :=
  concyclicityDetCoords (P₁ 0) (P₁ 1) (P₂ 0) (P₂ 1)
    (P₃ 0) (P₃ 1) (P₄ 0) (P₄ 1)

/-! ## Part 3: Numerical sanity check -/

/-- The four unit-square vertices $(1, 0)$, $(0, 1)$, $(-1, 0)$, $(0, -1)$ are
concyclic (they lie on the unit circle), so $\Delta = 0$. Rows 1+3 equal rows
2+4 (both $(2, 0, 0, 2)$), forcing the determinant to vanish. -/
example :
    concyclicityDetCoords 1 0 0 1 (-1) 0 0 (-1) = 0 := by
  unfold concyclicityDetCoords
  simp [Matrix.det_fin_four]
  ring

/-- Moving the fourth point off the unit circle to $(0, -2)$ gives $\Delta = -8$. -/
example :
    concyclicityDetCoords 1 0 0 1 (-1) 0 0 (-2) = -8 := by
  unfold concyclicityDetCoords
  simp [Matrix.det_fin_four]
  ring

/-! ## Part 4: Main theorem (statement only) -/

/-- **Concyclicity criterion** (statement, proof deferred to S3 + S4).

Assume $P_1, P_2, P_3$ are non-collinear (placeholder hypothesis `True` until
S3 supplies the correct non-degeneracy condition). Then four points have
$\Delta = 0$ iff they lie on a common circle.

The ($\Leftarrow$) direction (S4) follows by row reduction; ($\Rightarrow$)
(S3) uses Cramer's rule on the implicit-circle equation
$x^2 + y^2 + Dx + Ey + F = 0$. -/
theorem concyclicityDet_eq_zero_iff_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (hNonCollinear : True) :
    concyclicityDet P₁ P₂ P₃ P₄ = 0 ↔
      ∃ (O : Vec2) (r : ℝ), 0 < r ∧
        ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧ ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r := by
  sorry

end ProductOfSegmentsOfChordsOQ03
