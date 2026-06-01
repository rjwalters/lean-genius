import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Concyclicity Determinant — Scaffold (OQ-03 / S2)

## What This File Contains

S2 SCAFFOLD for `product-of-segments-of-chords-oq-03`:

1. Coordinate-form definition `concyclicityDetCoords` of the classical $4\times 4$
   concyclicity determinant (Möbius / Berger, *Geometry I*, Theorem 10.7.6).
2. `Vec2`-level wrapper `concyclicityDet` accessing the two coordinates of each
   `EuclideanSpace ℝ (Fin 2)` point.
3. Statement of the main bidirectional criterion
   `concyclicityDet_eq_zero_iff_concyclic`, with `sorry` (closed in S3 + S4).
4. (S7 BUILD-VERIFY note) The two numerical sanity-check examples shipped in
   S2 SCAFFOLD on `Matrix.det_fin_four` have been removed — the lemma never
   existed in Mathlib v4.26.0. See the comment in Part 3 below.

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

/-! ## Part 3: Numerical sanity check (deferred to S7b ACT)

The original S2 SCAFFOLD shipped two numerical sanity checks built on
`Matrix.det_fin_four`, which does not exist in Mathlib v4.26.0 (the lemma
ladder stops at `Matrix.det_fin_three`; only the cofactor-expansion
`Matrix.det_succ_row_zero` is available for 4×4 matrices). Both example
blocks were inert documentation — no downstream consumer — and have been
removed in S7 BUILD-VERIFY to unblock the file. Reinstating them as
named numerical lemmas (e.g. via `Matrix.det_succ_row_zero` +
`Matrix.det_fin_three` expansion, or via an explicit row-dependence
`Matrix.det_eq_zero_of_row_eq` for the unit-square example) is a small
follow-up scoped for S7b.

Geometric content for reference:

- Unit-square vertices $(1,0), (0,1), (-1,0), (0,-1)$ are concyclic
  (they lie on the unit circle), so $\Delta = 0$. Rows 1+3 = rows 2+4 =
  $(2, 0, 0, 2)$, forcing a row dependency.
- Perturbing the fourth point to $(0, -2)$ moves it off the unit circle
  and gives $\Delta = -8$.
-/

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

/-! ## Part 5: Coordinate-form norm-squared helper (S15 ACT) -/

/-- For `Vec2 = EuclideanSpace ℝ (Fin 2)`, the squared norm of a difference
expands to the sum of squared coordinate differences.

This is the bridge between the abstract `‖A - P‖` notation and the explicit
coordinate-polynomial form needed by the concyclicity determinant. Used by
`signed_inner_product_to_scalar_coord` below to translate the signed
inner-product hypothesis to coordinate form. -/
lemma norm_sub_sq_coord (X Y : Vec2) :
    ‖X - Y‖ ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two]
  simp [pow_two]

/-! ## Part 6: Signed-product → scalar bridge (S15 ACT)

S9 PREP §2 established that the parent axiom is FALSE under the unsigned
hypothesis `‖P-A‖·‖P-B‖ = ‖P-C‖·‖P-D‖` (counterexample
`P=(0,0), A=(1,0), B=(-2,0), C=(0,1), D=(0,2) ⇒ Δ=12 ≠ 0`).

S9 §5 / S10 §3.3 recommend Option A: replace the hypothesis by the signed
inner-product equality `⟪A-P, B-P⟫_ℝ = ⟪C-P, D-P⟫_ℝ`, which under
chord-collinearity through P collapses to the single scalar equation
`t·‖A-P‖² = s·‖C-P‖²` (no `False.elim` case-split).

S15 ACT delivers two lemmas establishing this scalar bridge:

- `signed_inner_product_to_scalar` — abstract form.
- `signed_inner_product_to_scalar_coord` — coordinate form.

The full discharge of `concyclicityDet A B C D = 0` requires combining
these with the closed-form cofactor expansion
`Δ = (t−1)(s−1)(t‖A-P‖² − s‖C-P‖²)·(cross product)`
(S12 §3.2 / S14 §2.4) via `linear_combination`. That step is deferred to
S16 ACT, which needs only to:

1. Substitute `B i = P i + t·(A i - P i)` in the goal (S14 §4.1 substitution fix).
2. Apply `Matrix.det_succ_row_zero` + `Matrix.det_fin_three` cofactor expansion.
3. Call `linear_combination` with the closed-form witness
   `(t − 1)(s − 1)(cross_AC) * h_signed_coords`
   using `signed_inner_product_to_scalar_coord` for `h_signed_coords`. -/

/-- Under chord-collinearity through P, the signed inner-product
hypothesis collapses to a single scalar equation in the squared norms. -/
theorem signed_inner_product_to_scalar
    (P A B C D : Vec2)
    (t s : ℝ)
    (ht : B - P = t • (A - P))
    (hs : D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫ = ⟪C - P, D - P⟫) :
    t * ‖A - P‖ ^ 2 = s * ‖C - P‖ ^ 2 := by
  have h_AP : ⟪A - P, B - P⟫ = t * ‖A - P‖ ^ 2 := by
    rw [ht, inner_smul_right, real_inner_self_eq_norm_sq]
  have h_CP : ⟪C - P, D - P⟫ = s * ‖C - P‖ ^ 2 := by
    rw [hs, inner_smul_right, real_inner_self_eq_norm_sq]
  linarith [h_AP, h_CP, hSignedProduct]

/-- Coordinate form of the scalar bridge:
`t · ‖A-P‖² = s · ‖C-P‖²` translates to the polynomial identity
`t · ((A 0 - P 0)² + (A 1 - P 1)²) = s · ((C 0 - P 0)² + (C 1 - P 1)²)`. -/
theorem signed_inner_product_to_scalar_coord
    (P A B C D : Vec2)
    (t s : ℝ)
    (ht : B - P = t • (A - P))
    (hs : D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫ = ⟪C - P, D - P⟫) :
    t * ((A 0 - P 0) ^ 2 + (A 1 - P 1) ^ 2)
      = s * ((C 0 - P 0) ^ 2 + (C 1 - P 1) ^ 2) := by
  have h_scalar :=
    signed_inner_product_to_scalar P A B C D t s ht hs hSignedProduct
  rw [← norm_sub_sq_coord A P, ← norm_sub_sq_coord C P]
  exact h_scalar

end ProductOfSegmentsOfChordsOQ03
