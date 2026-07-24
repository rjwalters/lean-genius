import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
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
3. The main bidirectional criterion `concyclicityDet_eq_zero_iff_concyclic`,
   **fully proven** (S18 ACT, Part 12) under the genuine non-degeneracy
   hypothesis `¬ Collinear ℝ {P₁, P₂, P₃}` — the `(hNonCollinear : True)`
   placeholder from S2 is gone. The file now has **0 sorries and 0 axioms**.
4. (S7 BUILD-VERIFY note) The two numerical sanity-check examples shipped in
   S2 SCAFFOLD on `Matrix.det_fin_four` have been removed — the lemma never
   existed in Mathlib v4.26.0. See the comment in Part 3 below.
5. (S18 ACT) Parts 9–12: the collinearity determinant and its bridge to
   `Collinear ℝ`, the explicit Cramer-rule circumcircle of three non-collinear
   points, the cofactor decomposition of Δ relative to a candidate circle, and
   the assembled iff.

The remaining programme (state.md S5/S6) bridges this result back to
`Proofs/ProductOfSegmentsOfChords.lean` line 468
(`converse_product_implies_concyclic_axiom`).

See `research/problems/product-of-segments-of-chords-oq-03/state.md` for the
multi-session plan.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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

/-! ## Part 3: Numerical sanity checks (S7b ACT)

The original S2 SCAFFOLD shipped two numerical checks built on
`Matrix.det_fin_four`, which does not exist in Mathlib v4.26.0 (the lemma
ladder stops at `Matrix.det_fin_three`; for 4×4 one cofactor step via
`Matrix.det_succ_row_zero` reduces to four 3×3 minors). They were removed
in S7 BUILD-VERIFY to unblock the file; S7b ACT (this iteration)
reinstates them as named numerical lemmas, expanding the 4×4 determinant
via `Matrix.det_succ_row_zero` + `Matrix.det_fin_three`.

Geometric content:

- Unit-circle vertices $(1,0), (0,1), (-1,0), (0,-1)$ are concyclic, so
  $\Delta = 0$ (rows 1+3 = rows 2+4 = $(2,0,0,2)$, a row dependency).
- Moving the fourth point off the circle to $(0,-2)$ gives $\Delta = -6$.
  (The S2 SCAFFOLD doc asserted $-8$; direct cofactor expansion — verified
  here by Lean — gives $-6$, so the earlier figure was a hand-computation
  slip.)
-/

/-- The four unit-circle vertices $(1,0),(0,1),(-1,0),(0,-1)$ are concyclic,
so their concyclicity determinant vanishes. -/
theorem concyclicityDetCoords_unit_circle :
    concyclicityDetCoords 1 0 0 1 (-1) 0 0 (-1) = 0 := by
  unfold concyclicityDetCoords
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero, Fin.succAbove]
  norm_num

/-- Moving the fourth vertex off the unit circle to $(0,-2)$ makes the four
points non-concyclic, witnessed by a nonzero concyclicity determinant
($\Delta = -6$). -/
theorem concyclicityDetCoords_off_circle :
    concyclicityDetCoords 1 0 0 1 (-1) 0 0 (-2) = -6 := by
  unfold concyclicityDetCoords
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero, Fin.succAbove]
  norm_num

/-! ## Part 4: Main theorem (moved)

The headline criterion `concyclicityDet_eq_zero_iff_concyclic` is stated and
**proven** in Part 12 at the end of this file (S18 ACT) — its proof consumes
the helper lemmas of Parts 5–11, so the declaration must come after them.
Relative to the S2 stub that used to live here, the placeholder hypothesis
`(hNonCollinear : True)` has been replaced by the genuine non-degeneracy
condition `¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)`; with the placeholder the
($\Rightarrow$) direction is *false* (four distinct collinear points have
$\Delta = 0$ but lie on no common circle). -/

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

/-! ## Part 7: Chord-collinearity coordinate substitution (S16 ACT)

The signed-product bridge above (`signed_inner_product_to_scalar_coord`)
takes the chord-collinearity hypotheses `B - P = t • (A - P)` and
`D - P = s • (C - P)` as abstract `Vec2` equations. The final
cofactor-expansion + `linear_combination` discharge (S17 ACT) needs the
same hypotheses re-expressed coordinate-wise:

  `B 0 = P 0 + t * (A 0 - P 0)`, `B 1 = P 1 + t * (A 1 - P 1)`,
  `D 0 = P 0 + s * (C 0 - P 0)`, `D 1 = P 1 + s * (C 1 - P 1)`.

These are mechanical (`PiLp.sub_apply` + `PiLp.smul_apply` at indices
`0` and `1`) but packaging them as a single lemma keeps the S17 ACT
discharge focused on the polynomial witness step. The lemma is stated
generically (any two indices, any names) so it applies to all four
substitutions in S17 ACT.
-/

/-- Coordinate form of chord-collinearity:
`R - P = t • (Q - P)` evaluated at index `i` gives `R i = P i + t * (Q i - P i)`.

Used by S17 ACT to substitute `B i` and `D i` in the concyclicity determinant
before cofactor expansion. -/
lemma coord_of_smul_diff
    (P Q R : Vec2) (t : ℝ) (h : R - P = t • (Q - P)) (i : Fin 2) :
    R i = P i + t * (Q i - P i) := by
  have hi : (R - P) i = (t • (Q - P)) i := by rw [h]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hi
  linarith

/-! ## Part 8: Easy direction of the concyclicity criterion (`⟸`) -/

/-- **Concyclic ⟹ determinant vanishes** (the `⟸` direction of
`concyclicityDet_eq_zero_iff_concyclic`, proved unconditionally — no
non-degeneracy hypothesis is needed for this direction).

If `P₁, P₂, P₃, P₄` lie on a common circle with center `O` and radius `r`,
the concyclicity determinant is zero. Reason: writing each point's circle
equation `(xᵢ−O₀)² + (yᵢ−O₁)² = r²` expands to
`xᵢ² + yᵢ² = 2O₀·xᵢ + 2O₁·yᵢ + (r²−O₀²−O₁²)`, so the first column of the
matrix is the linear combination `2O₀·(x col) + 2O₁·(y col) + (r²−O₀²−O₁²)·(1 col)`
of the other three. The columns are therefore dependent — equivalently the
nonzero vector `w = (1, −2O₀, −2O₁, O₀²+O₁²−r²)` lies in the kernel — so the
determinant vanishes (`Matrix.exists_mulVec_eq_zero_iff`). -/
theorem concyclic_implies_concyclicityDet_zero
    (P₁ P₂ P₃ P₄ O : Vec2) (r : ℝ)
    (h₁ : ‖P₁ - O‖ = r) (h₂ : ‖P₂ - O‖ = r)
    (h₃ : ‖P₃ - O‖ = r) (h₄ : ‖P₄ - O‖ = r) :
    concyclicityDet P₁ P₂ P₃ P₄ = 0 := by
  have e : ∀ Q : Vec2, ‖Q - O‖ = r →
      (Q 0 - O 0) ^ 2 + (Q 1 - O 1) ^ 2 = r ^ 2 := by
    intro Q hQ
    have h := norm_sub_sq_coord Q O
    rw [hQ] at h; linarith
  unfold concyclicityDet concyclicityDetCoords
  refine Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨![1, -(2 * O 0), -(2 * O 1), O 0 ^ 2 + O 1 ^ 2 - r ^ 2], ?_, ?_⟩
  · intro hw
    have h0 := congrFun hw 0
    simp at h0
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      nlinarith [e P₁ h₁, e P₂ h₂, e P₃ h₃, e P₄ h₄]

/-! ## Part 9: The collinearity determinant and non-collinearity (S18 ACT)

The genuine non-degeneracy hypothesis for the concyclicity criterion is that
`P₁, P₂, P₃` are not collinear. Algebraically this is the non-vanishing of the
$2\times 2$ determinant $d = (x_2-x_1)(y_3-y_1) - (x_3-x_1)(y_2-y_1)$ (twice
the signed triangle area, and also the bottom cofactor $M_4$ of the
concyclicity matrix). This part defines `collinearityDet` and proves the
direction of the bridge needed downstream: vanishing determinant ⟹
`Collinear ℝ`, hence ¬collinear ⟹ nonzero determinant. -/

/-- The planar collinearity determinant of three points in raw coordinates:
$(x_2-x_1)(y_3-y_1) - (x_3-x_1)(y_2-y_1)$, i.e. twice the signed area of the
triangle `P₁P₂P₃`. The three points are collinear iff it vanishes. -/
def collinearityDetCoords (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) : ℝ :=
  (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)

/-- `Vec2`-level wrapper for `collinearityDetCoords`. -/
def collinearityDet (P₁ P₂ P₃ : Vec2) : ℝ :=
  collinearityDetCoords (P₁ 0) (P₁ 1) (P₂ 0) (P₂ 1) (P₃ 0) (P₃ 1)

/-- If the collinearity determinant of three planar points vanishes, the
points are collinear in the affine sense. Case split: if `P₂ = P₁` the
direction `P₃ - P₁` works; otherwise `P₂ - P₁` is a nonzero direction and the
vanishing determinant supplies the scalar for `P₃` (parametrising by whichever
coordinate of `P₂ - P₁` is nonzero). -/
theorem collinear_of_collinearityDet_eq_zero
    (P₁ P₂ P₃ : Vec2) (h : collinearityDet P₁ P₂ P₃ = 0) :
    Collinear ℝ ({P₁, P₂, P₃} : Set Vec2) := by
  have h' : (P₂ 0 - P₁ 0) * (P₃ 1 - P₁ 1) - (P₃ 0 - P₁ 0) * (P₂ 1 - P₁ 1) = 0 := h
  rw [collinear_iff_of_mem (Set.mem_insert P₁ {P₂, P₃})]
  by_cases hx : P₂ 0 - P₁ 0 = 0
  · by_cases hy : P₂ 1 - P₁ 1 = 0
    · -- both coordinates agree: `P₂ = P₁`, direction `P₃ - P₁`
      have h21 : P₂ = P₁ := by
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        exact ⟨sub_eq_zero.mp hx, sub_eq_zero.mp hy⟩
      refine ⟨P₃ - P₁, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp [h21]⟩
      · exact ⟨1, by simp [vadd_eq_add]⟩
    · -- `P₂ 1 ≠ P₁ 1`: parametrise `P₃` by its `y`-coordinate
      refine ⟨P₂ - P₁, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | hpe
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp [vadd_eq_add]⟩
      · rw [hpe]
        refine ⟨(P₃ 1 - P₁ 1) / (P₂ 1 - P₁ 1), ?_⟩
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · -- the `x`-coordinate needs the vanishing determinant
          simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
            smul_eq_mul]
          field_simp [hy]
          linear_combination -h'
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
            smul_eq_mul]
          field_simp [hy]
          try ring
  · -- `P₂ 0 ≠ P₁ 0`: parametrise `P₃` by its `x`-coordinate
    refine ⟨P₂ - P₁, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | hpe
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [vadd_eq_add]⟩
    · rw [hpe]
      refine ⟨(P₃ 0 - P₁ 0) / (P₂ 0 - P₁ 0), ?_⟩
      apply PiLp.ext
      rw [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩
      · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          smul_eq_mul]
        field_simp [hx]
        try ring
      · -- the `y`-coordinate needs the vanishing determinant
        simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          smul_eq_mul]
        field_simp [hx]
        linear_combination h'

/-- Contrapositive form used by the main theorem: non-collinear triples have
nonzero collinearity determinant. -/
theorem collinearityDet_ne_zero_of_not_collinear
    (P₁ P₂ P₃ : Vec2)
    (h : ¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)) :
    collinearityDet P₁ P₂ P₃ ≠ 0 :=
  fun h0 => h (collinear_of_collinearityDet_eq_zero P₁ P₂ P₃ h0)

/-! ## Part 10: The circumcircle of a non-collinear triple (S18 ACT)

Cramer's rule on the two perpendicular-bisector equations

  `2(x₂-x₁)·O₀ + 2(y₂-y₁)·O₁ = (x₂²+y₂²) - (x₁²+y₁²)`
  `2(x₃-x₁)·O₀ + 2(y₃-y₁)·O₁ = (x₃²+y₃²) - (x₁²+y₁²)`

whose coefficient determinant is `4·collinearityDet ≠ 0`, gives the explicit
circumcenter; the common radius `r = ‖P₁ - O‖` is positive because `r = 0`
would force `P₂ = P₁` and hence a vanishing collinearity determinant. -/

/-- A point `(O₀, O₁)` on the perpendicular bisector of `(x₁,y₁)`-`(x₂,y₂)`
(in equation form) is equidistant from the two points, in squared form. Pure
ring identity — the `O₀²`, `O₁²` terms cancel, so this stays linear in the
center coordinates and never needs a denominator cleared. -/
private lemma bisector_to_dist
    (x₁ y₁ x₂ y₂ O₀ O₁ : ℝ)
    (hb : 2 * (x₂ - x₁) * O₀ + 2 * (y₂ - y₁) * O₁
        = x₂ ^ 2 + y₂ ^ 2 - x₁ ^ 2 - y₁ ^ 2) :
    (x₂ - O₀) ^ 2 + (y₂ - O₁) ^ 2 = (x₁ - O₀) ^ 2 + (y₁ - O₁) ^ 2 := by
  linear_combination -hb

/-- Core Cramer computation, pure coordinates: the explicit circumcenter
equalises the three squared distances. Denominators are cleared by a
deterministic `mul_div_assoc`/`div_add_div_same`/`div_eq_iff` chain (the
quotients only ever appear linearly here, thanks to `bisector_to_dist`). -/
private lemma circumcenter_spec
    (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ)
    (hd : (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁) ≠ 0) :
    ∃ O₀ O₁ : ℝ,
      (x₂ - O₀) ^ 2 + (y₂ - O₁) ^ 2 = (x₁ - O₀) ^ 2 + (y₁ - O₁) ^ 2 ∧
      (x₃ - O₀) ^ 2 + (y₃ - O₁) ^ 2 = (x₁ - O₀) ^ 2 + (y₁ - O₁) ^ 2 := by
  have h2d : 2 * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)) ≠ 0 :=
    mul_ne_zero two_ne_zero hd
  refine ⟨((x₂ ^ 2 + y₂ ^ 2 - x₁ ^ 2 - y₁ ^ 2) * (y₃ - y₁)
          - (x₃ ^ 2 + y₃ ^ 2 - x₁ ^ 2 - y₁ ^ 2) * (y₂ - y₁))
          / (2 * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁))),
         ((x₃ ^ 2 + y₃ ^ 2 - x₁ ^ 2 - y₁ ^ 2) * (x₂ - x₁)
          - (x₂ ^ 2 + y₂ ^ 2 - x₁ ^ 2 - y₁ ^ 2) * (x₃ - x₁))
          / (2 * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁))),
         bisector_to_dist _ _ _ _ _ _ ?_, bisector_to_dist _ _ _ _ _ _ ?_⟩
  · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff h2d]
    ring
  · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff h2d]
    ring

/-- Every non-collinear triple in the plane lies on a genuine circle
(positive radius). -/
theorem exists_circumcircle
    (P₁ P₂ P₃ : Vec2) (hd : collinearityDet P₁ P₂ P₃ ≠ 0) :
    ∃ (O : Vec2) (r : ℝ), 0 < r ∧
      ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧ ‖P₃ - O‖ = r := by
  have hdc : (P₂ 0 - P₁ 0) * (P₃ 1 - P₁ 1) - (P₃ 0 - P₁ 0) * (P₂ 1 - P₁ 1) ≠ 0 := hd
  obtain ⟨O₀, O₁, h2, h3⟩ :=
    circumcenter_spec (P₁ 0) (P₁ 1) (P₂ 0) (P₂ 1) (P₃ 0) (P₃ 1) hdc
  set O : Vec2 := WithLp.toLp 2 ![O₀, O₁] with hO
  have hO0 : O 0 = O₀ := rfl
  have hO1 : O 1 = O₁ := rfl
  have hsq2 : ‖P₂ - O‖ ^ 2 = ‖P₁ - O‖ ^ 2 := by
    rw [norm_sub_sq_coord, norm_sub_sq_coord, hO0, hO1]
    exact h2
  have hsq3 : ‖P₃ - O‖ ^ 2 = ‖P₁ - O‖ ^ 2 := by
    rw [norm_sub_sq_coord, norm_sub_sq_coord, hO0, hO1]
    exact h3
  have h₂ : ‖P₂ - O‖ = ‖P₁ - O‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq2
  have h₃ : ‖P₃ - O‖ = ‖P₁ - O‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq3
  refine ⟨O, ‖P₁ - O‖, ?_, rfl, h₂, h₃⟩
  rcases (norm_nonneg (P₁ - O)).lt_or_eq with hlt | heq
  · exact hlt
  · -- radius `0` would force `P₂ = P₁`, contradicting `hd`
    exfalso
    have e₁ : P₁ = O := sub_eq_zero.mp (norm_eq_zero.mp heq.symm)
    have e₂ : P₂ = O := by
      have h0 : ‖P₂ - O‖ = 0 := by rw [h₂, ← heq]
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    have h21 : P₂ = P₁ := e₂.trans e₁.symm
    apply hdc
    have c0 : P₂ 0 = P₁ 0 := by rw [h21]
    have c1 : P₂ 1 = P₁ 1 := by rw [h21]
    rw [c0, c1]
    ring

/-! ## Part 11: Cofactor decomposition and the forced fourth point (S18 ACT)

Column multilinearity gives the *exact polynomial identity*

  `Δ = e₁·M₁ - e₂·M₂ + e₃·M₃ - e₄·M₄`,

where `eᵢ = (xᵢ-O₀)² + (yᵢ-O₁)² - r²` is the circle defect of `Pᵢ` and `Mᵢ`
is the 3×3 minor of the `(x, y, 1)` columns omitting row `i` (in particular
`M₄ = collinearityDet P₁ P₂ P₃`): substituting
`xᵢ²+yᵢ² = eᵢ + 2O₀xᵢ + 2O₁yᵢ + (r²-O₀²-O₁²)` in the first column, the three
non-`e` summands each produce a repeated column, so only `det(e-col, x, y, 1)`
survives. With `P₁, P₂, P₃` on the circle (`e₁ = e₂ = e₃ = 0`) and `Δ = 0`,
the identity collapses to `e₄ · M₄ = 0`, and `M₄ ≠ 0` forces `e₄ = 0`. -/

/-- Exact cofactor decomposition of the concyclicity determinant relative to
an arbitrary candidate circle (center `(O₀, O₁)`, radius `r`). This is a pure
polynomial identity — no hypotheses. -/
lemma concyclicityDetCoords_circle_decomp
    (O₀ O₁ r x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) :
    concyclicityDetCoords x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ =
      ((x₁ - O₀) ^ 2 + (y₁ - O₁) ^ 2 - r ^ 2)
          * (x₂ * (y₃ - y₄) - x₃ * (y₂ - y₄) + x₄ * (y₂ - y₃))
        - ((x₂ - O₀) ^ 2 + (y₂ - O₁) ^ 2 - r ^ 2)
          * (x₁ * (y₃ - y₄) - x₃ * (y₁ - y₄) + x₄ * (y₁ - y₃))
        + ((x₃ - O₀) ^ 2 + (y₃ - O₁) ^ 2 - r ^ 2)
          * (x₁ * (y₂ - y₄) - x₂ * (y₁ - y₄) + x₄ * (y₁ - y₂))
        - ((x₄ - O₀) ^ 2 + (y₄ - O₁) ^ 2 - r ^ 2)
          * (x₁ * (y₂ - y₃) - x₂ * (y₁ - y₃) + x₃ * (y₁ - y₂)) := by
  unfold concyclicityDetCoords
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero,
    Fin.succAbove]
  ring

/-- If `P₁, P₂, P₃` lie on the circle of center `O` and radius `r`, are not
collinear, and the concyclicity determinant of `P₁, P₂, P₃, P₄` vanishes,
then `P₄` lies on the same circle. -/
theorem fourth_point_on_circle
    (P₁ P₂ P₃ P₄ O : Vec2) (r : ℝ) (hr : 0 ≤ r)
    (hd : collinearityDet P₁ P₂ P₃ ≠ 0)
    (h₁ : ‖P₁ - O‖ = r) (h₂ : ‖P₂ - O‖ = r) (h₃ : ‖P₃ - O‖ = r)
    (hΔ : concyclicityDet P₁ P₂ P₃ P₄ = 0) :
    ‖P₄ - O‖ = r := by
  have e₁ : (P₁ 0 - O 0) ^ 2 + (P₁ 1 - O 1) ^ 2 = r ^ 2 := by
    have h := norm_sub_sq_coord P₁ O
    rw [h₁] at h
    linarith
  have e₂ : (P₂ 0 - O 0) ^ 2 + (P₂ 1 - O 1) ^ 2 = r ^ 2 := by
    have h := norm_sub_sq_coord P₂ O
    rw [h₂] at h
    linarith
  have e₃ : (P₃ 0 - O 0) ^ 2 + (P₃ 1 - O 1) ^ 2 = r ^ 2 := by
    have h := norm_sub_sq_coord P₃ O
    rw [h₃] at h
    linarith
  have hdc : (P₂ 0 - P₁ 0) * (P₃ 1 - P₁ 1) - (P₃ 0 - P₁ 0) * (P₂ 1 - P₁ 1) ≠ 0 := hd
  have hΔ' : concyclicityDetCoords (P₁ 0) (P₁ 1) (P₂ 0) (P₂ 1) (P₃ 0) (P₃ 1)
      (P₄ 0) (P₄ 1) = 0 := hΔ
  rw [concyclicityDetCoords_circle_decomp (O 0) (O 1) r] at hΔ'
  have key : ((P₄ 0 - O 0) ^ 2 + (P₄ 1 - O 1) ^ 2 - r ^ 2)
      * ((P₂ 0 - P₁ 0) * (P₃ 1 - P₁ 1) - (P₃ 0 - P₁ 0) * (P₂ 1 - P₁ 1)) = 0 := by
    linear_combination (-1 : ℝ) * hΔ'
      + (P₂ 0 * (P₃ 1 - P₄ 1) - P₃ 0 * (P₂ 1 - P₄ 1) + P₄ 0 * (P₂ 1 - P₃ 1)) * e₁
      - (P₁ 0 * (P₃ 1 - P₄ 1) - P₃ 0 * (P₁ 1 - P₄ 1) + P₄ 0 * (P₁ 1 - P₃ 1)) * e₂
      + (P₁ 0 * (P₂ 1 - P₄ 1) - P₂ 0 * (P₁ 1 - P₄ 1) + P₄ 0 * (P₁ 1 - P₂ 1)) * e₃
  have h4 : (P₄ 0 - O 0) ^ 2 + (P₄ 1 - O 1) ^ 2 = r ^ 2 := by
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · exact absurd h hdc
  have hsq : ‖P₄ - O‖ ^ 2 = r ^ 2 := by
    rw [norm_sub_sq_coord]
    exact h4
  exact (pow_left_inj₀ (norm_nonneg _) hr (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

/-! ## Part 12: Main theorem (S18 ACT) -/

/-- **Concyclicity criterion.** For `P₁, P₂, P₃` non-collinear, the four
points `P₁, P₂, P₃, P₄` have vanishing concyclicity determinant iff they lie
on a common circle of positive radius.

(⟹): the circumcircle of `P₁P₂P₃` exists by `exists_circumcircle`, and the
cofactor decomposition forces `P₄` onto it (`fourth_point_on_circle`).
(⟸): `concyclic_implies_concyclicityDet_zero`, which needs no non-degeneracy
hypothesis at all. -/
theorem concyclicityDet_eq_zero_iff_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (hNonCollinear : ¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)) :
    concyclicityDet P₁ P₂ P₃ P₄ = 0 ↔
      ∃ (O : Vec2) (r : ℝ), 0 < r ∧
        ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧ ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r := by
  have hd : collinearityDet P₁ P₂ P₃ ≠ 0 :=
    collinearityDet_ne_zero_of_not_collinear P₁ P₂ P₃ hNonCollinear
  constructor
  · intro hΔ
    obtain ⟨O, r, hr, h₁, h₂, h₃⟩ := exists_circumcircle P₁ P₂ P₃ hd
    exact ⟨O, r, hr, h₁, h₂, h₃,
      fourth_point_on_circle P₁ P₂ P₃ P₄ O r hr.le hd h₁ h₂ h₃ hΔ⟩
  · rintro ⟨O, r, _, h₁, h₂, h₃, h₄⟩
    exact concyclic_implies_concyclicityDet_zero P₁ P₂ P₃ P₄ O r h₁ h₂ h₃ h₄

end ProductOfSegmentsOfChordsOQ03
