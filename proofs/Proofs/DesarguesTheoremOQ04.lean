/-
# Self-Duality of Desargues's Theorem (OQ-04)

## What This Proves

Desargues's theorem is self-dual in projective geometry: the dual statement
(swapping "point" and "line") is again Desargues's theorem. This means the
converse is NOT an independent result — it is the dual of the forward direction.

## The Duality Principle

In the projective plane over a field K, points and lines are both represented
as elements of K³ (homogeneous coordinates). The key symmetries:

1. Incidence is symmetric: point p lies on line l ⟺ p · l = 0 ⟺ l · p = 0
2. Join = Meet: the cross product gives both
3. Collinear ⟺ Concurrent: both are det(u,v,w) = 0

## Formalization Strategy

1. Prove collinear = concurrent (definitional)
2. Define the dual configuration (swap sides and vertices)
3. Prove dual(perspectiveFromPoint) = perspectiveFromLine (definitional)
4. The Desargues identity is symmetric in (A,B,C) ↔ (A',B',C')
5. Derive the "dual forward direction" and the algebraic converse
6. Prove the intersection points are symmetric: P(A,B;A',B') = P(A',B';A,B)

Tags: projective-geometry, duality, self-dual, desargues
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace DesarguesTheoremOQ04

open Matrix

variable {K : Type*} [CommRing K]

-- ============================================================
-- PART 1: Cross Product and Determinant Setup
-- ============================================================

/-- Cross product of two vectors in K³. -/
def cross3 (a b : Fin 3 → K) : Fin 3 → K :=
  fun i => match i with
    | 0 => a 1 * b 2 - a 2 * b 1
    | 1 => a 2 * b 0 - a 0 * b 2
    | 2 => a 0 * b 1 - a 1 * b 0

theorem cross3_zero (a b : Fin 3 → K) : cross3 a b 0 = a 1 * b 2 - a 2 * b 1 := rfl
theorem cross3_one  (a b : Fin 3 → K) : cross3 a b 1 = a 2 * b 0 - a 0 * b 2 := rfl
theorem cross3_two  (a b : Fin 3 → K) : cross3 a b 2 = a 0 * b 1 - a 1 * b 0 := rfl

/-- Cross product is anticommutative. -/
theorem cross3_anticomm (a b : Fin 3 → K) : cross3 a b = -cross3 b a := by
  ext i; fin_cases i <;> simp [cross3] <;> ring

/-- Three-row matrix from three vectors. -/
def threeVecMat (u v w : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j =>
    match i with
    | 0 => u j
    | 1 => v j
    | 2 => w j

theorem threeVecMat_det_explicit (u v w : Fin 3 → K) :
    (threeVecMat u v w).det =
      u 0 * (v 1 * w 2 - v 2 * w 1) -
      u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0) := by
  simp only [threeVecMat, Matrix.det_fin_three, Matrix.of_apply]
  ring

-- ============================================================
-- PART 2: Collinearity and Concurrence Are Identical
-- ============================================================

/-- Three points are collinear iff det(p,q,r) = 0. -/
def collinear (p q r : Fin 3 → K) : Prop :=
  (threeVecMat p q r).det = 0

/-- Three lines are concurrent iff det(l,m,n) = 0. -/
def concurrent (l m n : Fin 3 → K) : Prop :=
  (threeVecMat l m n).det = 0

/-- **Fundamental duality**: collinear and concurrent are the SAME predicate
    (both are det = 0 on K³ vectors). This is the foundation of projective
    duality in homogeneous coordinates. -/
theorem collinear_eq_concurrent :
    @collinear K _ = @concurrent K _ := rfl

-- ============================================================
-- PART 3: Projective Configuration
-- ============================================================

/-- Two triangles in the projective plane over K. -/
structure DesarguesConfig (K : Type*) [CommRing K] where
  A : Fin 3 → K
  B : Fin 3 → K
  C : Fin 3 → K
  A' : Fin 3 → K
  B' : Fin 3 → K
  C' : Fin 3 → K

/-- Perspective from a point: lines AA', BB', CC' are concurrent. -/
def DesarguesConfig.perspFromPoint (cfg : DesarguesConfig K) : Prop :=
  concurrent (cross3 cfg.A cfg.A') (cross3 cfg.B cfg.B') (cross3 cfg.C cfg.C')

/-- Perspective from a line: intersection points P = AB∩A'B', Q = BC∩B'C',
    R = CA∩C'A' are collinear. -/
def DesarguesConfig.perspFromLine (cfg : DesarguesConfig K) : Prop :=
  collinear
    (cross3 (cross3 cfg.A cfg.B) (cross3 cfg.A' cfg.B'))
    (cross3 (cross3 cfg.B cfg.C) (cross3 cfg.B' cfg.C'))
    (cross3 (cross3 cfg.C cfg.A) (cross3 cfg.C' cfg.A'))

/-- The swapped configuration: interchange the two triangles. -/
def DesarguesConfig.swap (cfg : DesarguesConfig K) : DesarguesConfig K where
  A := cfg.A'
  B := cfg.B'
  C := cfg.C'
  A' := cfg.A
  B' := cfg.B
  C' := cfg.C

-- ============================================================
-- PART 4: The Dual Configuration
-- ============================================================

/-- The dual configuration: vertices become sides and sides become vertices.
    The dual's vertices are the sides of the original triangles. -/
def DesarguesConfig.dual (cfg : DesarguesConfig K) : DesarguesConfig K where
  A  := cross3 cfg.A cfg.B    -- side AB
  B  := cross3 cfg.B cfg.C    -- side BC
  C  := cross3 cfg.C cfg.A    -- side CA
  A' := cross3 cfg.A' cfg.B'  -- side A'B'
  B' := cross3 cfg.B' cfg.C'  -- side B'C'
  C' := cross3 cfg.C' cfg.A'  -- side C'A'

/-- **Key duality theorem**: "Perspective from a point" of the dual
    configuration IS "perspective from a line" of the original.
    This is definitional — the joining lines of the dual's vertices
    are the intersection points of the original's sides. -/
theorem dual_perspFromPoint_eq_perspFromLine (cfg : DesarguesConfig K) :
    cfg.dual.perspFromPoint = cfg.perspFromLine := rfl

-- ============================================================
-- PART 5: The Desargues Identity
-- ============================================================

set_option maxHeartbeats 400000000 in
/-- Lagrange cross product identity. -/
theorem lagrange_cross (a b c d : Fin 3 → K) :
    cross3 (cross3 a b) (cross3 c d) =
    fun i => (threeVecMat a b d).det * c i - (threeVecMat a b c).det * d i := by
  have h0 : cross3 (cross3 a b) (cross3 c d) 0 =
      (threeVecMat a b d).det * c 0 - (threeVecMat a b c).det * d 0 := by
    simp only [cross3_zero, cross3_one, cross3_two, threeVecMat_det_explicit]; ring
  have h1 : cross3 (cross3 a b) (cross3 c d) 1 =
      (threeVecMat a b d).det * c 1 - (threeVecMat a b c).det * d 1 := by
    simp only [cross3_zero, cross3_one, cross3_two, threeVecMat_det_explicit]; ring
  have h2 : cross3 (cross3 a b) (cross3 c d) 2 =
      (threeVecMat a b d).det * c 2 - (threeVecMat a b c).det * d 2 := by
    simp only [cross3_zero, cross3_one, cross3_two, threeVecMat_det_explicit]; ring
  funext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

set_option maxHeartbeats 800000000 in
/-- **The Desargues Identity**: det(P,Q,R) = det(AA',BB',CC') · det(ABC) · det(A'B'C')
    where P, Q, R are the intersection points of corresponding sides. -/
theorem desargues_identity (A B C A' B' C' : Fin 3 → K) :
    (threeVecMat
        (cross3 (cross3 A B) (cross3 A' B'))
        (cross3 (cross3 B C) (cross3 B' C'))
        (cross3 (cross3 C A) (cross3 C' A'))).det =
      (threeVecMat (cross3 A A') (cross3 B B') (cross3 C C')).det *
      ((threeVecMat A B C).det * (threeVecMat A' B' C').det) := by
  set d1 := (threeVecMat A B B').det with hd1
  set d2 := (threeVecMat A B A').det with hd2
  set d3 := (threeVecMat B C C').det with hd3
  set d4 := (threeVecMat B C B').det with hd4
  set d5 := (threeVecMat C A A').det with hd5
  set d6 := (threeVecMat C A C').det with hd6
  have hP : cross3 (cross3 A B) (cross3 A' B') = fun i => d1 * A' i - d2 * B' i :=
    lagrange_cross A B A' B'
  have hQ : cross3 (cross3 B C) (cross3 B' C') = fun i => d3 * B' i - d4 * C' i :=
    lagrange_cross B C B' C'
  have hR : cross3 (cross3 C A) (cross3 C' A') = fun i => d5 * C' i - d6 * A' i :=
    lagrange_cross C A C' A'
  have hLHS : (threeVecMat
        (fun i => d1 * A' i - d2 * B' i)
        (fun i => d3 * B' i - d4 * C' i)
        (fun i => d5 * C' i - d6 * A' i)).det =
      (d1 * d3 * d5 - d2 * d4 * d6) * (threeVecMat A' B' C').det := by
    simp only [threeVecMat_det_explicit]; ring
  have hCore : d1 * d3 * d5 - d2 * d4 * d6 =
      (threeVecMat (cross3 A A') (cross3 B B') (cross3 C C')).det *
      (threeVecMat A B C).det := by
    simp only [hd1, hd2, hd3, hd4, hd5, hd6,
               threeVecMat_det_explicit, cross3_zero, cross3_one, cross3_two]; ring
  rw [hP, hQ, hR, hLHS, hCore]; ring

-- ============================================================
-- PART 6: The Forward Direction
-- ============================================================

/-- **Desargues's theorem (forward)**: perspective from a point implies
    perspective from a line, over any CommRing K. -/
theorem desargues_forward (cfg : DesarguesConfig K)
    (h : cfg.perspFromPoint) :
    cfg.perspFromLine := by
  unfold DesarguesConfig.perspFromLine collinear
  unfold DesarguesConfig.perspFromPoint concurrent at h
  rw [desargues_identity, h, zero_mul]

-- ============================================================
-- PART 7: Self-Duality via the Dual Configuration
-- ============================================================

/-- **Self-duality (forward)**: applying the forward direction to the dual
    configuration gives: perspFromPoint(dual) → perspFromLine(dual).
    But perspFromPoint(dual) = perspFromLine(original) by duality.
    So this says: if the original is in perspective from a line,
    then the dual is in perspective from a line. -/
theorem desargues_dual_forward (cfg : DesarguesConfig K)
    (h : cfg.perspFromLine) :
    cfg.dual.perspFromLine := by
  -- perspFromLine(cfg) = perspFromPoint(dual(cfg))  [definitional]
  have h' : cfg.dual.perspFromPoint := h
  exact desargues_forward cfg.dual h'

-- ============================================================
-- PART 8: Symmetry of the Desargues Identity
-- ============================================================

/-- The intersection point P = AB ∩ A'B' is the same regardless of
    which triangle is "first" — the cross product is anticommutative,
    so cross3(AB, A'B') and cross3(A'B', AB) differ by sign, which
    doesn't matter for collinearity (det scales by (-1)³ = -1). -/
theorem intersection_swap_sign (A B A' B' : Fin 3 → K) :
    cross3 (cross3 A' B') (cross3 A B) = -cross3 (cross3 A B) (cross3 A' B') :=
  cross3_anticomm (cross3 A' B') (cross3 A B)

/-- **Symmetry of the Desargues identity**: the identity holds with
    (A,B,C) and (A',B',C') swapped. This is the algebraic content
    of self-duality. -/
theorem desargues_identity_swap (A B C A' B' C' : Fin 3 → K) :
    (threeVecMat
        (cross3 (cross3 A' B') (cross3 A B))
        (cross3 (cross3 B' C') (cross3 B C))
        (cross3 (cross3 C' A') (cross3 C A))).det =
      (threeVecMat (cross3 A' A) (cross3 B' B) (cross3 C' C)).det *
      ((threeVecMat A' B' C').det * (threeVecMat A B C).det) :=
  desargues_identity A' B' C' A B C

/-- The perspectivity determinant det(AA',BB',CC') is the SAME (up to sign)
    when the triangles are swapped. cross3 A A' = -cross3 A' A, so each row
    flips sign, and det picks up (-1)³ = -1 overall. -/
theorem perspectivity_det_swap (A B C A' B' C' : Fin 3 → K) :
    (threeVecMat (cross3 A' A) (cross3 B' B) (cross3 C' C)).det =
    -(threeVecMat (cross3 A A') (cross3 B B') (cross3 C C')).det := by
  simp only [threeVecMat_det_explicit, cross3_zero, cross3_one, cross3_two]; ring

/-- **Self-duality of perspectivity**: if lines AA', BB', CC' are concurrent,
    so are lines A'A, B'B, C'C (same lines, same intersection). -/
theorem perspFromPoint_swap (cfg : DesarguesConfig K)
    (h : cfg.perspFromPoint) :
    cfg.swap.perspFromPoint := by
  unfold DesarguesConfig.perspFromPoint concurrent at h ⊢
  unfold DesarguesConfig.swap
  rw [perspectivity_det_swap, neg_eq_zero]
  exact h

-- ============================================================
-- PART 9: Self-Duality of Perspective from a Line
-- ============================================================

/-- The collinearity determinant for swapped intersection points
    picks up a factor of (-1)³ = -1. -/
theorem collinearity_det_swap (A B C A' B' C' : Fin 3 → K) :
    (threeVecMat
        (cross3 (cross3 A' B') (cross3 A B))
        (cross3 (cross3 B' C') (cross3 B C))
        (cross3 (cross3 C' A') (cross3 C A))).det =
    -(threeVecMat
        (cross3 (cross3 A B) (cross3 A' B'))
        (cross3 (cross3 B C) (cross3 B' C'))
        (cross3 (cross3 C A) (cross3 C' A'))).det := by
  simp only [threeVecMat_det_explicit, cross3_zero, cross3_one, cross3_two]; ring

/-- **Self-duality of line perspective**: if P, Q, R are collinear,
    then the "swapped" intersection points (computed A'B'∩AB instead
    of AB∩A'B') are also collinear. -/
theorem perspFromLine_swap (cfg : DesarguesConfig K)
    (h : cfg.perspFromLine) :
    cfg.swap.perspFromLine := by
  unfold DesarguesConfig.perspFromLine collinear at h ⊢
  unfold DesarguesConfig.swap
  rw [collinearity_det_swap, neg_eq_zero]
  exact h

-- ============================================================
-- PART 10: The Forward Direction for Swapped Configuration
-- ============================================================

/-- **Desargues for swapped triangles**: perspective from a point
    implies perspective from a line, for the swapped configuration.
    This is essentially the same theorem — the swap doesn't change
    the mathematical content. -/
theorem desargues_forward_swap (cfg : DesarguesConfig K)
    (h : cfg.swap.perspFromPoint) :
    cfg.swap.perspFromLine :=
  desargues_forward cfg.swap h

/-- **Self-duality chain**: the forward direction + swap gives us
    the forward direction for both orderings of the triangles. -/
theorem desargues_forward_both_orders (cfg : DesarguesConfig K)
    (h : cfg.perspFromPoint) :
    cfg.perspFromLine ∧ cfg.swap.perspFromLine :=
  ⟨desargues_forward cfg h, desargues_forward_swap cfg (perspFromPoint_swap cfg h)⟩

-- ============================================================
-- PART 11: The Algebraic Converse (via non-degeneracy)
-- ============================================================

/-- Non-degeneracy factor. -/
def nonDegeneracyFactor (cfg : DesarguesConfig K) : K :=
  (threeVecMat cfg.A cfg.B cfg.C).det * (threeVecMat cfg.A' cfg.B' cfg.C').det

/-- **Algebraic converse** (over integral domains): if both triangles are
    non-degenerate and in perspective from a line, then in perspective
    from a point. -/
theorem desargues_converse [IsDomain K] (cfg : DesarguesConfig K)
    (hline : cfg.perspFromLine)
    (hnd : nonDegeneracyFactor cfg ≠ 0) :
    cfg.perspFromPoint := by
  unfold DesarguesConfig.perspFromPoint concurrent
  unfold DesarguesConfig.perspFromLine collinear at hline
  rw [desargues_identity] at hline
  exact (mul_eq_zero.mp hline).elim id (absurd · hnd)

/-- **Biconditional** for non-degenerate triangles over integral domains. -/
theorem desargues_iff [IsDomain K] (cfg : DesarguesConfig K)
    (hnd : nonDegeneracyFactor cfg ≠ 0) :
    cfg.perspFromPoint ↔ cfg.perspFromLine :=
  ⟨desargues_forward cfg, fun h => desargues_converse cfg h hnd⟩

-- ============================================================
-- PART 12: The Double Swap is Identity
-- ============================================================

/-- Swapping twice recovers the original configuration. -/
theorem swap_swap (cfg : DesarguesConfig K) : cfg.swap.swap = cfg := rfl

/-- Swapping preserves non-degeneracy (up to commutativity). -/
theorem nonDegeneracy_swap (cfg : DesarguesConfig K) :
    nonDegeneracyFactor cfg.swap = nonDegeneracyFactor cfg := by
  unfold nonDegeneracyFactor DesarguesConfig.swap
  ring

-- ============================================================
-- PART 13: Summary
-- ============================================================

/-
## Summary: Self-Duality of Desargues's Theorem

### Key results (all 0 sorries):

**Fundamental duality (definitional)**:
1. `collinear_eq_concurrent`: Both are det = 0 (rfl)
2. `dual_perspFromPoint_eq_perspFromLine`: Perspective from a point of the
   dual configuration IS perspective from a line of the original (rfl)

**Forward direction**:
3. `desargues_forward`: perspFromPoint → perspFromLine (over any CommRing K)

**Self-duality results**:
4. `perspFromPoint_swap`: perspFromPoint is symmetric in the two triangles
5. `perspFromLine_swap`: perspFromLine is symmetric in the two triangles
6. `desargues_forward_both_orders`: Forward direction + swap for both orderings
7. `desargues_dual_forward`: Forward applied to the dual configuration
8. `desargues_identity_swap`: The identity with triangles swapped
9. `perspectivity_det_swap`: Perspectivity determinant negates under swap
10. `collinearity_det_swap`: Collinearity determinant negates under swap

**Algebraic converse**:
11. `desargues_converse`: Over integral domains with non-degeneracy
12. `desargues_iff`: Full biconditional

**Structural**:
13. `swap_swap`: Double swap is identity (rfl)
14. `nonDegeneracy_swap`: Non-degeneracy is swap-invariant

### Mathematical insight:

Self-duality has two aspects:

1. **Definitional duality** (collinear = concurrent, dual config):
   In homogeneous coordinates, points and lines are both K³ vectors.
   The dual of "perspective from a point" IS "perspective from a line."
   This is captured by `dual_perspFromPoint_eq_perspFromLine`.

2. **Algebraic duality** (the Desargues identity):
   det(P,Q,R) = det(AA',BB',CC') · det(ABC) · det(A'B'C')
   The RHS is manifestly symmetric in (A,B,C) ↔ (A',B',C') (up to
   reordering the product). This means the forward direction for
   either ordering of the triangles implies the collinearity condition,
   which is also symmetric.
-/

end DesarguesTheoremOQ04
