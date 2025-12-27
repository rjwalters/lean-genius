import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-!
# Desargues's Theorem

## What This Proves
Desargues's Theorem (Wiedijk's #87): If two triangles ABC and A'B'C' are in **perspective
from a point** (i.e., lines AA', BB', CC' are concurrent at a point O), then they are in
**perspective from a line** (i.e., the intersections P = AB ∩ A'B', Q = BC ∩ B'C',
R = CA ∩ C'A' are collinear).

The converse also holds: if two triangles are in perspective from a line, they are in
perspective from a point.

## Historical Context
Girard Desargues (1591-1661) was a French mathematician who is considered one of the
founders of projective geometry. He published this theorem in 1639 in a work on conic
sections. The theorem is remarkable because:
1. It is self-dual in projective geometry (the dual statement is also Desargues's theorem)
2. It characterizes Desarguesian planes - those where the theorem holds
3. It fails in some non-Desarguesian projective planes (finite planes of certain orders)

## Approach
- **Foundation (from Mathlib):** We use Mathlib's linear algebra for vectors and cross products.
- **Projective Points:** Points in the projective plane are represented as nonzero vectors
  in ℝ³ (homogeneous coordinates), where scalar multiples represent the same point.
- **Lines:** A line through two points p, q is represented by their cross product p ×₃ q.
- **Collinearity:** Three points are collinear iff their determinant is zero.
- **Concurrence:** Three lines are concurrent iff the determinant of their coefficients is zero.

## Status
- [x] Core theorem statement
- [x] Homogeneous coordinate representation
- [x] Helper lemmas (all complete)
- [x] Key algebraic identity (Desargues identity - complete)
- [x] Main theorem (forward direction - complete, no sorries)
- [x] Converse theorem (complete, no sorries)
- [x] Special cases (complete, no sorries)
- [x] Uses Mathlib for linear algebra foundations

## Mathlib Dependencies
- Cross product in ℝ³ (Mathlib.LinearAlgebra.CrossProduct)
- Matrix determinant (Mathlib.LinearAlgebra.Matrix.Determinant.Basic)
- Real number arithmetic

Historical Note: Desargues's theorem is one of the most fundamental results in projective
geometry. It's notable that the theorem is true in any projective space of dimension ≥ 3,
and in any projective plane that can be embedded in such a space, but can fail in certain
abstract projective planes.
-/

set_option linter.unusedVariables false

open Matrix

-- ============================================================
-- PART 1: Projective Geometry Setup
-- ============================================================

/-- Notation for the cross product in ℝ³ -/
local notation a " ×₃ " b => crossProduct a b

/-- A point in the projective plane is represented as a nonzero vector in ℝ³.
    Two vectors represent the same projective point iff one is a scalar multiple
    of the other. -/
abbrev ProjPoint := Fin 3 → ℝ

/-- A projective point is valid (nonzero) -/
def ProjPoint.valid (p : ProjPoint) : Prop := p ≠ 0

/-- A line in the projective plane, represented in homogeneous coordinates.
    A point p lies on line l iff p · l = 0. -/
abbrev ProjLine := Fin 3 → ℝ

/-- A projective line is valid (nonzero) -/
def ProjLine.valid (l : ProjLine) : Prop := l ≠ 0

-- ============================================================
-- PART 2: Fundamental Operations
-- ============================================================

/-- The line through two distinct points is their cross product. -/
noncomputable def lineThrough (p q : ProjPoint) : ProjLine := p ×₃ q

/-- The intersection of two distinct lines is their cross product. -/
noncomputable def lineIntersection (l m : ProjLine) : ProjPoint := l ×₃ m

/-- A point lies on a line iff their dot product is zero. -/
def pointOnLine (p : ProjPoint) (l : ProjLine) : Prop :=
  (∑ i, p i * l i) = 0

-- ============================================================
-- PART 3: Collinearity and Concurrence
-- ============================================================

/-- The 3×3 matrix formed by three vectors as rows. -/
def threeVectorMatrix (u v w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    match i with
    | 0 => u j
    | 1 => v j
    | 2 => w j

/-- Three points are collinear iff the determinant of their coordinate matrix is zero.
    This is equivalent to saying the three vectors are linearly dependent. -/
def collinear (p q r : ProjPoint) : Prop :=
  (threeVectorMatrix p q r).det = 0

/-- Three lines are concurrent iff the determinant of their coefficient matrix is zero.
    By duality, this uses the same determinant condition. -/
def concurrent (l m n : ProjLine) : Prop :=
  (threeVectorMatrix l m n).det = 0

-- ============================================================
-- PART 4: Perspective Configurations
-- ============================================================

/-- Two triangles ABC and A'B'C' are in **perspective from a point** if the lines
    AA', BB', CC' all pass through a common point O.

    We express this as: the three lines AA', BB', CC' are concurrent. -/
def perspectiveFromPoint (A B C A' B' C' : ProjPoint) : Prop :=
  concurrent (lineThrough A A') (lineThrough B B') (lineThrough C C')

/-- The three intersection points for perspective from a line:
    - P = AB ∩ A'B' (intersection of corresponding sides AB and A'B')
    - Q = BC ∩ B'C' (intersection of corresponding sides BC and B'C')
    - R = CA ∩ C'A' (intersection of corresponding sides CA and C'A') -/
noncomputable def perspectiveIntersectionP (A B A' B' : ProjPoint) : ProjPoint :=
  lineIntersection (lineThrough A B) (lineThrough A' B')

noncomputable def perspectiveIntersectionQ (B C B' C' : ProjPoint) : ProjPoint :=
  lineIntersection (lineThrough B C) (lineThrough B' C')

noncomputable def perspectiveIntersectionR (C A C' A' : ProjPoint) : ProjPoint :=
  lineIntersection (lineThrough C A) (lineThrough C' A')

/-- Two triangles ABC and A'B'C' are in **perspective from a line** if the intersections
    P = AB ∩ A'B', Q = BC ∩ B'C', R = CA ∩ C'A' are collinear. -/
def perspectiveFromLine (A B C A' B' C' : ProjPoint) : Prop :=
  collinear
    (perspectiveIntersectionP A B A' B')
    (perspectiveIntersectionQ B C B' C')
    (perspectiveIntersectionR C A C' A')

-- ============================================================
-- PART 5: Helper Lemmas
-- ============================================================

/-- The cross product of a vector with itself is zero. -/
theorem crossProduct_self (a : Fin 3 → ℝ) : a ×₃ a = 0 := by
  ext i
  fin_cases i <;> simp [crossProduct] <;> ring

/-- Cross product identity: a ×₃ (b ×₃ c) = b * (a · c) - c * (a · b)
    This is the vector triple product / BAC-CAB rule. -/
theorem cross_triple_product (a b c : Fin 3 → ℝ) :
    a ×₃ (b ×₃ c) = (∑ i, a i * c i) • b - (∑ i, a i * b i) • c := by
  ext i
  fin_cases i <;> simp [crossProduct, Fin.sum_univ_three] <;> ring

/-- The scalar triple product [a, b, c] = a · (b × c) equals the determinant of the
    matrix with a, b, c as rows. -/
theorem scalar_triple_product_eq_det (a b c : Fin 3 → ℝ) :
    ∑ i, a i * (b ×₃ c) i = (threeVectorMatrix a b c).det := by
  simp only [threeVectorMatrix, crossProduct, Matrix.det_fin_three, Matrix.of_apply]
  ring

/-- The determinant of the threeVectorMatrix expanded explicitly. -/
theorem threeVectorMatrix_det_explicit (u v w : Fin 3 → ℝ) :
    (threeVectorMatrix u v w).det =
      u 0 * (v 1 * w 2 - v 2 * w 1) -
      u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0) := by
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply]
  ring

/-- The cross product expanded component-wise. -/
theorem crossProduct_components (a b : Fin 3 → ℝ) :
    (a ×₃ b) 0 = a 1 * b 2 - a 2 * b 1 ∧
    (a ×₃ b) 1 = a 2 * b 0 - a 0 * b 2 ∧
    (a ×₃ b) 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [crossProduct]

/-- If the first row of a 3x3 matrix is zero, det = 0 -/
theorem threeVectorMatrix_det_zero_of_first_zero (v w : Fin 3 → ℝ) :
    (threeVectorMatrix 0 v w).det = 0 := by
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply]
  simp only [Pi.zero_apply, zero_mul, sub_zero, add_zero, zero_sub, neg_zero]

-- ============================================================
-- PART 6: Key Identity - Scalar Triple Product of Cross Products
-- ============================================================

/-- The scalar triple product of three cross products.
    This is THE key algebraic identity underlying Desargues's theorem.

    For vectors a, b, c, d, e, f in ℝ³:
    det(a×b, c×d, e×f) can be expressed as a polynomial in the determinants
    of various combinations of a, b, c, d, e, f.

    This identity, proved by direct computation (the `ring` tactic verifies
    the polynomial equality), is what makes Desargues's theorem hold in ℝ³
    (and more generally in any 3-dimensional vector space over a field). -/
theorem scalar_triple_of_cross_products (a b c d e f : Fin 3 → ℝ) :
    (threeVectorMatrix (a ×₃ b) (c ×₃ d) (e ×₃ f)).det =
      (threeVectorMatrix a c e).det * (threeVectorMatrix b d f).det -
      (threeVectorMatrix a c f).det * (threeVectorMatrix b d e).det -
      (threeVectorMatrix a d e).det * (threeVectorMatrix b c f).det +
      (threeVectorMatrix a d f).det * (threeVectorMatrix b c e).det +
      (threeVectorMatrix a e f).det * (threeVectorMatrix b c d).det -
      (threeVectorMatrix a e d).det * (threeVectorMatrix b c f).det := by
  simp only [threeVectorMatrix_det_explicit, crossProduct]
  ring

-- ============================================================
-- PART 7: Desargues Identity
-- ============================================================

/-- **The Desargues Identity**

    This is the core algebraic fact that makes Desargues's theorem work.
    When applied to the specific vectors in the Desargues configuration,
    this identity shows that the collinearity determinant factors through
    the concurrence determinant.

    Specifically, for the Desargues configuration:
    - Lines through corresponding vertices: AA', BB', CC'
    - Intersection points: P = AB ∩ A'B', Q = BC ∩ B'C', R = CA ∩ C'A'

    The determinant det(P, Q, R) (which equals 0 iff P, Q, R collinear)
    equals det(AA', BB', CC') (which equals 0 iff AA', BB', CC' concurrent)
    times a factor K.

    This is verified by the `ring` tactic through direct polynomial computation
    on the 18 coordinate variables. -/
theorem desargues_identity (A B C A' B' C' : Fin 3 → ℝ) :
    let P := (A ×₃ B) ×₃ (A' ×₃ B')
    let Q := (B ×₃ C) ×₃ (B' ×₃ C')
    let R := (C ×₃ A) ×₃ (C' ×₃ A')
    let concurrenceDet := (threeVectorMatrix (A ×₃ A') (B ×₃ B') (C ×₃ C')).det
    (threeVectorMatrix P Q R).det =
      concurrenceDet * (
        (threeVectorMatrix A B C).det * (threeVectorMatrix A' B' C').det -
        (threeVectorMatrix A B C').det * (threeVectorMatrix A' B' C).det
      ) := by
  simp only [threeVectorMatrix_det_explicit, crossProduct]
  ring

/-- The "K factor" in Desargues's identity, representing the non-degeneracy
    condition for the converse direction. -/
noncomputable def desargues_K (A B C A' B' C' : Fin 3 → ℝ) : ℝ :=
  (threeVectorMatrix A B C).det * (threeVectorMatrix A' B' C').det -
  (threeVectorMatrix A B C').det * (threeVectorMatrix A' B' C).det

/-- The Desargues identity restated using K. -/
theorem desargues_identity' (A B C A' B' C' : Fin 3 → ℝ) :
    let P := (A ×₃ B) ×₃ (A' ×₃ B')
    let Q := (B ×₃ C) ×₃ (B' ×₃ C')
    let R := (C ×₃ A) ×₃ (C' ×₃ A')
    (threeVectorMatrix P Q R).det =
      (threeVectorMatrix (A ×₃ A') (B ×₃ B') (C ×₃ C')).det * desargues_K A B C A' B' C' := by
  simp only [desargues_K, threeVectorMatrix_det_explicit, crossProduct]
  ring

-- ============================================================
-- PART 8: Main Theorem - Desargues's Theorem
-- ============================================================

/-- **Desargues's Theorem** (Wiedijk #87) - Forward Direction

    If two triangles ABC and A'B'C' are in perspective from a point O
    (meaning the lines AA', BB', CC' are concurrent at O),
    then they are in perspective from a line
    (meaning the points P = AB ∩ A'B', Q = BC ∩ B'C', R = CA ∩ C'A' are collinear).

    **Proof:**
    By the Desargues identity, det(P, Q, R) = det(AA', BB', CC') * K
    for some expression K. When AA', BB', CC' are concurrent,
    det(AA', BB', CC') = 0, so det(P, Q, R) = 0 * K = 0,
    meaning P, Q, R are collinear. -/
theorem desargues_theorem (A B C A' B' C' : ProjPoint)
    (hA : ProjPoint.valid A) (hB : ProjPoint.valid B) (hC : ProjPoint.valid C)
    (hA' : ProjPoint.valid A') (hB' : ProjPoint.valid B') (hC' : ProjPoint.valid C')
    (h_perspective : perspectiveFromPoint A B C A' B' C') :
    perspectiveFromLine A B C A' B' C' := by
  unfold perspectiveFromLine perspectiveIntersectionP perspectiveIntersectionQ perspectiveIntersectionR
  unfold collinear lineIntersection lineThrough
  unfold perspectiveFromPoint concurrent lineThrough at h_perspective
  -- Apply the Desargues identity
  rw [desargues_identity]
  -- The hypothesis says the concurrence determinant is 0
  rw [h_perspective]
  -- 0 * anything = 0
  ring

/-- **Desargues's Theorem - Converse** (with non-degeneracy hypothesis)

    If two triangles ABC and A'B'C' are in perspective from a line
    (meaning P = AB ∩ A'B', Q = BC ∩ B'C', R = CA ∩ C'A' are collinear),
    AND the configuration is non-degenerate (K ≠ 0),
    then they are in perspective from a point
    (meaning the lines AA', BB', CC' are concurrent).

    **Proof:**
    By the Desargues identity, det(P, Q, R) = det(AA', BB', CC') * K.
    We know det(P, Q, R) = 0 (collinearity) and K ≠ 0 (non-degeneracy).
    Therefore det(AA', BB', CC') = 0 / K = 0, i.e., the lines are concurrent.

    **Note on non-degeneracy:**
    The factor K = det(ABC) * det(A'B'C') - det(ABC') * det(A'B'C) measures
    whether the two triangles are "in general position". It is nonzero when
    neither triangle is degenerate and they are not specially aligned. -/
theorem desargues_theorem_converse (A B C A' B' C' : ProjPoint)
    (hA : ProjPoint.valid A) (hB : ProjPoint.valid B) (hC : ProjPoint.valid C)
    (hA' : ProjPoint.valid A') (hB' : ProjPoint.valid B') (hC' : ProjPoint.valid C')
    (h_nondegen : desargues_K A B C A' B' C' ≠ 0)
    (h_perspective : perspectiveFromLine A B C A' B' C') :
    perspectiveFromPoint A B C A' B' C' := by
  unfold perspectiveFromPoint concurrent lineThrough
  unfold perspectiveFromLine collinear perspectiveIntersectionP perspectiveIntersectionQ
    perspectiveIntersectionR lineIntersection lineThrough at h_perspective
  -- By the Desargues identity: det(P,Q,R) = concurrenceDet * K
  -- We know det(P,Q,R) = 0 (h_perspective) and K ≠ 0 (h_nondegen)
  -- So concurrenceDet = 0
  have h := desargues_identity' A B C A' B' C'
  simp only at h
  rw [h] at h_perspective
  -- h_perspective : concurrenceDet * K = 0
  -- h_nondegen : K ≠ 0
  -- Therefore concurrenceDet = 0
  exact mul_eq_zero.mp h_perspective |>.resolve_right h_nondegen

-- ============================================================
-- PART 9: Full Equivalence
-- ============================================================

/-- **Desargues's Theorem - Full Equivalence** (with non-degeneracy)

    For non-degenerate configurations (K ≠ 0):
    Two triangles are in perspective from a point if and only if they are
    in perspective from a line.

    This captures the complete content of Desargues's theorem and its converse
    for generic triangle configurations. -/
theorem desargues_theorem_iff (A B C A' B' C' : ProjPoint)
    (hA : ProjPoint.valid A) (hB : ProjPoint.valid B) (hC : ProjPoint.valid C)
    (hA' : ProjPoint.valid A') (hB' : ProjPoint.valid B') (hC' : ProjPoint.valid C')
    (h_nondegen : desargues_K A B C A' B' C' ≠ 0) :
    perspectiveFromPoint A B C A' B' C' ↔ perspectiveFromLine A B C A' B' C' :=
  ⟨desargues_theorem A B C A' B' C' hA hB hC hA' hB' hC',
   desargues_theorem_converse A B C A' B' C' hA hB hC hA' hB' hC' h_nondegen⟩

-- ============================================================
-- PART 10: Special Cases and Examples
-- ============================================================

/-- Example: Triangles that share a vertex are trivially in perspective from that vertex.
    When A = A', the line AA' degenerates (cross product is zero), and the
    determinant condition for concurrence is satisfied. -/
theorem shared_vertex_perspective (A B C B' C' : ProjPoint)
    (hA : ProjPoint.valid A) (hB : ProjPoint.valid B) (hC : ProjPoint.valid C)
    (hB' : ProjPoint.valid B') (hC' : ProjPoint.valid C') :
    perspectiveFromPoint A B C A B' C' := by
  unfold perspectiveFromPoint concurrent lineThrough
  have h : A ×₃ A = 0 := crossProduct_self A
  simp only [threeVectorMatrix_det_explicit]
  simp only [h, Pi.zero_apply, zero_mul, sub_zero, add_zero, zero_sub, neg_zero]

/-- A concrete numerical example: when all points are zero vectors,
    the configuration is degenerate and collinear. -/
example : collinear (fun _ => (0 : ℝ)) (fun _ => 0) (fun _ => 0) := by
  unfold collinear threeVectorMatrix
  simp [Matrix.det_fin_three]

/-- Collinearity is reflexive for repeated points. -/
theorem collinear_repeated (p q : ProjPoint) : collinear p p q := by
  unfold collinear threeVectorMatrix
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  ring

-- ============================================================
-- PART 11: Connections and Historical Context
-- ============================================================

/-!
### Projective Duality

Desargues's theorem is remarkable for being **self-dual**. In projective geometry:
- Points and lines are dual concepts
- "Point lies on line" is dual to "line passes through point"
- "Three points are collinear" is dual to "three lines are concurrent"

The dual of Desargues's theorem (swapping points↔lines, collinear↔concurrent)
is... Desargues's theorem again! This self-duality is a beautiful property.

### Non-Desarguesian Planes

Not all projective planes satisfy Desargues's theorem:
- Any projective plane that can be embedded in a 3D projective space is Desarguesian
- The Moulton plane is a non-Desarguesian plane
- Finite projective planes of order p² (p prime) can be non-Desarguesian

A projective plane is called **Desarguesian** if Desargues's theorem holds.
This is equivalent to the plane being coordinatizable by a division ring.

### The Non-Degeneracy Condition

The factor K = det(ABC) * det(A'B'C') - det(ABC') * det(A'B'C) in our formalization
captures the "general position" requirement. It is nonzero when:
- Neither triangle ABC nor A'B'C' is degenerate (i.e., vertices are not collinear)
- The triangles are not specially aligned

For most practical applications in computer graphics and vision, configurations
are generic and K ≠ 0 holds automatically.

### Applications

1. **Computer Graphics**: Perspective projections and 3D rendering
2. **Computer Vision**: Camera calibration and 3D reconstruction
3. **Architecture**: Perspective drawing techniques
4. **Art**: Understanding perspective in paintings

### Relationship to Other Theorems

- **Pappus's Theorem**: A special case of Desargues for configurations on two lines
- **Pascal's Theorem**: Related theorem for hexagons inscribed in conics
- **Fundamental Theorem of Projective Geometry**: Desargues implies this
-/

-- ============================================================
-- Export main results
-- ============================================================

#check @perspectiveFromPoint
#check @perspectiveFromLine
#check @desargues_theorem
#check @desargues_theorem_converse
#check @desargues_theorem_iff
#check @shared_vertex_perspective
#check @desargues_identity
#check @desargues_K
