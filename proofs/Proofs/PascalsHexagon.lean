import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Tactic

/-!
# Pascal's Hexagon Theorem

## What This Proves
Pascal's Hexagon Theorem (Wiedijk's #28): If a hexagon ABCDEF is inscribed in a conic section,
then the three pairs of opposite sides meet in three collinear points:
- P = AB ∩ DE (intersection of opposite sides AB and DE)
- Q = BC ∩ EF (intersection of opposite sides BC and EF)
- R = CD ∩ FA (intersection of opposite sides CD and FA)

These three points P, Q, R are always collinear. This line is called the **Pascal line**.

## Historical Context
Blaise Pascal discovered this theorem in 1639, at age 16! It's one of the most beautiful
results in projective geometry. The theorem generalizes to:
- Degenerate conics (pairs of lines)
- Complex projective plane
- Any projective plane over a field

**Dual Theorem (Brianchon's Theorem):**
If a hexagon is *circumscribed* about a conic (each side tangent to the conic), then the
three main diagonals (AD, BE, CF) are concurrent.

## Approach
We use **projective coordinates** (homogeneous coordinates in ℝ³):
- Points are nonzero vectors in ℝ³ (up to scalar multiple)
- Lines are also nonzero vectors (the line through p, q is p × q)
- A point p lies on line l iff p · l = 0
- Three points are collinear iff det(p, q, r) = 0

A **conic** in projective coordinates is represented by a symmetric 3×3 matrix C.
A point p lies on the conic iff p^T C p = 0 (the quadratic form vanishes).

## Status
- [x] Core theorem statement
- [x] Projective geometry setup
- [x] Conic section definition
- [x] Hexagon inscribed condition
- [x] Main theorem with axiom for Pascal constraint

## Mathlib Dependencies
- Cross product in ℝ³ (Mathlib.LinearAlgebra.CrossProduct)
- Matrix determinant (Mathlib.LinearAlgebra.Matrix.Determinant.Basic)
-/

set_option linter.unusedVariables false

open Matrix

-- ============================================================
-- PART 1: Projective Geometry Setup
-- ============================================================

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
noncomputable def lineThrough (p q : ProjPoint) : ProjLine := crossProduct p q

/-- The intersection of two distinct lines is their cross product. -/
noncomputable def lineIntersection (l m : ProjLine) : ProjPoint := crossProduct l m

/-- A point lies on a line iff their dot product is zero. -/
def pointOnLine (p : ProjPoint) (l : ProjLine) : Prop :=
  (∑ i, p i * l i) = 0

-- ============================================================
-- PART 3: Collinearity
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

/-- Three lines are concurrent iff the determinant of their coefficient matrix is zero. -/
def concurrent (l m n : ProjLine) : Prop :=
  (threeVectorMatrix l m n).det = 0

-- ============================================================
-- PART 4: Conic Sections
-- ============================================================

/-- A conic in the projective plane is represented by a symmetric 3×3 matrix.
    A point p = (x, y, z) lies on the conic iff p^T C p = 0, i.e.,
    Σᵢⱼ Cᵢⱼ pᵢ pⱼ = 0. -/
abbrev Conic := Matrix (Fin 3) (Fin 3) ℝ

/-- The quadratic form associated with a conic, evaluated at a point.
    This equals p^T C p = Σᵢⱼ Cᵢⱼ pᵢ pⱼ -/
noncomputable def conicQuadraticForm (C : Conic) (p : ProjPoint) : ℝ :=
  ∑ i, ∑ j, C i j * p i * p j

/-- A point lies on a conic iff the quadratic form vanishes. -/
def pointOnConic (p : ProjPoint) (C : Conic) : Prop :=
  conicQuadraticForm C p = 0

/-- A conic is non-degenerate (not a pair of lines or empty).
    This is equivalent to det(C) ≠ 0. -/
def Conic.nondegenerate (C : Conic) : Prop := C.det ≠ 0

/-- A conic is symmetric (Cᵢⱼ = Cⱼᵢ). We work with symmetric conics. -/
def Conic.symmetric (C : Conic) : Prop := ∀ i j, C i j = C j i

-- ============================================================
-- PART 5: Hexagon Inscribed in Conic
-- ============================================================

/-- Six points forming a hexagon ABCDEF inscribed in a conic C.
    This means all six vertices lie on the conic. -/
structure InscribedHexagon (C : Conic) where
  A : ProjPoint
  B : ProjPoint
  C' : ProjPoint  -- Using C' to avoid conflict with Conic C
  D : ProjPoint
  E : ProjPoint
  F : ProjPoint
  hA : pointOnConic A C
  hB : pointOnConic B C
  hC : pointOnConic C' C
  hD : pointOnConic D C
  hE : pointOnConic E C
  hF : pointOnConic F C
  -- Validity conditions (points are nonzero in projective space)
  hAvalid : ProjPoint.valid A
  hBvalid : ProjPoint.valid B
  hCvalid : ProjPoint.valid C'
  hDvalid : ProjPoint.valid D
  hEvalid : ProjPoint.valid E
  hFvalid : ProjPoint.valid F

/-- The Pascal point P = AB ∩ DE (intersection of opposite sides) -/
noncomputable def pascalP (hex : InscribedHexagon C) : ProjPoint :=
  lineIntersection (lineThrough hex.A hex.B) (lineThrough hex.D hex.E)

/-- The Pascal point Q = BC ∩ EF (intersection of opposite sides) -/
noncomputable def pascalQ (hex : InscribedHexagon C) : ProjPoint :=
  lineIntersection (lineThrough hex.B hex.C') (lineThrough hex.E hex.F)

/-- The Pascal point R = CD ∩ FA (intersection of opposite sides) -/
noncomputable def pascalR (hex : InscribedHexagon C) : ProjPoint :=
  lineIntersection (lineThrough hex.C' hex.D) (lineThrough hex.F hex.A)

-- ============================================================
-- PART 6: Pascal's Constraint
-- ============================================================

/-- The Pascal constraint: when 6 points lie on a conic, this algebraic
    condition holds. This captures the key geometric relationship.

    For hexagon ABCDEF on conic, the intersections of opposite sides
    P = AB ∩ DE, Q = BC ∩ EF, R = CD ∩ FA satisfy det(P, Q, R) = 0. -/
def pascalConstraint (A B C D E F : ProjPoint) : Prop :=
  let P := lineIntersection (lineThrough A B) (lineThrough D E)
  let Q := lineIntersection (lineThrough B C) (lineThrough E F)
  let R := lineIntersection (lineThrough C D) (lineThrough F A)
  (threeVectorMatrix P Q R).det = 0

-- ============================================================
-- PART 7: Main Theorem
-- ============================================================

/-- **Six points on a conic satisfy the Pascal constraint.**

    This is the deep geometric fact at the heart of Pascal's theorem.
    Mathematically, this follows from:
    - Any 5 points in general position determine a unique conic
    - The 6th point lying on this conic constrains the geometry
    - This constraint forces the Pascal line to exist

    The proof uses the theory of cubic curves and Bézout's theorem:
    consider the degenerate cubic consisting of lines AB, CD, EF
    and the degenerate cubic consisting of lines BC, DE, FA.
    These two cubics intersect in 9 points (by Bézout), but 6 of
    these points are A, B, C, D, E, F on the conic. By the
    Cayley-Bacharach theorem, the remaining 3 points P, Q, R
    (the intersection points of opposite sides) are collinear. -/
axiom conic_implies_pascal_constraint :
  ∀ (C : Conic) (hex : InscribedHexagon C),
    pascalConstraint hex.A hex.B hex.C' hex.D hex.E hex.F

/-- **Pascal's Hexagon Theorem** (Wiedijk #28)

    If a hexagon ABCDEF is inscribed in a conic, then the three
    intersection points of opposite sides are collinear:
    - P = AB ∩ DE
    - Q = BC ∩ EF
    - R = CD ∩ FA

    The line through P, Q, R is called the **Pascal line** of the hexagon.

    **Historical note:** Blaise Pascal proved this at age 16 in 1639,
    calling it the "Mystic Hexagram" (Hexagrammum Mysticum). -/
theorem pascal_hexagon_theorem (C : Conic) (hex : InscribedHexagon C) :
    collinear (pascalP hex) (pascalQ hex) (pascalR hex) := by
  -- Unfold definitions to match pascalConstraint
  unfold collinear pascalP pascalQ pascalR
  -- The Pascal constraint is exactly the collinearity condition
  have h := conic_implies_pascal_constraint C hex
  unfold pascalConstraint at h
  exact h

-- ============================================================
-- PART 8: Special Cases
-- ============================================================

/-! **Pappus's Theorem** as a special case of Pascal's theorem

When the conic degenerates to a pair of lines:
- If A, C, E lie on line l₁
- And B, D, F lie on line l₂
Then P = AB ∩ DE, Q = BC ∩ EF, R = CD ∩ FA are collinear.

This is Pascal's theorem for the degenerate conic l₁ ∪ l₂. -/

/-- Three points are collinear in the sense of lying on a common line. -/
def collinearOnLine (P Q R : ProjPoint) (l : ProjLine) : Prop :=
  pointOnLine P l ∧ pointOnLine Q l ∧ pointOnLine R l

-- ============================================================
-- PART 9: Dual Theorem (Brianchon's Theorem)
-- ============================================================

/-! **Brianchon's Theorem** (Dual of Pascal's Theorem)

If a hexagon is *circumscribed* about a conic (each side is tangent
to the conic), then the three main diagonals AD, BE, CF are concurrent.

This is the projective dual of Pascal's theorem:
- Points ↔ Lines
- Collinear ↔ Concurrent
- Inscribed ↔ Circumscribed -/

/-- The diagonal connecting vertices A and D of a hexagon. -/
noncomputable def hexagonDiagonal1 (hex : InscribedHexagon C) : ProjLine :=
  lineThrough hex.A hex.D

/-- The diagonal connecting vertices B and E of a hexagon. -/
noncomputable def hexagonDiagonal2 (hex : InscribedHexagon C) : ProjLine :=
  lineThrough hex.B hex.E

/-- The diagonal connecting vertices C' and F of a hexagon. -/
noncomputable def hexagonDiagonal3 (hex : InscribedHexagon C) : ProjLine :=
  lineThrough hex.C' hex.F

-- ============================================================
-- PART 10: Historical Notes
-- ============================================================

/-!
### Historical Context

**Blaise Pascal (1623-1662)** discovered this theorem in 1639, at age 16!
He called it the "Mystic Hexagram" (Hexagrammum Mysticum). The original
proof was lost, but the result was recorded by Leibniz.

### The 60 Pascal Lines

Given 6 points on a conic, there are 60 different ways to connect them
as a hexagon (permutations / dihedral symmetry). Each gives a Pascal
line. These 60 lines have remarkable incidence properties:
- They meet in 20 "Steiner points" (3 lines each)
- They meet in 60 "Kirkman points" (3 lines each)
- They meet in 15 "Plücker lines" (4 points each)

### Proof Methods

1. **Projective/Cross-ratio**: Most elegant, uses cross-ratio properties
2. **Algebraic**: Express conic constraint, compute determinants
3. **Bézout/Cayley-Bacharach**: Two cubic curves, 9 intersection points
4. **Synthetic**: Classical ruler-and-compass arguments

### Relationship to Other Theorems

- **Desargues's Theorem**: About perspective triangles (Wiedijk #87)
- **Pappus's Theorem**: Special case where conic degenerates to two lines
- **Brianchon's Theorem**: Projective dual (circumscribed hexagon)
-/

-- ============================================================
-- PART 11: Proof for Standard Conic (Axiom Elimination)
-- ============================================================

/-!
## Partial Proof of Pascal's Theorem from First Principles

The axiom `conic_implies_pascal_constraint` above axiomatizes the key geometric fact.
Below we prove it for the standard conic x₀² + x₁² = x₂² using rational parametrization.

### Strategy
1. **Parametrize**: Points on x₀² + x₁² = x₂² as P(t) = (1-t², 2t, 1+t²)
2. **Compute**: det(P,Q,R) becomes a polynomial in 6 parameters (a,b,c,d,e,f)
3. **Verify**: The polynomial is identically zero — `ring` closes the proof

### Remaining for Full Axiom Elimination
- Prove any non-degenerate conic is projectively equivalent to the standard one
- Prove `pascalConstraint` is preserved under projective transformations
- Handle degenerate conics (pairs of lines)
-/

/-- A point on the standard conic x₀² + x₁² = x₂² via rational parametrization.
    P(t) = (1 - t², 2t, 1 + t²) satisfies (1-t²)² + (2t)² = (1+t²)².
    This covers all real points on the conic (since x₂ ≠ 0 for all real points). -/
def stdConicPoint (t : ℝ) : ProjPoint :=
  fun i => match i with
  | 0 => 1 - t ^ 2
  | 1 => 2 * t
  | 2 => 1 + t ^ 2

/-- The standard conic matrix: diag(1, 1, -1) represents x₀² + x₁² - x₂² = 0. -/
def stdConic : Conic :=
  Matrix.of fun i j => match i, j with
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => -1
  | _, _ => 0

/-- Points from stdConicPoint lie on the standard conic. -/
theorem stdConicPoint_on_conic (t : ℝ) : pointOnConic (stdConicPoint t) stdConic := by
  unfold pointOnConic conicQuadraticForm stdConicPoint stdConic
  simp only [Fin.sum_univ_three, Fin.isValue, Matrix.of_apply]
  ring

/-- **Pascal's theorem for the standard conic** — proved by polynomial identity.

    When all 6 points are rationally parametrized on x₀² + x₁² = x₂², the
    determinant det(P,Q,R) is identically zero as a polynomial in 6 variables.
    Verified computationally: ~3500 terms cancel to 0 via `ring`.

    This is the core computational step for eliminating `conic_implies_pascal_constraint`. -/
set_option maxHeartbeats 2000000 in
theorem pascal_std_conic_parametrized (a b c d e f : ℝ) :
    pascalConstraint (stdConicPoint a) (stdConicPoint b) (stdConicPoint c)
      (stdConicPoint d) (stdConicPoint e) (stdConicPoint f) := by
  -- Unfold to cross products and determinant (same pattern as DesarguesTheorem.lean)
  unfold pascalConstraint lineIntersection lineThrough stdConicPoint
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  -- The resulting degree-12 polynomial in 6 variables is identically 0
  -- (verified independently via sympy: ~3500 terms cancel)
  ring

-- ============================================================
-- PART 11b: Scalar Triple Product Formula
-- ============================================================

/-!
### Scalar Triple Product for Parametric Circle Points

For points P(a) = (1-a², 2a, 1+a²) on the standard conic, the scalar
triple product (3×3 determinant) has a remarkably simple factored form:

  det(P(a), P(b), P(c)) = 4(a-b)(b-c)(c-a)

This factorization is key to an alternative proof strategy that avoids
expanding the full degree-12 polynomial. By the BAC-CAB identity:

  P = (A×B) × (D×E) = [ABE]D - [ABD]E

where [XYZ] = det(X,Y,Z). The Pascal determinant det(P,Q,R) then becomes
a sum of four terms, each a product of four scalar triple products.
Substituting the factored formula makes the cancellation transparent.
-/

/-- Scalar triple product of three parametric circle points factors as
    4(a-b)(b-c)(c-a). Proved by explicit 3×3 determinant expansion. -/
theorem stdConic_det_factored (a b c : ℝ) :
    (threeVectorMatrix (stdConicPoint a) (stdConicPoint b) (stdConicPoint c)).det =
    4 * (a - b) * (b - c) * (c - a) := by
  unfold threeVectorMatrix stdConicPoint
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  ring

-- ============================================================
-- PART 12: Projective Invariance (Toward General Conics)
-- ============================================================

/-!
## Projective Invariance of Pascal's Constraint

The key fact for lifting from the standard conic to general conics:

1. `det(M·u, M·v, M·w) = det(M) · det(u, v, w)` (determinant multiplicativity)
2. `cross(M·u, M·v) = det(M) · M⁻ᵀ · cross(u, v)` (cross product transforms contravariantly)
3. Together: `collinear (M·p) (M·q) (M·r) ↔ collinear p q r` (when det(M) ≠ 0)
4. And: `pascalConstraint (M·A) (M·B) ... ↔ pascalConstraint A B ...`

### Full axiom elimination roadmap:
- [x] Part 11: Pascal for standard conic via parametrization
- [ ] Part 12: Projective invariance of pascalConstraint (this section, partial)
- [ ] Part 13: Sylvester's law — any non-degenerate conic ≅ standard conic
- [ ] Part 14: Degenerate conics (pair of lines) — separate argument
-/

/-- Apply an invertible matrix M to a projective point.
    In projective geometry, this is a projective transformation. -/
def projTransform (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ProjPoint) : ProjPoint :=
  M.mulVec p

/-- The threeVectorMatrix of M-transformed vectors equals M times the original matrix.
    Specifically: if the rows of the matrix are M·u, M·v, M·w, then the determinant
    is det(M) times det(u, v, w). -/
theorem threeVectorMatrix_projTransform (M : Matrix (Fin 3) (Fin 3) ℝ) (u v w : Fin 3 → ℝ) :
    (threeVectorMatrix (projTransform M u) (projTransform M v) (projTransform M w)).det =
    M.det * (threeVectorMatrix u v w).det := by
  -- Key: threeVectorMatrix (M·u) (M·v) (M·w) = threeVectorMatrix u v w * Mᵀ
  -- (row i of LHS is M applied to row i of RHS, so LHS = RHS * Mᵀ by def of matrix mul)
  -- Then det(LHS) = det(RHS) * det(Mᵀ) = det(RHS) * det(M).
  unfold projTransform
  have h : threeVectorMatrix (M *ᵥ u) (M *ᵥ v) (M *ᵥ w) =
           threeVectorMatrix u v w * M.transpose := by
    ext i j
    fin_cases i <;>
    simp only [threeVectorMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
               Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue] <;>
    ring
  rw [h, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Collinearity is preserved under invertible projective transformations. -/
theorem collinear_projTransform (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det ≠ 0)
    (p q r : ProjPoint) :
    collinear (projTransform M p) (projTransform M q) (projTransform M r) ↔ collinear p q r := by
  unfold collinear
  rw [threeVectorMatrix_projTransform]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hM
  · intro h; rw [h, mul_zero]

/-- **Cross product transformation law (adjugate form):**
    cross(M·u, M·v) = adj(M)ᵀ · cross(u, v)

    Equivalently, cross(M·u, M·v) = det(M) · M⁻ᵀ · cross(u, v) when M is invertible.
    This identity says cross products transform contravariantly under linear maps.
    Verified computationally: degree-3 polynomial identity in 15 variables. -/
-- The cross product identity is a degree-3 polynomial in 15 variables; needs extra heartbeats.
set_option maxHeartbeats 2000000 in
theorem crossProduct_projTransform (M : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    crossProduct (projTransform M u) (projTransform M v) =
    projTransform M.adjugate.transpose (crossProduct u v) := by
  -- Proof: cross(M·u, M·v) = adj(M)ᵀ · cross(u, v)
  -- This is a degree-3 polynomial identity in 15 variables (9 matrix entries + 6 vector entries).
  -- Proved by expanding both sides via cross_apply, mulVec, adjugate_fin_three, and ring.
  unfold projTransform
  ext i
  fin_cases i <;>
  simp only [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue,
             Matrix.adjugate_fin_three, Matrix.transpose_apply, Matrix.of_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Nat.reduceAdd, Fin.reduceFinMk] <;>
  ring

/-- **Pascal constraint is invariant under invertible projective transformations.**

    The key theorem: if 6 points satisfy (or don't satisfy) Pascal's constraint,
    then so do their images under any invertible projective transformation M.

    Proof uses: P' = cross(cross(M·A,M·B), cross(M·D,M·E))
              = cross(adj(M)ᵀ·AB, adj(M)ᵀ·DE)
              = adj(adj(M)ᵀ)ᵀ · cross(AB, DE)
              = det(M) · M · P  (since adj(adj(M)ᵀ) = det(M)·Mᵀ)
    Then det(P',Q',R') = det(M)⁴ · det(P,Q,R). -/
theorem pascalConstraint_projTransform (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det ≠ 0)
    (A B C D E F : ProjPoint) :
    pascalConstraint (projTransform M A) (projTransform M B) (projTransform M C)
      (projTransform M D) (projTransform M E) (projTransform M F)
    ↔ pascalConstraint A B C D E F := by
  unfold pascalConstraint lineIntersection lineThrough
  -- Apply cross product transformation law: cross(M·u, M·v) = adj(M)ᵀ · cross(u,v)
  -- Simp applies bottom-up: first inner cross products (using M), then outer (using adj(M)ᵀ)
  simp only [crossProduct_projTransform]
  -- Now all three vectors are projTransform (adj(adj(M)ᵀ)ᵀ) applied to original intersections
  rw [threeVectorMatrix_projTransform]
  -- Goal: det(adj(adj(M)ᵀ)ᵀ) * det(P,Q,R) = 0 ↔ det(P,Q,R) = 0
  constructor
  · intro h
    have hdet : (M.adjugate.transpose).adjugate.transpose.det ≠ 0 := by
      simp only [Matrix.det_transpose, Matrix.det_adjugate, Fintype.card_fin]
      -- det(M)^2^2 ≠ 0
      exact pow_ne_zero _ (pow_ne_zero _ hM)
    exact (mul_eq_zero.mp h).resolve_left hdet
  · intro h; rw [h, mul_zero]

-- ============================================================
-- PART 13: Parametric Coverage of Standard Conic
-- ============================================================

/-! Every point on the standard conic x₀²+x₁²=x₂² is either:
    (a) A scalar multiple of stdConicPoint(t) for some t (when p₀+p₂ ≠ 0), or
    (b) A scalar multiple of (1, 0, -1) (the "point at infinity", when p₀+p₂ = 0).

    This establishes that the rational parametrization t ↦ (1-t², 2t, 1+t²) covers
    all finite points on the conic, which is needed for the full axiom elimination. -/

/-- The unique point on the standard conic not covered by stdConicPoint:
    (1, 0, -1) satisfies x₀² + x₁² = x₂² (trivially: 1 + 0 = 1). -/
def stdConicInfinity : ProjPoint :=
  fun i => match i with
  | 0 => 1
  | 1 => 0
  | 2 => -1

/-- The point at infinity lies on the standard conic. -/
theorem stdConicInfinity_on_conic : pointOnConic stdConicInfinity stdConic := by
  unfold pointOnConic conicQuadraticForm stdConicInfinity stdConic
  simp only [Fin.sum_univ_three, Fin.isValue, Matrix.of_apply]
  ring

/-- On the standard conic, p₀ + p₂ = 0 characterizes the point at infinity.
    If p is on the conic and p₀ + p₂ = 0, then p₁ = 0 (so p is (α, 0, -α)). -/
theorem stdConic_infinity_char (p : ProjPoint) (hp : pointOnConic p stdConic)
    (h02 : p 0 + p 2 = 0) : p 1 = 0 := by
  unfold pointOnConic conicQuadraticForm stdConic at hp
  simp only [Fin.sum_univ_three, Fin.isValue, Matrix.of_apply, mul_comm, mul_one,
             zero_mul, mul_zero, add_zero, zero_add] at hp
  have h : p 2 = -(p 0) := by linarith
  nlinarith [sq_nonneg (p 1), sq_nonneg (p 0), mul_self_nonneg (p 1)]

/-- **Parametric coverage**: Every point on stdConic with p₀+p₂ ≠ 0 is a scalar
    multiple of stdConicPoint(p₁/(p₀+p₂)).
    Uses the half-angle substitution t = sin θ / (1 + cos θ) from trigonometry. -/
theorem stdConicPoint_covers (p : ProjPoint) (hp : pointOnConic p stdConic)
    (h02 : p 0 + p 2 ≠ 0) :
    ∃ (t k : ℝ), k ≠ 0 ∧ ∀ i, p i = k * stdConicPoint t i := by
  use p 1 / (p 0 + p 2), (p 0 + p 2) / 2
  refine ⟨div_ne_zero h02 two_ne_zero, ?_⟩
  have hconic : p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2 := by
    unfold pointOnConic conicQuadraticForm stdConic at hp
    simp only [Fin.sum_univ_three, Fin.isValue, Matrix.of_apply] at hp
    nlinarith
  intro i; fin_cases i <;> simp only [stdConicPoint] <;> field_simp <;> nlinarith [hconic]

/-
### Roadmap for Full Axiom Elimination

**Completed:**
1. `pascal_std_conic_parametrized`: Pascal's theorem for the standard conic x₀²+x₁²=x₂²
2. `stdConic_det_factored`: Scalar triple product formula det(P(a),P(b),P(c)) = 4(a-b)(b-c)(c-a)
3. `collinear_projTransform`: Collinearity is projectively invariant
4. `threeVectorMatrix_projTransform`: Determinant of transformed vectors = det(M) · original
5. `pascalConstraint_projTransform`: Pascal constraint is projectively invariant
6. `stdConicPoint_covers`: Every finite point on stdConic is stdConicPoint(t)
7. `stdConic_infinity_char`: The point at infinity (1,0,-1) is the only uncovered point
8. `crossProduct_smul_left/right`: Bilinearity of cross product under scaling
9. `pascal_std_conic_infinity_{A,B,C,D,E,F}`: Pascal holds when one vertex is at infinity
10. `det_threeVectorMatrix_smul`: Determinant scales with row scaling
11. `pascalConstraint_smul`: Pascal constraint is invariant under nonzero scaling

**Remaining for full proof:**
1. **stdConic degenerate assembly**: Handle ≥2 vertices at infinity on stdConic.
   Two approaches: (a) rotation trick — apply R(θ) preserving stdConic that moves
   infinity to finite, or (b) direct: if any two vertices coincide projectively,
   det(P,Q,R) = 0 because two Pascal points lie on the same line through the
   repeated point.
2. **Sylvester's law**: Any non-degenerate symmetric conic with real points is congruent
   to diag(1,1,-1). Requires spectral theorem for 3×3 real symmetric matrices.
3. **Final assembly**: Combine Sylvester + stdConic Pascal + projective invariance
   to eliminate `conic_implies_pascal_constraint`.
-/

-- ============================================================
-- PART 14: Bilinearity of Cross Product (Scaling)
-- ============================================================

/-! Cross product is bilinear: scaling either argument scales the result.
    This is needed for the scale-invariance of the Pascal constraint. -/

theorem crossProduct_smul_left (c : ℝ) (u v : Fin 3 → ℝ) :
    crossProduct (c • u) v = c • crossProduct u v := by
  ext i; fin_cases i <;>
    simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons, Fin.isValue] <;> ring

theorem crossProduct_smul_right (c : ℝ) (u v : Fin 3 → ℝ) :
    crossProduct u (c • v) = c • crossProduct u v := by
  ext i; fin_cases i <;>
    simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons, Fin.isValue] <;> ring

-- ============================================================
-- PART 15: Pascal's Theorem — Point at Infinity Cases
-- ============================================================

-- Large polynomial identities: increase heartbeat limit for this section
set_option maxHeartbeats 800000

/-! When one vertex of the hexagon is at the point at infinity (1,0,-1),
    Pascal's constraint still holds. Each of the 6 positions is a separate
    polynomial identity in 5 variables, verified computationally by `ring`.

    Combined with `pascal_std_conic_parametrized` (all 6 finite) and the
    scaling lemma, these cover all configurations on the standard conic. -/

/-- Pascal's constraint when F = (1,0,-1) (point at infinity). -/
theorem pascal_std_conic_infinity_F (a b c d e : ℝ) :
    pascalConstraint (stdConicPoint a) (stdConicPoint b) (stdConicPoint c)
      (stdConicPoint d) (stdConicPoint e) stdConicInfinity := by
  unfold pascalConstraint lineIntersection lineThrough stdConicPoint stdConicInfinity
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

/-- Pascal's constraint when A = (1,0,-1) (point at infinity). -/
theorem pascal_std_conic_infinity_A (b c d e f : ℝ) :
    pascalConstraint stdConicInfinity (stdConicPoint b) (stdConicPoint c)
      (stdConicPoint d) (stdConicPoint e) (stdConicPoint f) := by
  unfold pascalConstraint lineIntersection lineThrough stdConicPoint stdConicInfinity
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

/-- Pascal's constraint when B = (1,0,-1) (point at infinity). -/
theorem pascal_std_conic_infinity_B (a c d e f : ℝ) :
    pascalConstraint (stdConicPoint a) stdConicInfinity (stdConicPoint c)
      (stdConicPoint d) (stdConicPoint e) (stdConicPoint f) := by
  unfold pascalConstraint lineIntersection lineThrough stdConicPoint stdConicInfinity
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

/-- Pascal's constraint when C = (1,0,-1) (point at infinity). -/
theorem pascal_std_conic_infinity_C (a b d e f : ℝ) :
    pascalConstraint (stdConicPoint a) (stdConicPoint b) stdConicInfinity
      (stdConicPoint d) (stdConicPoint e) (stdConicPoint f) := by
  unfold pascalConstraint lineIntersection lineThrough stdConicPoint stdConicInfinity
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

/-- Pascal's constraint when D = (1,0,-1) (point at infinity). -/
theorem pascal_std_conic_infinity_D (a b c e f : ℝ) :
    pascalConstraint (stdConicPoint a) (stdConicPoint b) (stdConicPoint c)
      stdConicInfinity (stdConicPoint e) (stdConicPoint f) := by
  unfold pascalConstraint lineIntersection lineThrough stdConicPoint stdConicInfinity
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

/-- Pascal's constraint when E = (1,0,-1) (point at infinity). -/
theorem pascal_std_conic_infinity_E (a b c d f : ℝ) :
    pascalConstraint (stdConicPoint a) (stdConicPoint b) (stdConicPoint c)
      (stdConicPoint d) stdConicInfinity (stdConicPoint f) := by
  unfold pascalConstraint lineIntersection lineThrough stdConicPoint stdConicInfinity
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

-- ============================================================
-- PART 16: Scale Invariance of Pascal Constraint
-- ============================================================

/-! The Pascal constraint is invariant under individual point scaling.
    Since `pascalConstraint` is defined via cross products and determinants,
    both of which are multilinear, scaling each point by a nonzero scalar
    doesn't change whether the constraint holds. -/

/-- Scaling the threeVectorMatrix rows by constants scales the determinant
    by their product. -/
theorem det_threeVectorMatrix_smul (α β γ : ℝ) (u v w : Fin 3 → ℝ) :
    (threeVectorMatrix (α • u) (β • v) (γ • w)).det =
    α * β * γ * (threeVectorMatrix u v w).det := by
  unfold threeVectorMatrix
  simp only [Matrix.det_fin_three, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Scale invariance**: The Pascal constraint is unchanged when each point
    is scaled by a nonzero scalar. This is because the cross products and
    determinant are multilinear, so the scalars factor out. -/
theorem pascalConstraint_smul
    {A B C D E F : ProjPoint}
    {k₁ k₂ k₃ k₄ k₅ k₆ : ℝ}
    (h1 : k₁ ≠ 0) (h2 : k₂ ≠ 0) (h3 : k₃ ≠ 0)
    (h4 : k₄ ≠ 0) (h5 : k₅ ≠ 0) (h6 : k₆ ≠ 0) :
    pascalConstraint (k₁ • A) (k₂ • B) (k₃ • C) (k₄ • D) (k₅ • E) (k₆ • F) ↔
    pascalConstraint A B C D E F := by
  unfold pascalConstraint lineIntersection lineThrough
  -- Pull scalars through cross products and collapse nested smul
  simp only [crossProduct_smul_left, crossProduct_smul_right, smul_smul]
  -- Now each Pascal point is (kᵢkⱼkₖkₗ) • original, so the det scales
  rw [det_threeVectorMatrix_smul]
  constructor
  · intro h
    have hprod : k₁ * k₂ * (k₄ * k₅) * (k₂ * k₃ * (k₅ * k₆)) *
      (k₃ * k₄ * (k₆ * k₁)) ≠ 0 := by
      apply mul_ne_zero; apply mul_ne_zero
      · exact mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero h4 h5)
      · exact mul_ne_zero (mul_ne_zero h2 h3) (mul_ne_zero h5 h6)
      · exact mul_ne_zero (mul_ne_zero h3 h4) (mul_ne_zero h6 h1)
    exact (mul_eq_zero.mp h).resolve_left hprod
  · intro h; rw [h, mul_zero]

-- ============================================================
-- Export main results
-- ============================================================

#check @pascal_hexagon_theorem
#check @pascalP
#check @pascalQ
#check @pascalR
#check @InscribedHexagon
#check @pointOnConic
#check @collinear
#check @pascalConstraint
#check @conic_implies_pascal_constraint
#check @pascal_std_conic_parametrized
#check @crossProduct_projTransform
#check @stdConic_det_factored
#check @pascalConstraint_projTransform
#check @stdConicPoint_covers
#check @stdConic_infinity_char
#check @crossProduct_smul_left
#check @crossProduct_smul_right
#check @pascal_std_conic_infinity_F
#check @pascal_std_conic_infinity_A
#check @det_threeVectorMatrix_smul
#check @pascalConstraint_smul

-- ============================================================
-- PART 17: Assembly — Pascal's Theorem for Standard Conic
-- ============================================================

/-! These theorems assemble the parametric proof, coverage theorem, infinity
    cases, and scale invariance to prove Pascal's theorem for the standard
    conic directly (no axiom needed). -/

/-- **Classification**: Every valid point on stdConic is either a scaled
    parametric point or a scaled infinity point. -/
theorem stdConic_point_classification (p : ProjPoint) (hp : pointOnConic p stdConic)
    (hv : ProjPoint.valid p) :
    (∃ t k, k ≠ 0 ∧ ∀ i, p i = k * stdConicPoint t i) ∨
    (∃ k, k ≠ 0 ∧ ∀ i, p i = k * stdConicInfinity i) := by
  by_cases h02 : p 0 + p 2 = 0
  · right
    have hp1 := stdConic_infinity_char p hp h02
    have hp2 : p 2 = -(p 0) := by linarith
    have hp0_ne : p 0 ≠ 0 := by
      intro h0
      apply hv
      ext i; fin_cases i <;> simp_all
    exact ⟨p 0, hp0_ne, fun i => by fin_cases i <;>
      simp only [stdConicInfinity, Fin.isValue, mul_one, mul_zero, mul_neg] <;>
      linarith⟩
  · left; exact stdConicPoint_covers p hp h02

/-- **Pascal for stdConic (all finite vertices)**: When all 6 points have
    p₀+p₂ ≠ 0, they decompose as scaled parametric points and Pascal follows. -/
theorem pascal_stdConic_allFinite (A B C D E F : ProjPoint)
    (hA : pointOnConic A stdConic) (hA0 : A 0 + A 2 ≠ 0)
    (hB : pointOnConic B stdConic) (hB0 : B 0 + B 2 ≠ 0)
    (hC : pointOnConic C stdConic) (hC0 : C 0 + C 2 ≠ 0)
    (hD : pointOnConic D stdConic) (hD0 : D 0 + D 2 ≠ 0)
    (hE : pointOnConic E stdConic) (hE0 : E 0 + E 2 ≠ 0)
    (hF : pointOnConic F stdConic) (hF0 : F 0 + F 2 ≠ 0) :
    pascalConstraint A B C D E F := by
  obtain ⟨a, ka, hka, ha⟩ := stdConicPoint_covers A hA hA0
  obtain ⟨b, kb, hkb, hb⟩ := stdConicPoint_covers B hB hB0
  obtain ⟨c, kc, hkc, hc⟩ := stdConicPoint_covers C hC hC0
  obtain ⟨d, kd, hkd, hd⟩ := stdConicPoint_covers D hD hD0
  obtain ⟨e, ke, hke, he⟩ := stdConicPoint_covers E hE hE0
  obtain ⟨f, kf, hkf, hf⟩ := stdConicPoint_covers F hF hF0
  have hA_eq : A = ka • stdConicPoint a := funext ha
  have hB_eq : B = kb • stdConicPoint b := funext hb
  have hC_eq : C = kc • stdConicPoint c := funext hc
  have hD_eq : D = kd • stdConicPoint d := funext hd
  have hE_eq : E = ke • stdConicPoint e := funext he
  have hF_eq : F = kf • stdConicPoint f := funext hf
  rw [hA_eq, hB_eq, hC_eq, hD_eq, hE_eq, hF_eq]
  exact (pascalConstraint_smul hka hkb hkc hkd hke hkf).mpr
    (pascal_std_conic_parametrized a b c d e f)

-- ============================================================
-- PART 18: Coincident Vertex Lemmas
-- ============================================================

/-! When two vertices of the hexagon coincide (are projectively equal), the Pascal
    constraint holds by algebraic cancellation. These are pure polynomial identities,
    independent of the conic — they hold for ANY six projective points with repeated positions.

    Mathematical insight:
    - **Opposite pairs (A=D, B=E, C=F)**: Two of the three Pascal points become
      proportional to the shared vertex, forcing det(P,Q,R) = 0 by row dependence.
    - **Adjacent pairs (A=B, B=C, ...)**: The shared vertex appears as both arguments
      of a lineThrough, giving lineThrough V V = V×V = 0, so one Pascal point is 0.
    - **Skip-one pairs (A=C, B=D, ...)**: More subtle cancellation, still a ring identity.

    All 15 lemmas are proved by `ring` after unfolding the cross-product/determinant
    definitions. These cover all C(6,2) = 15 possible pairs of coincident vertices. -/

-- Opposite pairs: P∝A and R∝A when A=D; Q∝B and P∝B when B=E; Q∝C and R∝C when C=F
private theorem pascalConstraint_A_eq_D (A B C E F : ProjPoint) :
    pascalConstraint A B C A E F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_B_eq_E (A B C D F : ProjPoint) :
    pascalConstraint A B C D B F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_C_eq_F (A B C D E : ProjPoint) :
    pascalConstraint A B C D E C := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

-- Adjacent pairs: lineThrough V V = V×V = 0, so one Pascal point is zero
private theorem pascalConstraint_A_eq_B (A C D E F : ProjPoint) :
    pascalConstraint A A C D E F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_B_eq_C (A B D E F : ProjPoint) :
    pascalConstraint A B B D E F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_C_eq_D (A B C E F : ProjPoint) :
    pascalConstraint A B C C E F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_D_eq_E (A B C D F : ProjPoint) :
    pascalConstraint A B C D D F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_E_eq_F (A B C D E : ProjPoint) :
    pascalConstraint A B C D E E := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_F_eq_A (A B C D E : ProjPoint) :
    pascalConstraint A B C D E A := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

-- Skip-one pairs: more subtle cancellation (involving two Pascal points)
private theorem pascalConstraint_A_eq_C (A B D E F : ProjPoint) :
    pascalConstraint A B A D E F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_B_eq_D (A B C E F : ProjPoint) :
    pascalConstraint A B C B E F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_C_eq_E (A B C D F : ProjPoint) :
    pascalConstraint A B C D C F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_D_eq_F (A B C D E : ProjPoint) :
    pascalConstraint A B C D E D := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_E_eq_A (A B C D F : ProjPoint) :
    pascalConstraint A B C D A F := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

private theorem pascalConstraint_F_eq_B (A B C D E : ProjPoint) :
    pascalConstraint A B C D E B := by
  unfold pascalConstraint lineIntersection lineThrough
  simp only [threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply, cross_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
             Nat.reduceAdd, Fin.reduceFinMk]
  ring

-- ============================================================
-- PART 19: Pascal's Theorem for Standard Conic (All Cases)
-- ============================================================

-- Heartbeat budget for the case-dispatch section
set_option maxHeartbeats 800000

/-! **Pascal's theorem for stdConic** assembles all the building blocks:
    - `pascal_std_conic_parametrized`: all 6 vertices are finite parametric points
    - `pascal_std_conic_infinity_{A..F}`: exactly one vertex is at infinity
    - Coincident vertex lemmas: ≥2 vertices at infinity (they coincide on stdConic)

    The proof strategy:
    1. Classify each vertex as finite (∃ t, V = λ·stdConicPoint t) or at infinity (V = λ·stdConicInfinity)
    2. Normalize all 6 vertices by removing the scale factors via `pascalConstraint_smul`
    3. For the normalized form: apply the appropriate lemma from the list above -/

/-- **Normalized Pascal for stdConic**: proves Pascal when each vertex is EXACTLY
    `stdConicPoint t` or `stdConicInfinity` (no scalar factor). This is the key
    dispatch lemma that routes to the appropriate proved case. -/
private theorem pascal_std_conic_normalized (A B C D E F : ProjPoint)
    (hA : (∃ t : ℝ, A = stdConicPoint t) ∨ A = stdConicInfinity)
    (hB : (∃ t : ℝ, B = stdConicPoint t) ∨ B = stdConicInfinity)
    (hC : (∃ t : ℝ, C = stdConicPoint t) ∨ C = stdConicInfinity)
    (hD : (∃ t : ℝ, D = stdConicPoint t) ∨ D = stdConicInfinity)
    (hE : (∃ t : ℝ, E = stdConicPoint t) ∨ E = stdConicInfinity)
    (hF : (∃ t : ℝ, F = stdConicPoint t) ∨ F = stdConicInfinity) :
    pascalConstraint A B C D E F := by
  -- Nested case analysis with early stopping: once two ∞ vertices are detected, apply
  -- the coincident-vertex lemma immediately without recursing further. Each of the 22
  -- leaf cases has exactly one applicable lemma (no backtracking search needed).
  rcases hA with ⟨ta, rfl⟩ | rfl
  · -- A = stdConicPoint ta (finite)
    rcases hB with ⟨tb, rfl⟩ | rfl
    · -- A, B finite
      rcases hC with ⟨tc, rfl⟩ | rfl
      · -- A, B, C finite
        rcases hD with ⟨td, rfl⟩ | rfl
        · -- A, B, C, D finite
          rcases hE with ⟨te, rfl⟩ | rfl
          · -- A..E finite; check F
            rcases hF with ⟨tf, rfl⟩ | rfl
            · exact pascal_std_conic_parametrized ta tb tc td te tf  -- all finite
            · exact pascal_std_conic_infinity_F ta tb tc td te        -- F = ∞
          · -- E = ∞; check F
            rcases hF with ⟨tf, rfl⟩ | rfl
            · exact pascal_std_conic_infinity_E ta tb tc td tf        -- E = ∞, others fin
            · exact pascalConstraint_E_eq_F _ _ _ _ _                -- E = F = ∞
        · -- D = ∞; check E
          rcases hE with ⟨te, rfl⟩ | rfl
          · rcases hF with ⟨tf, rfl⟩ | rfl
            · exact pascal_std_conic_infinity_D ta tb tc te tf        -- D = ∞, others fin
            · exact pascalConstraint_D_eq_F _ _ _ _ _                -- D = F = ∞
          · exact pascalConstraint_D_eq_E _ _ _ _ _                  -- D = E = ∞ (F arb)
      · -- C = ∞; check D
        rcases hD with ⟨td, rfl⟩ | rfl
        · rcases hE with ⟨te, rfl⟩ | rfl
          · rcases hF with ⟨tf, rfl⟩ | rfl
            · exact pascal_std_conic_infinity_C ta tb td te tf        -- C = ∞, others fin
            · exact pascalConstraint_C_eq_F _ _ _ _ _                -- C = F = ∞
          · exact pascalConstraint_C_eq_E _ _ _ _ _                  -- C = E = ∞ (F arb)
        · exact pascalConstraint_C_eq_D _ _ _ _ _                    -- C = D = ∞ (E,F arb)
    · -- B = ∞; check C
      rcases hC with ⟨tc, rfl⟩ | rfl
      · rcases hD with ⟨td, rfl⟩ | rfl
        · rcases hE with ⟨te, rfl⟩ | rfl
          · rcases hF with ⟨tf, rfl⟩ | rfl
            · exact pascal_std_conic_infinity_B ta tc td te tf        -- B = ∞, others fin
            · exact pascalConstraint_F_eq_B _ _ _ _ _                -- B = F = ∞
          · exact pascalConstraint_B_eq_E _ _ _ _ _                  -- B = E = ∞ (F arb)
        · exact pascalConstraint_B_eq_D _ _ _ _ _                    -- B = D = ∞ (E,F arb)
      · exact pascalConstraint_B_eq_C _ _ _ _ _                      -- B = C = ∞ (D,E,F arb)
  · -- A = ∞; check B
    rcases hB with ⟨tb, rfl⟩ | rfl
    · -- A = ∞, B finite; check C
      rcases hC with ⟨tc, rfl⟩ | rfl
      · rcases hD with ⟨td, rfl⟩ | rfl
        · rcases hE with ⟨te, rfl⟩ | rfl
          · rcases hF with ⟨tf, rfl⟩ | rfl
            · exact pascal_std_conic_infinity_A tb tc td te tf        -- A = ∞, others fin
            · exact pascalConstraint_F_eq_A _ _ _ _ _                -- A = F = ∞
          · exact pascalConstraint_E_eq_A _ _ _ _ _                  -- A = E = ∞ (F arb)
        · exact pascalConstraint_A_eq_D _ _ _ _ _                    -- A = D = ∞ (E,F arb)
      · exact pascalConstraint_A_eq_C _ _ _ _ _                      -- A = C = ∞ (D,E,F arb)
    · exact pascalConstraint_A_eq_B _ _ _ _ _                        -- A = B = ∞ (C..F arb)

/-- **Pascal's theorem for the standard conic** (all valid hexagons).

    For ANY 6 valid points on `stdConic = {x₀²+x₁²=x₂²}`, the Pascal constraint holds.
    This includes degenerate hexagons with repeated vertices.

    Proof sketch:
    1. Classify each vertex via `stdConic_point_classification`: either finite (∃ t,
       V = λ·stdConicPoint t) or at infinity (V = λ·stdConicInfinity).
    2. Normalize by `pascalConstraint_smul`: scale factors λ don't affect the constraint.
    3. Apply `pascal_std_conic_normalized` to dispatch to the 22 proved cases. -/
theorem pascal_std_conic (A B C D E F : ProjPoint)
    (hA : pointOnConic A stdConic) (hAv : ProjPoint.valid A)
    (hB : pointOnConic B stdConic) (hBv : ProjPoint.valid B)
    (hC : pointOnConic C stdConic) (hCv : ProjPoint.valid C)
    (hD : pointOnConic D stdConic) (hDv : ProjPoint.valid D)
    (hE : pointOnConic E stdConic) (hEv : ProjPoint.valid E)
    (hF : pointOnConic F stdConic) (hFv : ProjPoint.valid F) :
    pascalConstraint A B C D E F := by
  -- Step 1: Classify each vertex
  rcases stdConic_point_classification A hA hAv with ⟨ta, ka, hka, haEq⟩ | ⟨ka, hka, haEq⟩ <;>
  rcases stdConic_point_classification B hB hBv with ⟨tb, kb, hkb, hbEq⟩ | ⟨kb, hkb, hbEq⟩ <;>
  rcases stdConic_point_classification C hC hCv with ⟨tc, kc, hkc, hcEq⟩ | ⟨kc, hkc, hcEq⟩ <;>
  rcases stdConic_point_classification D hD hDv with ⟨td, kd, hkd, hdEq⟩ | ⟨kd, hkd, hdEq⟩ <;>
  rcases stdConic_point_classification E hE hEv with ⟨te, ke, hke, heEq⟩ | ⟨ke, hke, heEq⟩ <;>
  rcases stdConic_point_classification F hF hFv with ⟨tf, kf, hkf, hfEq⟩ | ⟨kf, hkf, hfEq⟩
  -- Step 2 & 3: Rewrite each vertex to k·(normalized form), apply smul invariance,
  -- then dispatch to pascal_std_conic_normalized.
  -- In each of the 64 cases, haEq (and hbEq, ...) gives ∀ i, V i = k * form i,
  -- so V = k • form by funext. After rewriting, pascalConstraint_smul removes the k.
  all_goals (
    rw [show A = ka • _ from funext haEq, show B = kb • _ from funext hbEq,
        show C = kc • _ from funext hcEq, show D = kd • _ from funext hdEq,
        show E = ke • _ from funext heEq, show F = kf • _ from funext hfEq]
    apply (pascalConstraint_smul hka hkb hkc hkd hke hkf).mpr
    apply pascal_std_conic_normalized
    all_goals first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr rfl)

-- ============================================================
-- PART 20: Toward Eliminating the Axiom
-- ============================================================

/-! ## Roadmap to Eliminating `conic_implies_pascal_constraint`

With `pascal_std_conic` proved, the remaining work is:

**Step A — Sylvester's Law (the key missing piece):**
Any non-degenerate real symmetric conic C with real points has signature (2,1) or (1,2),
hence is congruent to stdConic = diag(1,1,-1) via some invertible matrix M:
    ∃ (M : Matrix (Fin 3) (Fin 3) ℝ), M.det ≠ 0 ∧ M.transpose * C * M = stdConic

Mathlib4 has: `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` for real
nondegenerate quadratic forms, and `Matrix.IsHermitian.spectral_theorem` for the
spectral decomposition. Building Sylvester for our 3×3 case requires ~50-100 lines
using Mathlib's quadratic form machinery.

**Step B — Full assembly:**
Given `conic_implies_pascal_constraint_for_std_conic` (trivial) and Sylvester's law,
the proof of `conic_implies_pascal_constraint C hex` goes:
1. By Sylvester, find M with `M.det ≠ 0` and `M^T·C·M = stdConic`
   (or equivalently: C = (M^{-T})·stdConic·(M^{-1}))
2. The transformed hexagon `M·hex` is inscribed on stdConic
   (since pointOnConic V C ↔ pointOnConic (M·V) stdConic by the change-of-variables formula)
3. By `pascal_std_conic`, the transformed hexagon satisfies Pascal's constraint
4. By `pascalConstraint_projTransform M (det_ne_zero)`, the original hexagon does too

The axiom `conic_implies_pascal_constraint` can then be replaced by a theorem.
See `proof_sketch_conic_implies_pascal` below. -/

-- ============================================================
-- PART 20a: Mathlib QuadraticForm Bridge (for Sylvester's Law)
-- ============================================================

/-! ## Connecting to Mathlib's QuadraticForm machinery

The key helper `mathlibQF_separatingLeft` shows that for a non-degenerate symmetric
conic matrix C, the quadratic form `Matrix.toQuadraticMap' C` has a separating left
associated bilinear form — the key hypothesis for Sylvester's theorem
(`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`).

These lemmas support the proof plan in `proof_sketch_conic_implies_pascal` below. -/

/-- Our `conicQuadraticForm C p` equals the standard matrix bilinear form `p ⬝ᵥ (C *ᵥ p)`.
    Both compute `Σᵢⱼ Cᵢⱼ pᵢ pⱼ`. -/
private lemma conicQF_eq_dotProduct (C : Conic) (p : Fin 3 → ℝ) :
    conicQuadraticForm C p = p ⬝ᵥ (C *ᵥ p) := by
  simp only [conicQuadraticForm, dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- Mathlib's `Matrix.toQuadraticMap' C p` also equals `p ⬝ᵥ (C *ᵥ p)`.
    The `Matrix.toQuadraticMap'` definition is `LinearMap.BilinMap.toQuadraticMap (toLinearMap₂' ℝ C)`,
    which applies the bilinear map to `(p, p)`. -/
private lemma mathlibQF_eq_dotProduct (C : Conic) (p : Fin 3 → ℝ) :
    Matrix.toQuadraticMap' C p = p ⬝ᵥ (C *ᵥ p) := by
  simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
             Matrix.toLinearMap₂'_apply']

/-- Our `conicQuadraticForm` agrees with Mathlib's `Matrix.toQuadraticMap'` pointwise.
    Key connection for the Sylvester proof path. -/
private lemma conicQF_eq_mathlibQF (C : Conic) (p : Fin 3 → ℝ) :
    conicQuadraticForm C p = Matrix.toQuadraticMap' C p :=
  (conicQF_eq_dotProduct C p).trans (mathlibQF_eq_dotProduct C p).symm

/-- For a non-degenerate symmetric conic C, the associated bilinear form of
    `Matrix.toQuadraticMap' C` is separating on the left.

    This is the key hypothesis for `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`
    (Sylvester's law). The proof chain:
    1. Symmetry of C → `Matrix.toLinearMap₂' ℝ C` is a symmetric bilinear form
    2. `QuadraticMap.associated_left_inverse` → `associated Q = Matrix.toLinearMap₂' ℝ C`
    3. `C.det ≠ 0` → `Matrix.Nondegenerate C` → `(Matrix.toLinearMap₂' ℝ C).SeparatingLeft`
    4. Therefore `(associated Q).SeparatingLeft`. -/
private lemma mathlibQF_separatingLeft (C : Conic) (hC_sym : C.symmetric)
    (hC_nd : Conic.nondegenerate C) :
    (associated (R := ℝ) (Matrix.toQuadraticMap' C)).SeparatingLeft := by
  -- Step 1: Show associated Q = Matrix.toLinearMap₂' ℝ C using symmetry of C
  have h_assoc : associated (R := ℝ) (Matrix.toQuadraticMap' C) = Matrix.toLinearMap₂' ℝ C := by
    unfold Matrix.toQuadraticMap'
    exact QuadraticMap.associated_left_inverse (fun x y => by
      -- Prove: (Matrix.toLinearMap₂' ℝ C) x y = (Matrix.toLinearMap₂' ℝ C) y x
      -- i.e., x ⬝ᵥ (C *ᵥ y) = y ⬝ᵥ (C *ᵥ x), using symmetry of C
      simp only [Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec]
      simp_rw [Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      -- After swap: x l * (C l k * y k) = y k * (C k l * x l)
      -- Using hC_sym l k : C l k = C k l
      rw [hC_sym l k]; ring)
  -- Step 2: Apply Matrix.Nondegenerate.toLinearMap₂'
  rw [h_assoc]
  exact (Matrix.nondegenerate_of_det_ne_zero hC_nd).toLinearMap₂'

/-- **Invertible matrices preserve validity** (map nonzero vectors to nonzero vectors).
    If det(M) ≠ 0 and v ≠ 0, then M·v ≠ 0.
    Proof: if M·v = 0, then (adj(M)·M)·v = adj(M)·(M·v) = 0 = det(M)·v, so v = 0. -/
private lemma projTransform_valid_of_det_ne_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M.det ≠ 0) {v : Fin 3 → ℝ} (hv : ProjPoint.valid v) :
    ProjPoint.valid (projTransform M v) := by
  unfold ProjPoint.valid projTransform
  intro h
  apply hv
  have h0 : (M.adjugate * M) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h0
  exact (smul_eq_zero.mp h0).resolve_left hM

/-- **Sylvester reduction to the standard conic** — the sole remaining gap in the
    elimination of `conic_implies_pascal_constraint` for non-degenerate symmetric conics.

    A non-degenerate symmetric real conic `C` carrying a real point (`p₀ ≠ 0` with
    `pointOnConic p₀ C`) is *indefinite* of signature `(2,1)`, hence projectively
    equivalent to `stdConic = diag(1,1,-1)`: there is an invertible `M` with
    `pointOnConic p C ↔ pointOnConic (M·p) stdConic` for every `p`.

    The real-point hypothesis is **essential and not removable**: a *definite*
    non-degenerate `C` (signature `(3,0)`/`(0,3)`) has only the trivial zero `p = 0`,
    while `stdConic` has a full cone of real zeros, so no such `M` can exist. The
    inscribed hexagon supplies the witness `p₀ := hex.A`, ruling out the definite case —
    this is why the inline existential in `proof_sketch_conic_implies_pascal` was not
    provable from `hC_sym`/`hC_nd` alone.

    Proof plan (Sylvester's law of inertia; all tools in
    `Mathlib.LinearAlgebra.QuadraticForm.Real`):
    1. `mathlibQF_separatingLeft` gives that the associated bilinear form of
       `Matrix.toQuadraticMap' C` is separating-left — the hypothesis for
       `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`, yielding weights
       `w : Fin 3 → ℝ` (`w i ∈ {1,-1}`) and an isometry
       `φ : (toQuadraticMap' C).IsometryEquiv (weightedSumSquares ℝ w)`.
    2. Extract `M₁ := LinearMap.toMatrix' φ.toLinearEquiv.toLinearMap` (invertible,
       `M₁ *ᵥ p = φ p`).
    3. The real zero `p₀` forces `w` indefinite (`conicQF_eq_mathlibQF` makes
       `(weightedSumSquares ℝ w)(φ p₀) = 0` with `φ p₀ ≠ 0`), leaving the 6 indefinite
       weight patterns; each admits a fixed permutation/sign correction `M₂` carrying
       `weightedSumSquares ℝ w` to `stdConic`. Set `M := M₂ * M₁`.
    4. Chase the iff through `conicQF_eq_mathlibQF`, the isometry `φ`, and the `M₂`
       correction (`mulVec` associativity). -/
theorem sylvester_stdConic_of_isotropic (C : Conic)
    (hC_sym : C.symmetric) (hC_nd : Conic.nondegenerate C)
    (p₀ : ProjPoint) (hp₀v : ProjPoint.valid p₀) (hp₀ : pointOnConic p₀ C) :
    ∃ (M : Matrix (Fin 3) (Fin 3) ℝ), M.det ≠ 0 ∧
      ∀ (p : ProjPoint), pointOnConic p C ↔
        pointOnConic (projTransform M p) stdConic := by
  sorry

/-- **Proof sketch**: The full proof of `conic_implies_pascal_constraint`, for the case
    where C is a symmetric non-degenerate conic. The remaining gap — extracting an
    explicit invertible matrix from Mathlib's `IsometryEquiv` — is now isolated in the
    standalone lemma `sylvester_stdConic_of_isotropic` (the only `sorry` on this path);
    everything else here is complete.

    **Why hC_sym and hC_nd are needed:**
    - `hC_sym`: Without symmetry, the quadratic form's zero set is the same as its symmetrization
      `(C + Cᵀ)/2`, so WLOG C is symmetric. But the proof of Sylvester requires a symmetric matrix.
    - `hC_nd`: Degenerate conics (pairs of lines, single points, empty) need separate treatment;
      for non-degenerate conics, Sylvester gives a projective equivalence to `stdConic`.

    **For the full elimination of `conic_implies_pascal_constraint`**, two additional steps remain:
    1. Handle asymmetric C: replace with symmetrized `(C + Cᵀ)/2` (same zero set).
    2. Handle degenerate C: use a Pappus-type argument for pairs of lines.

    All other steps (projective invariance, Pascal for stdConic) are proved above. -/
theorem proof_sketch_conic_implies_pascal (C : Conic)
    (hC_sym : C.symmetric) (hC_nd : Conic.nondegenerate C)
    (hex : InscribedHexagon C) :
    pascalConstraint hex.A hex.B hex.C' hex.D hex.E hex.F := by
  -- The sole remaining gap, isolated as a clean (and *true*) standalone lemma. The
  -- inscribed hexagon supplies the isotropic witness `hex.A`, which is exactly what
  -- makes the existential provable (it rules out the definite case). See
  -- `sylvester_stdConic_of_isotropic` for the full Sylvester-law proof plan.
  obtain ⟨M, hM_det, hM_eq⟩ :=
    sylvester_stdConic_of_isotropic C hC_sym hC_nd hex.A hex.hAvalid hex.hA
  -- Step C: The M-transformed hexagon vertices lie on stdConic
  have hMA : pointOnConic (projTransform M hex.A) stdConic := (hM_eq hex.A).mp hex.hA
  have hMB : pointOnConic (projTransform M hex.B) stdConic := (hM_eq hex.B).mp hex.hB
  have hMC : pointOnConic (projTransform M hex.C') stdConic := (hM_eq hex.C').mp hex.hC
  have hMD : pointOnConic (projTransform M hex.D) stdConic := (hM_eq hex.D).mp hex.hD
  have hME : pointOnConic (projTransform M hex.E) stdConic := (hM_eq hex.E).mp hex.hE
  have hMF : pointOnConic (projTransform M hex.F) stdConic := (hM_eq hex.F).mp hex.hF
  -- Step D: M·V is valid (nonzero) since M is invertible and V is valid
  -- (Proved by projTransform_valid_of_det_ne_zero)
  have hMAv : ProjPoint.valid (projTransform M hex.A) :=
    projTransform_valid_of_det_ne_zero hM_det hex.hAvalid
  have hMBv : ProjPoint.valid (projTransform M hex.B) :=
    projTransform_valid_of_det_ne_zero hM_det hex.hBvalid
  have hMCv : ProjPoint.valid (projTransform M hex.C') :=
    projTransform_valid_of_det_ne_zero hM_det hex.hCvalid
  have hMDv : ProjPoint.valid (projTransform M hex.D) :=
    projTransform_valid_of_det_ne_zero hM_det hex.hDvalid
  have hMEv : ProjPoint.valid (projTransform M hex.E) :=
    projTransform_valid_of_det_ne_zero hM_det hex.hEvalid
  have hMFv : ProjPoint.valid (projTransform M hex.F) :=
    projTransform_valid_of_det_ne_zero hM_det hex.hFvalid
  -- Step E: Apply pascal_std_conic to the transformed hexagon
  have hStd := pascal_std_conic (projTransform M hex.A) (projTransform M hex.B)
    (projTransform M hex.C') (projTransform M hex.D) (projTransform M hex.E) (projTransform M hex.F)
    hMA hMAv hMB hMBv hMC hMCv hMD hMDv hME hMEv hMF hMFv
  -- Step F: Pull back via projective invariance
  exact (pascalConstraint_projTransform M hM_det hex.A hex.B hex.C' hex.D hex.E hex.F).mp hStd

#check @pascal_std_conic
#check @pascal_std_conic_normalized
#check @proof_sketch_conic_implies_pascal
