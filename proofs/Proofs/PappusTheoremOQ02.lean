import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-
# Pappus's Hexagon Theorem via Algebraic Framework

## Open Question (OQ-02)
Can Pappus's Hexagon Theorem be proved in Lean 4 using the same algebraic
cross-product framework as the Desargues theorem (OQ-01)?

## Answer: YES — fully proved over any CommRing K (0 sorries)

Pappus's Theorem states: Given two sets of collinear points A, B, C on line L₁
and A', B', C' on line L₂ (in a projective plane over K), the three cross-join
intersection points:
  P = line(A, B') ∩ line(A', B)
  Q = line(A, C') ∩ line(A', C)
  R = line(B, C') ∩ line(B', C)
are collinear.

This is a fundamental result with deep connections to:
- Commutative algebra: Pappus holds iff the coordinatizing ring is commutative
- Projective geometry: Pappus implies Desargues (classical result)
- Group theory: Commutativity of coordinate multiplication

## Proof Strategy

Using the Lagrange cross-product identity (same as Desargues OQ-01):
  cross(cross(a,b), cross(c,d)) = det(a,b,d)·c − det(a,b,c)·d

We express:
  P = d1·A' − d2·B   where d1 = det(A,B',B), d2 = det(A,B',A')
  Q = d3·A' − d4·C   where d3 = det(A,C',C), d4 = det(A,C',A')
  R = d5·B' − d6·C   where d5 = det(B,C',C), d6 = det(B,C',B')

**Step 1 (Multilinear expansion, proved by `ring` at degree 6)**:
det(d1·A'-d2·B, d3·A'-d4·C, d5·B'-d6·C) =
  −d1·d4·d5·det(A',C,B') − d2·d3·d5·det(B,A',B')
  + d2·d3·d6·det(B,A',C) + d2·d4·d5·det(B,C,B')
(with d1,...,d6 as ABSTRACT ring elements — degree 6 identity, feasible for `ring`)

**Step 2 (Core Pappus identity, proved)**:
The 4-term expression = f·det(A,B,C) + g·det(A',B',C') (degree-9 coefficients)
This is the key algebraic identity requiring `linear_combination` with Groebner coefficients.

## Status
- [x] Lagrange identity (reproduced from Desargues OQ-01)
- [x] pappus_det_multilinear: Clean degree-6 ring identity (abstract d_i's)
- [x] pappus_det_expansion: Instantiate with actual determinant values
- [x] desargues_from_ring_commutativity: Reproof of Desargues using this framework
- [x] Numerical verification: 3 concrete configurations verified by ring
- [x] pappus_K: Main theorem (0 sorries — core identity proved via CAS-computed coefficients)
- [x] pappus_Q, pappus_Z, pappus_Fp: Corollaries for ℚ, ℤ, 𝔽_p
-/

namespace PappusTheoremOQ02

open Matrix

variable {K : Type*} [CommRing K]

-- ============================================================
-- PART 1: Cross Product Infrastructure (Self-Contained)
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

/-- 3×3 matrix with three vectors as rows over K. -/
def threeVecMat (u v w : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j =>
    match i with
    | 0 => u j
    | 1 => v j
    | 2 => w j

/-- Explicit determinant expansion. -/
theorem threeVecMat_det_explicit (u v w : Fin 3 → K) :
    (threeVecMat u v w).det =
      u 0 * (v 1 * w 2 - v 2 * w 1) -
      u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0) := by
  simp only [threeVecMat, Matrix.det_fin_three, Matrix.of_apply]
  ring

/-- Collinearity via vanishing determinant. -/
def collinear_K (p q r : Fin 3 → K) : Prop :=
  (threeVecMat p q r).det = 0

-- ============================================================
-- PART 2: Lagrange Cross Product Identity
-- ============================================================

set_option maxHeartbeats 400000000 in
/-- **Lagrange Cross Product Identity**:
    cross(cross(a,b), cross(c,d)) = det(a,b,d)·c − det(a,b,c)·d
    This expresses projective line intersections as linear combinations. -/
theorem lagrange_cross_K (a b c d : Fin 3 → K) :
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

-- ============================================================
-- PART 3: Multilinear Expansion (Degree-6 Identity)
-- ============================================================

/-
## The Key Multilinear Expansion

The determinant det(d1·A' - d2·B, d3·A' - d4·C, d5·B' - d6·C)
expands by multilinearity of det. Each row is a sum of two terms;
expanding gives 8 combinations, but 4 vanish (repeated rows):
  det(A',A',?) = 0  (rows 1,2 both choose A')
  det(A',?,C) combined with (?,C,C): det(_,C,C) = 0  (rows 2,3 both choose C)

Remaining 4 non-zero terms:
  (A', C, B') → coeff −d1·d4·d5
  (B, A', B') → coeff −d2·d3·d5
  (B, A', C)  → coeff +d2·d3·d6
  (B, C, B')  → coeff +d2·d4·d5

**Key advantage of this lemma**: d1,...,d6 are ABSTRACT ring elements.
After simp [threeVecMat_det_explicit], the identity is degree 6 in
{d1,...,d6, A'₀,...,C₂} — feasible for `ring`.
-/

set_option maxHeartbeats 800000000 in
/-- **Multilinear Expansion of det(P,Q,R)**

    With d1,...,d6 as abstract ring elements and A', B, C, B' as vectors,
    the determinant of (d1·A'-d2·B, d3·A'-d4·C, d5·B'-d6·C) reduces to
    4 non-vanishing terms.

    Proof: degree-6 polynomial identity in 6+15=21 variables, verified by ring. -/
theorem pappus_det_multilinear (d1 d2 d3 d4 d5 d6 : K)
    (A' B C B' : Fin 3 → K) :
    (threeVecMat
        (fun i => d1 * A' i - d2 * B i)
        (fun i => d3 * A' i - d4 * C i)
        (fun i => d5 * B' i - d6 * C i)).det =
    - d1 * d4 * d5 * (threeVecMat A' C B').det
    - d2 * d3 * d5 * (threeVecMat B A' B').det
    + d2 * d3 * d6 * (threeVecMat B A' C).det
    + d2 * d4 * d5 * (threeVecMat B C B').det := by
  simp only [threeVecMat_det_explicit]
  ring

-- ============================================================
-- PART 4: The Pappus Core Identity
-- ============================================================

/-
## The Core Algebraic Identity

The 4-term expression lies in the ideal generated by det(A,B,C) and det(A',B',C').

Specifically:
  −d1·d4·d5·det(A',C,B') − d2·d3·d5·det(B,A',B') + d2·d3·d6·det(B,A',C)
  + d2·d4·d5·det(B,C,B')
  = f(A,B,C,A',B',C') · det(A,B,C) + g(A,B,C,A',B',C') · det(A',B',C')

where f, g are degree-9 polynomials in the 18 coordinate variables.

This is verifiable by `linear_combination (deg 9 expr)·hABC + (deg 9 expr)·hA'B'C'`
with the coefficients computed from a Groebner basis computation.
(The identity holds by the theory of commutative algebra over any CommRing K.)
-/

-- Need high heartbeat budget for the degree-12 ring verification in linear_combination
set_option maxHeartbeats 4000000000 in
/-- **The Pappus Core Identity**

    The 4-term multilinear expansion of det(P,Q,R) vanishes when both
    det(A,B,C) = 0 and det(A',B',C') = 0.

    Proof: `linear_combination` with degree-9 Groebner basis coefficients.
    These coefficients can be computed symbolically and verified by `ring`.
    Status: proved (CAS-computed degree-9 Groebner coefficients, verified by ring). -/
lemma pappus_core_identity (A B C A' B' C' : Fin 3 → K)
    (hABC : (threeVecMat A B C).det = 0)
    (hA'B'C' : (threeVecMat A' B' C').det = 0) :
    - (threeVecMat A B' B).det * (threeVecMat A C' A').det * (threeVecMat B C' C).det *
        (threeVecMat A' C B').det
    - (threeVecMat A B' A').det * (threeVecMat A C' C).det * (threeVecMat B C' C).det *
        (threeVecMat B A' B').det
    + (threeVecMat A B' A').det * (threeVecMat A C' C).det * (threeVecMat B C' B').det *
        (threeVecMat B A' C).det
    + (threeVecMat A B' A').det * (threeVecMat A C' A').det * (threeVecMat B C' C).det *
        (threeVecMat B C B').det = 0 := by
  -- Expand all determinants to raw coordinate polynomials (including hypotheses)
  simp only [threeVecMat_det_explicit] at *
  -- The goal becomes: degree-12 polynomial = 0, with two degree-3 hypotheses.
  -- CAS-computed decomposition: LHS = f·det(A,B,C) + g·det(A',B',C')
  -- where f, g are degree-9 polynomials (174 and 234 terms respectively).
  -- Computed via sympy.reduced() with grevlex ordering over ℤ[18 variables].
  linear_combination
    ((A 0)*(A' 0)^2*(B 2)*(B' 1)^2*(C 1)*(C' 2)^2 - (A 0)*(A' 0)^2*(B 2)*(B' 1)^2*(C 2)*(C' 1)*(C' 2) + (A 0)*(A' 0)^2*(B 2)*(B' 1)*(B' 2)*(C 2)*(C' 1)^2 - (A 0)*(A' 0)^2*(B 2)*(B' 2)^2*(C 1)*(C' 1)^2 - (A 0)*(A' 0)*(A' 1)*(B 1)*(B' 0)*(B' 2)*(C 1)*(C' 2)^2 + (A 0)*(A' 0)*(A' 1)*(B 1)*(B' 0)*(B' 2)*(C 2)*(C' 1)*(C' 2) + (A 0)*(A' 0)*(A' 1)*(B 1)*(B' 1)*(B' 2)*(C 0)*(C' 2)^2 - (A 0)*(A' 0)*(A' 1)*(B 1)*(B' 1)*(B' 2)*(C 2)*(C' 0)*(C' 2) - (A 0)*(A' 0)*(A' 1)*(B 1)*(B' 2)^2*(C 0)*(C' 1)*(C' 2) + (A 0)*(A' 0)*(A' 1)*(B 1)*(B' 2)^2*(C 1)*(C' 0)*(C' 2) - (A 0)*(A' 0)*(A' 1)*(B 2)*(B' 0)*(B' 2)*(C 1)*(C' 1)*(C' 2) + (A 0)*(A' 0)*(A' 1)*(B 2)*(B' 1)*(B' 2)*(C 1)*(C' 0)*(C' 2) - (A 0)*(A' 0)*(A' 2)*(B 0)*(B' 1)^2*(C 1)*(C' 2)^2 + (A 0)*(A' 0)*(A' 2)*(B 0)*(B' 1)^2*(C 2)*(C' 1)*(C' 2) - (A 0)*(A' 0)*(A' 2)*(B 0)*(B' 1)*(B' 2)*(C 2)*(C' 1)^2 + (A 0)*(A' 0)*(A' 2)*(B 0)*(B' 2)^2*(C 1)*(C' 1)^2 + (A 0)*(A' 0)*(A' 2)*(B 1)*(B' 0)*(B' 1)*(C 1)*(C' 2)^2 - (A 0)*(A' 0)*(A' 2)*(B 1)*(B' 0)*(B' 1)*(C 2)*(C' 1)*(C' 2) + (A 0)*(A' 0)*(A' 2)*(B 1)*(B' 1)*(B' 2)*(C 2)*(C' 0)*(C' 1) - (A 0)*(A' 0)*(A' 2)*(B 1)*(B' 2)^2*(C 1)*(C' 0)*(C' 1) + (A 0)*(A' 0)*(A' 2)*(B 2)*(B' 0)*(B' 1)*(C 1)*(C' 1)*(C' 2) + (A 0)*(A' 0)*(A' 2)*(B 2)*(B' 1)^2*(C 0)*(C' 1)*(C' 2) - (A 0)*(A' 0)*(A' 2)*(B 2)*(B' 1)*(B' 2)*(C 0)*(C' 1)^2 - (A 0)*(A' 0)*(A' 2)*(B 2)*(B' 1)*(B' 2)*(C 1)*(C' 0)*(C' 1) + (A 0)*(A' 1)^2*(B 0)*(B' 0)*(B' 2)*(C 1)*(C' 2)^2 - (A 0)*(A' 1)^2*(B 0)*(B' 0)*(B' 2)*(C 2)*(C' 1)*(C' 2) - (A 0)*(A' 1)^2*(B 0)*(B' 1)*(B' 2)*(C 0)*(C' 2)^2 + (A 0)*(A' 1)^2*(B 0)*(B' 1)*(B' 2)*(C 2)*(C' 0)*(C' 2) + (A 0)*(A' 1)^2*(B 0)*(B' 2)^2*(C 0)*(C' 1)*(C' 2) - (A 0)*(A' 1)^2*(B 0)*(B' 2)^2*(C 1)*(C' 0)*(C' 2) - (A 0)*(A' 1)^2*(B 2)*(B' 0)^2*(C 1)*(C' 2)^2 + (A 0)*(A' 1)^2*(B 2)*(B' 0)^2*(C 2)*(C' 1)*(C' 2) - (A 0)*(A' 1)^2*(B 2)*(B' 0)*(B' 2)*(C 0)*(C' 1)*(C' 2) + (A 0)*(A' 1)^2*(B 2)*(B' 1)*(B' 2)*(C 0)*(C' 0)*(C' 2) - (A 0)*(A' 1)^2*(B 2)*(B' 1)*(B' 2)*(C 2)*(C' 0)^2 + (A 0)*(A' 1)^2*(B 2)*(B' 2)^2*(C 1)*(C' 0)^2 + (A 0)*(A' 1)*(A' 2)*(B 0)*(B' 0)*(B' 2)*(C 2)*(C' 1)^2 + (A 0)*(A' 1)*(A' 2)*(B 0)*(B' 1)^2*(C 0)*(C' 2)^2 - (A 0)*(A' 1)*(A' 2)*(B 0)*(B' 1)^2*(C 2)*(C' 0)*(C' 2) - (A 0)*(A' 1)*(A' 2)*(B 0)*(B' 2)^2*(C 0)*(C' 1)^2 - (A 0)*(A' 1)*(A' 2)*(B 1)*(B' 0)*(B' 1)*(C 0)*(C' 2)^2 + (A 0)*(A' 1)*(A' 2)*(B 1)*(B' 0)*(B' 1)*(C 2)*(C' 0)*(C' 2) - (A 0)*(A' 1)*(A' 2)*(B 1)*(B' 0)*(B' 2)*(C 2)*(C' 0)*(C' 1) + (A 0)*(A' 1)*(A' 2)*(B 1)*(B' 2)^2*(C 0)*(C' 0)*(C' 1) - (A 0)*(A' 1)*(A' 2)*(B 2)*(B' 0)^2*(C 2)*(C' 1)^2 - (A 0)*(A' 1)*(A' 2)*(B 2)*(B' 0)*(B' 1)*(C 1)*(C' 0)*(C' 2) + (A 0)*(A' 1)*(A' 2)*(B 2)*(B' 0)*(B' 2)*(C 0)*(C' 1)^2 + (A 0)*(A' 1)*(A' 2)*(B 2)*(B' 0)*(B' 2)*(C 1)*(C' 0)*(C' 1) - (A 0)*(A' 1)*(A' 2)*(B 2)*(B' 1)^2*(C 0)*(C' 0)*(C' 2) + (A 0)*(A' 1)*(A' 2)*(B 2)*(B' 1)^2*(C 2)*(C' 0)^2 - (A 0)*(A' 2)^2*(B 0)*(B' 0)*(B' 2)*(C 1)*(C' 1)^2 - (A 0)*(A' 2)^2*(B 0)*(B' 1)^2*(C 0)*(C' 1)*(C' 2) + (A 0)*(A' 2)^2*(B 0)*(B' 1)^2*(C 1)*(C' 0)*(C' 2) + (A 0)*(A' 2)^2*(B 0)*(B' 1)*(B' 2)*(C 0)*(C' 1)^2 + (A 0)*(A' 2)^2*(B 1)*(B' 0)*(B' 1)*(C 0)*(C' 1)*(C' 2) - (A 0)*(A' 2)^2*(B 1)*(B' 0)*(B' 1)*(C 1)*(C' 0)*(C' 2) + (A 0)*(A' 2)^2*(B 1)*(B' 0)*(B' 2)*(C 1)*(C' 0)*(C' 1) - (A 0)*(A' 2)^2*(B 1)*(B' 1)*(B' 2)*(C 0)*(C' 0)*(C' 1) + (A 0)*(A' 2)^2*(B 2)*(B' 0)^2*(C 1)*(C' 1)^2 - (A 0)*(A' 2)^2*(B 2)*(B' 1)^2*(C 1)*(C' 0)^2 + (A 1)*(A' 0)^2*(B 1)*(B' 0)*(B' 2)*(C 1)*(C' 2)^2 - (A 1)*(A' 0)^2*(B 1)*(B' 0)*(B' 2)*(C 2)*(C' 1)*(C' 2) - (A 1)*(A' 0)^2*(B 1)*(B' 1)*(B' 2)*(C 0)*(C' 2)^2 + (A 1)*(A' 0)^2*(B 1)*(B' 1)*(B' 2)*(C 2)*(C' 0)*(C' 2) + (A 1)*(A' 0)^2*(B 1)*(B' 2)^2*(C 0)*(C' 1)*(C' 2) - (A 1)*(A' 0)^2*(B 1)*(B' 2)^2*(C 1)*(C' 0)*(C' 2) - (A 1)*(A' 0)^2*(B 2)*(B' 0)*(B' 1)*(C 1)*(C' 2)^2 + (A 1)*(A' 0)^2*(B 2)*(B' 0)*(B' 1)*(C 2)*(C' 1)*(C' 2) - (A 1)*(A' 0)^2*(B 2)*(B' 1)*(B' 2)*(C 2)*(C' 0)*(C' 1) + (A 1)*(A' 0)^2*(B 2)*(B' 2)^2*(C 1)*(C' 0)*(C' 1) - (A 1)*(A' 0)*(A' 1)*(B 0)*(B' 0)*(B' 2)*(C 1)*(C' 2)^2 + (A 1)*(A' 0)*(A' 1)*(B 0)*(B' 0)*(B' 2)*(C 2)*(C' 1)*(C' 2) + (A 1)*(A' 0)*(A' 1)*(B 0)*(B' 1)*(B' 2)*(C 0)*(C' 2)^2 - (A 1)*(A' 0)*(A' 1)*(B 0)*(B' 1)*(B' 2)*(C 2)*(C' 0)*(C' 2) - (A 1)*(A' 0)*(A' 1)*(B 0)*(B' 2)^2*(C 0)*(C' 1)*(C' 2) + (A 1)*(A' 0)*(A' 1)*(B 0)*(B' 2)^2*(C 1)*(C' 0)*(C' 2) + (A 1)*(A' 0)*(A' 1)*(B 2)*(B' 0)^2*(C 1)*(C' 2)^2 - (A 1)*(A' 0)*(A' 1)*(B 2)*(B' 0)^2*(C 2)*(C' 1)*(C' 2) + (A 1)*(A' 0)*(A' 1)*(B 2)*(B' 0)*(B' 2)*(C 0)*(C' 1)*(C' 2) - (A 1)*(A' 0)*(A' 1)*(B 2)*(B' 1)*(B' 2)*(C 0)*(C' 0)*(C' 2) + (A 1)*(A' 0)*(A' 1)*(B 2)*(B' 1)*(B' 2)*(C 2)*(C' 0)^2 - (A 1)*(A' 0)*(A' 1)*(B 2)*(B' 2)^2*(C 1)*(C' 0)^2 + (A 1)*(A' 0)*(A' 2)*(B 0)*(B' 0)*(B' 1)*(C 1)*(C' 2)^2 - (A 1)*(A' 0)*(A' 2)*(B 0)*(B' 0)*(B' 1)*(C 2)*(C' 1)*(C' 2) + (A 1)*(A' 0)*(A' 2)*(B 0)*(B' 1)*(B' 2)*(C 2)*(C' 0)*(C' 1) - (A 1)*(A' 0)*(A' 2)*(B 0)*(B' 2)^2*(C 1)*(C' 0)*(C' 1) - (A 1)*(A' 0)*(A' 2)*(B 1)*(B' 0)^2*(C 1)*(C' 2)^2 + (A 1)*(A' 0)*(A' 2)*(B 1)*(B' 0)^2*(C 2)*(C' 1)*(C' 2) - (A 1)*(A' 0)*(A' 2)*(B 1)*(B' 1)*(B' 2)*(C 2)*(C' 0)^2 + (A 1)*(A' 0)*(A' 2)*(B 1)*(B' 2)^2*(C 1)*(C' 0)^2 - (A 1)*(A' 0)*(A' 2)*(B 2)*(B' 0)*(B' 1)*(C 0)*(C' 1)*(C' 2) + (A 1)*(A' 0)*(A' 2)*(B 2)*(B' 1)*(B' 2)*(C 0)*(C' 0)*(C' 1) - (A 1)*(A' 1)*(A' 2)*(B 0)*(B' 0)*(B' 1)*(C 0)*(C' 2)^2 + (A 1)*(A' 1)*(A' 2)*(B 0)*(B' 0)*(B' 1)*(C 2)*(C' 0)*(C' 2) - (A 1)*(A' 1)*(A' 2)*(B 0)*(B' 0)*(B' 2)*(C 2)*(C' 0)*(C' 1) + (A 1)*(A' 1)*(A' 2)*(B 0)*(B' 2)^2*(C 0)*(C' 0)*(C' 1) + (A 1)*(A' 1)*(A' 2)*(B 1)*(B' 0)^2*(C 0)*(C' 2)^2 - (A 1)*(A' 1)*(A' 2)*(B 1)*(B' 0)^2*(C 2)*(C' 0)*(C' 2) + (A 1)*(A' 1)*(A' 2)*(B 1)*(B' 0)*(B' 2)*(C 2)*(C' 0)^2 - (A 1)*(A' 1)*(A' 2)*(B 1)*(B' 2)^2*(C 0)*(C' 0)^2 + (A 1)*(A' 1)*(A' 2)*(B 2)*(B' 0)^2*(C 2)*(C' 0)*(C' 1) + (A 1)*(A' 1)*(A' 2)*(B 2)*(B' 0)*(B' 1)*(C 0)*(C' 0)*(C' 2) - (A 1)*(A' 1)*(A' 2)*(B 2)*(B' 0)*(B' 1)*(C 2)*(C' 0)^2 - (A 1)*(A' 1)*(A' 2)*(B 2)*(B' 0)*(B' 2)*(C 0)*(C' 0)*(C' 1) + (A 1)*(A' 2)^2*(B 0)*(B' 0)*(B' 1)*(C 0)*(C' 1)*(C' 2) - (A 1)*(A' 2)^2*(B 0)*(B' 0)*(B' 1)*(C 1)*(C' 0)*(C' 2) + (A 1)*(A' 2)^2*(B 0)*(B' 0)*(B' 2)*(C 1)*(C' 0)*(C' 1) - (A 1)*(A' 2)^2*(B 0)*(B' 1)*(B' 2)*(C 0)*(C' 0)*(C' 1) - (A 1)*(A' 2)^2*(B 1)*(B' 0)^2*(C 0)*(C' 1)*(C' 2) + (A 1)*(A' 2)^2*(B 1)*(B' 0)^2*(C 1)*(C' 0)*(C' 2) - (A 1)*(A' 2)^2*(B 1)*(B' 0)*(B' 2)*(C 1)*(C' 0)^2 + (A 1)*(A' 2)^2*(B 1)*(B' 1)*(B' 2)*(C 0)*(C' 0)^2 - (A 1)*(A' 2)^2*(B 2)*(B' 0)^2*(C 1)*(C' 0)*(C' 1) + (A 1)*(A' 2)^2*(B 2)*(B' 0)*(B' 1)*(C 1)*(C' 0)^2 - (A 2)*(A' 0)^2*(B 1)*(B' 0)*(B' 2)*(C 1)*(C' 1)*(C' 2) + (A 2)*(A' 0)^2*(B 1)*(B' 0)*(B' 2)*(C 2)*(C' 1)^2 + (A 2)*(A' 0)^2*(B 1)*(B' 1)^2*(C 0)*(C' 2)^2 - (A 2)*(A' 0)^2*(B 1)*(B' 1)^2*(C 2)*(C' 0)*(C' 2) + (A 2)*(A' 0)^2*(B 1)*(B' 1)*(B' 2)*(C 1)*(C' 0)*(C' 2) - (A 2)*(A' 0)^2*(B 1)*(B' 2)^2*(C 0)*(C' 1)^2 + (A 2)*(A' 0)^2*(B 2)*(B' 0)*(B' 1)*(C 1)*(C' 1)*(C' 2) - (A 2)*(A' 0)^2*(B 2)*(B' 0)*(B' 1)*(C 2)*(C' 1)^2 + (A 2)*(A' 0)^2*(B 2)*(B' 1)^2*(C 2)*(C' 0)*(C' 1) - (A 2)*(A' 0)^2*(B 2)*(B' 1)*(B' 2)*(C 1)*(C' 0)*(C' 1) + (A 2)*(A' 0)*(A' 1)*(B 0)*(B' 0)*(B' 2)*(C 1)*(C' 1)*(C' 2) - (A 2)*(A' 0)*(A' 1)*(B 0)*(B' 0)*(B' 2)*(C 2)*(C' 1)^2 - (A 2)*(A' 0)*(A' 1)*(B 0)*(B' 1)^2*(C 0)*(C' 2)^2 + (A 2)*(A' 0)*(A' 1)*(B 0)*(B' 1)^2*(C 2)*(C' 0)*(C' 2) - (A 2)*(A' 0)*(A' 1)*(B 0)*(B' 1)*(B' 2)*(C 1)*(C' 0)*(C' 2) + (A 2)*(A' 0)*(A' 1)*(B 0)*(B' 2)^2*(C 0)*(C' 1)^2 - (A 2)*(A' 0)*(A' 1)*(B 1)*(B' 0)*(B' 2)*(C 0)*(C' 1)*(C' 2) + (A 2)*(A' 0)*(A' 1)*(B 1)*(B' 1)*(B' 2)*(C 0)*(C' 0)*(C' 2) - (A 2)*(A' 0)*(A' 1)*(B 2)*(B' 0)^2*(C 1)*(C' 1)*(C' 2) + (A 2)*(A' 0)*(A' 1)*(B 2)*(B' 0)^2*(C 2)*(C' 1)^2 - (A 2)*(A' 0)*(A' 1)*(B 2)*(B' 0)*(B' 2)*(C 0)*(C' 1)^2 + (A 2)*(A' 0)*(A' 1)*(B 2)*(B' 1)^2*(C 0)*(C' 0)*(C' 2) - (A 2)*(A' 0)*(A' 1)*(B 2)*(B' 1)^2*(C 2)*(C' 0)^2 + (A 2)*(A' 0)*(A' 1)*(B 2)*(B' 1)*(B' 2)*(C 1)*(C' 0)^2 - (A 2)*(A' 0)*(A' 2)*(B 0)*(B' 0)*(B' 1)*(C 1)*(C' 1)*(C' 2) + (A 2)*(A' 0)*(A' 2)*(B 0)*(B' 0)*(B' 1)*(C 2)*(C' 1)^2 - (A 2)*(A' 0)*(A' 2)*(B 0)*(B' 1)^2*(C 2)*(C' 0)*(C' 1) + (A 2)*(A' 0)*(A' 2)*(B 0)*(B' 1)*(B' 2)*(C 1)*(C' 0)*(C' 1) + (A 2)*(A' 0)*(A' 2)*(B 1)*(B' 0)^2*(C 1)*(C' 1)*(C' 2) - (A 2)*(A' 0)*(A' 2)*(B 1)*(B' 0)^2*(C 2)*(C' 1)^2 + (A 2)*(A' 0)*(A' 2)*(B 1)*(B' 0)*(B' 1)*(C 0)*(C' 1)*(C' 2) + (A 2)*(A' 0)*(A' 2)*(B 1)*(B' 1)^2*(C 2)*(C' 0)^2 - (A 2)*(A' 0)*(A' 2)*(B 1)*(B' 1)*(B' 2)*(C 0)*(C' 0)*(C' 1) - (A 2)*(A' 0)*(A' 2)*(B 1)*(B' 1)*(B' 2)*(C 1)*(C' 0)^2 + (A 2)*(A' 0)*(A' 2)*(B 2)*(B' 0)*(B' 1)*(C 0)*(C' 1)^2 - (A 2)*(A' 0)*(A' 2)*(B 2)*(B' 1)^2*(C 0)*(C' 0)*(C' 1) + (A 2)*(A' 1)^2*(B 0)*(B' 0)*(B' 1)*(C 0)*(C' 2)^2 - (A 2)*(A' 1)^2*(B 0)*(B' 0)*(B' 1)*(C 2)*(C' 0)*(C' 2) + (A 2)*(A' 1)^2*(B 0)*(B' 0)*(B' 2)*(C 2)*(C' 0)*(C' 1) - (A 2)*(A' 1)^2*(B 0)*(B' 2)^2*(C 0)*(C' 0)*(C' 1) - (A 2)*(A' 1)^2*(B 1)*(B' 0)^2*(C 0)*(C' 2)^2 + (A 2)*(A' 1)^2*(B 1)*(B' 0)^2*(C 2)*(C' 0)*(C' 2) - (A 2)*(A' 1)^2*(B 1)*(B' 0)*(B' 2)*(C 2)*(C' 0)^2 + (A 2)*(A' 1)^2*(B 1)*(B' 2)^2*(C 0)*(C' 0)^2 - (A 2)*(A' 1)^2*(B 2)*(B' 0)^2*(C 2)*(C' 0)*(C' 1) - (A 2)*(A' 1)^2*(B 2)*(B' 0)*(B' 1)*(C 0)*(C' 0)*(C' 2) + (A 2)*(A' 1)^2*(B 2)*(B' 0)*(B' 1)*(C 2)*(C' 0)^2 + (A 2)*(A' 1)^2*(B 2)*(B' 0)*(B' 2)*(C 0)*(C' 0)*(C' 1) + (A 2)*(A' 1)*(A' 2)*(B 0)*(B' 0)*(B' 1)*(C 1)*(C' 0)*(C' 2) - (A 2)*(A' 1)*(A' 2)*(B 0)*(B' 0)*(B' 2)*(C 1)*(C' 0)*(C' 1) - (A 2)*(A' 1)*(A' 2)*(B 1)*(B' 0)^2*(C 1)*(C' 0)*(C' 2) - (A 2)*(A' 1)*(A' 2)*(B 1)*(B' 0)*(B' 1)*(C 0)*(C' 0)*(C' 2) + (A 2)*(A' 1)*(A' 2)*(B 1)*(B' 0)*(B' 2)*(C 0)*(C' 0)*(C' 1) + (A 2)*(A' 1)*(A' 2)*(B 1)*(B' 0)*(B' 2)*(C 1)*(C' 0)^2 + (A 2)*(A' 1)*(A' 2)*(B 2)*(B' 0)^2*(C 1)*(C' 0)*(C' 1) - (A 2)*(A' 1)*(A' 2)*(B 2)*(B' 0)*(B' 1)*(C 1)*(C' 0)^2 - (A 2)*(A' 2)^2*(B 0)*(B' 0)*(B' 1)*(C 0)*(C' 1)^2 + (A 2)*(A' 2)^2*(B 0)*(B' 1)^2*(C 0)*(C' 0)*(C' 1) + (A 2)*(A' 2)^2*(B 1)*(B' 0)^2*(C 0)*(C' 1)^2 - (A 2)*(A' 2)^2*(B 1)*(B' 1)^2*(C 0)*(C' 0)^2) * hABC +
    (-(A 0)^2*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 1)*(C 2)*(C' 2) + (A 0)^2*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 2)^2*(C' 1) - (A 0)^2*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 1)*(C 2)*(C' 1) + (A 0)^2*(A' 0)*(B 2)^2*(B' 1)*(C 1)^2*(C' 2) - (A 0)^2*(A' 0)*(B 2)^2*(B' 1)*(C 1)*(C 2)*(C' 1) + (A 0)^2*(A' 0)*(B 2)^2*(B' 2)*(C 1)^2*(C' 1) + (A 0)^2*(A' 1)*(B 0)*(B 2)*(B' 1)*(C 1)*(C 2)*(C' 2) - (A 0)^2*(A' 1)*(B 0)*(B 2)*(B' 1)*(C 2)^2*(C' 1) - (A 0)^2*(A' 1)*(B 0)*(B 2)*(B' 2)*(C 1)^2*(C' 2) + (A 0)^2*(A' 1)*(B 0)*(B 2)*(B' 2)*(C 1)*(C 2)*(C' 1) - (A 0)^2*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 1)*(C 2)*(C' 2) + (A 0)^2*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 2)^2*(C' 1) - (A 0)^2*(A' 1)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 2)*(C' 2) + (A 0)^2*(A' 1)*(B 1)*(B 2)*(B' 1)*(C 2)^2*(C' 0) + (A 0)^2*(A' 1)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 2) - (A 0)^2*(A' 1)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 2)*(C' 1) - (A 0)^2*(A' 1)*(B 1)*(B 2)*(B' 2)*(C 1)*(C 2)*(C' 0) + (A 0)^2*(A' 1)*(B 2)^2*(B' 0)*(C 1)^2*(C' 2) - (A 0)^2*(A' 1)*(B 2)^2*(B' 0)*(C 1)*(C 2)*(C' 1) + (A 0)^2*(A' 1)*(B 2)^2*(B' 1)*(C 0)*(C 2)*(C' 1) - (A 0)^2*(A' 1)*(B 2)^2*(B' 1)*(C 1)*(C 2)*(C' 0) + (A 0)^2*(A' 1)*(B 2)^2*(B' 2)*(C 1)^2*(C' 0) + (A 0)^2*(A' 2)*(B 0)*(B 1)*(B' 2)*(C 1)^2*(C' 2) - (A 0)^2*(A' 2)*(B 0)*(B 2)*(B' 1)*(C 1)^2*(C' 2) + (A 0)^2*(A' 2)*(B 0)*(B 2)*(B' 1)*(C 1)*(C 2)*(C' 1) - (A 0)^2*(A' 2)*(B 0)*(B 2)*(B' 2)*(C 1)^2*(C' 1) - (A 0)^2*(A' 2)*(B 1)^2*(B' 2)*(C 0)*(C 1)*(C' 2) - (A 0)^2*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 1)*(C 2)*(C' 1) + (A 0)^2*(A' 2)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 2) - (A 0)^2*(A' 2)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 2)*(C' 1) - (A 0)^2*(A' 2)*(B 1)*(B 2)*(B' 1)*(C 1)*(C 2)*(C' 0) + (A 0)^2*(A' 2)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 1) + (A 0)^2*(A' 2)*(B 2)^2*(B' 0)*(C 1)^2*(C' 1) + (A 0)^2*(A' 2)*(B 2)^2*(B' 1)*(C 1)^2*(C' 0) + (A 0)*(A 1)*(A' 0)*(B 0)*(B 2)*(B' 2)*(C 1)^2*(C' 2) + (A 0)*(A 1)*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 1)*(C 2)*(C' 2) - (A 0)*(A 1)*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 2)^2*(C' 1) + (A 0)*(A 1)*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 2)*(C' 2) - (A 0)*(A 1)*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 2)^2*(C' 0) - (A 0)*(A 1)*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 1)*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 2)*(C' 1) + (A 0)*(A 1)*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 1)*(C 2)*(C' 0) - (A 0)*(A 1)*(A' 0)*(B 2)^2*(B' 0)*(C 1)^2*(C' 2) + (A 0)*(A 1)*(A' 0)*(B 2)^2*(B' 0)*(C 1)*(C 2)*(C' 1) - (A 0)*(A 1)*(A' 0)*(B 2)^2*(B' 1)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 1)*(A' 0)*(B 2)^2*(B' 1)*(C 1)*(C 2)*(C' 0) - (A 0)*(A 1)*(A' 0)*(B 2)^2*(B' 2)*(C 0)*(C 1)*(C' 1) - (A 0)*(A 1)*(A' 0)*(B 2)^2*(B' 2)*(C 1)^2*(C' 0) + (A 0)*(A 1)*(A' 1)*(B 0)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 1)*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 2)*(C' 2) - (A 0)*(A 1)*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 2)^2*(C' 0) - (A 0)*(A 1)*(A' 1)*(B 1)*(B 2)*(B' 2)*(C 0)^2*(C' 2) + (A 0)*(A 1)*(A' 1)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 2)*(C' 0) - (A 0)*(A 1)*(A' 1)*(B 2)^2*(B' 0)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 1)*(A' 1)*(B 2)^2*(B' 0)*(C 1)*(C 2)*(C' 0) - (A 0)*(A 1)*(A' 1)*(B 2)^2*(B' 2)*(C 0)*(C 1)*(C' 0) - (A 0)*(A 1)*(A' 2)*(B 0)^2*(B' 2)*(C 1)^2*(C' 2) + (A 0)*(A 1)*(A' 2)*(B 0)*(B 2)*(B' 0)*(C 1)^2*(C' 2) + (A 0)*(A 1)*(A' 2)*(B 0)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 1)*(A' 2)*(B 0)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 1) + (A 0)*(A 1)*(A' 2)*(B 0)*(B 2)*(B' 2)*(C 1)^2*(C' 0) + (A 0)*(A 1)*(A' 2)*(B 1)^2*(B' 2)*(C 0)^2*(C' 2) - (A 0)*(A 1)*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 1)*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 2)*(C' 1) + (A 0)*(A 1)*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 1)*(C 2)*(C' 0) - (A 0)*(A 1)*(A' 2)*(B 1)*(B 2)*(B' 1)*(C 0)^2*(C' 2) + (A 0)*(A 1)*(A' 2)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 2)*(C' 0) - (A 0)*(A 1)*(A' 2)*(B 1)*(B 2)*(B' 2)*(C 0)^2*(C' 1) - (A 0)*(A 1)*(A' 2)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 0) - (A 0)*(A 1)*(A' 2)*(B 2)^2*(B' 0)*(C 0)*(C 1)*(C' 1) - (A 0)*(A 1)*(A' 2)*(B 2)^2*(B' 0)*(C 1)^2*(C' 0) - (A 0)*(A 1)*(A' 2)*(B 2)^2*(B' 1)*(C 0)*(C 1)*(C' 0) + (A 0)*(A 2)*(A' 0)*(B 0)*(B 1)*(B' 1)*(C 1)*(C 2)*(C' 2) - (A 0)*(A 2)*(A' 0)*(B 0)*(B 1)*(B' 1)*(C 2)^2*(C' 1) - (A 0)*(A 2)*(A' 0)*(B 0)*(B 1)*(B' 2)*(C 1)^2*(C' 2) + (A 0)*(A 2)*(A' 0)*(B 0)*(B 1)*(B' 2)*(C 1)*(C 2)*(C' 1) - (A 0)*(A 2)*(A' 0)*(B 0)*(B 2)*(B' 1)*(C 1)^2*(C' 2) + (A 0)*(A 2)*(A' 0)*(B 0)*(B 2)*(B' 1)*(C 1)*(C 2)*(C' 1) - (A 0)*(A 2)*(A' 0)*(B 0)*(B 2)*(B' 2)*(C 1)^2*(C' 1) - (A 0)*(A 2)*(A' 0)*(B 1)^2*(B' 0)*(C 1)*(C 2)*(C' 2) + (A 0)*(A 2)*(A' 0)*(B 1)^2*(B' 0)*(C 2)^2*(C' 1) - (A 0)*(A 2)*(A' 0)*(B 1)^2*(B' 1)*(C 0)*(C 2)*(C' 2) + (A 0)*(A 2)*(A' 0)*(B 1)^2*(B' 1)*(C 2)^2*(C' 0) + (A 0)*(A 2)*(A' 0)*(B 1)^2*(B' 2)*(C 0)*(C 1)*(C' 2) - (A 0)*(A 2)*(A' 0)*(B 1)^2*(B' 2)*(C 0)*(C 2)*(C' 1) - (A 0)*(A 2)*(A' 0)*(B 1)^2*(B' 2)*(C 1)*(C 2)*(C' 0) + (A 0)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 1)^2*(C' 2) - (A 0)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 1)*(C 2)*(C' 1) + (A 0)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 2) - (A 0)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 2)*(C' 1) - (A 0)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 1)*(C 2)*(C' 0) + (A 0)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 1) + (A 0)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 1)^2*(C' 0) + (A 0)*(A 2)*(A' 0)*(B 2)^2*(B' 1)*(C 0)*(C 1)*(C' 1) - (A 0)*(A 2)*(A' 1)*(B 0)^2*(B' 1)*(C 1)*(C 2)*(C' 2) + (A 0)*(A 2)*(A' 1)*(B 0)^2*(B' 1)*(C 2)^2*(C' 1) + (A 0)*(A 2)*(A' 1)*(B 0)^2*(B' 2)*(C 1)^2*(C' 2) - (A 0)*(A 2)*(A' 1)*(B 0)^2*(B' 2)*(C 1)*(C 2)*(C' 1) + (A 0)*(A 2)*(A' 1)*(B 0)*(B 1)*(B' 0)*(C 1)*(C 2)*(C' 2) - (A 0)*(A 2)*(A' 1)*(B 0)*(B 1)*(B' 0)*(C 2)^2*(C' 1) + (A 0)*(A 2)*(A' 1)*(B 0)*(B 1)*(B' 1)*(C 0)*(C 2)*(C' 2) - (A 0)*(A 2)*(A' 1)*(B 0)*(B 1)*(B' 1)*(C 2)^2*(C' 0) - (A 0)*(A 2)*(A' 1)*(B 0)*(B 1)*(B' 2)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 2)*(A' 1)*(B 0)*(B 1)*(B' 2)*(C 0)*(C 2)*(C' 1) + (A 0)*(A 2)*(A' 1)*(B 0)*(B 1)*(B' 2)*(C 1)*(C 2)*(C' 0) - (A 0)*(A 2)*(A' 1)*(B 0)*(B 2)*(B' 0)*(C 1)^2*(C' 2) + (A 0)*(A 2)*(A' 1)*(B 0)*(B 2)*(B' 0)*(C 1)*(C 2)*(C' 1) - (A 0)*(A 2)*(A' 1)*(B 0)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 2)*(A' 1)*(B 0)*(B 2)*(B' 1)*(C 1)*(C 2)*(C' 0) - (A 0)*(A 2)*(A' 1)*(B 0)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 1) - (A 0)*(A 2)*(A' 1)*(B 0)*(B 2)*(B' 2)*(C 1)^2*(C' 0) - (A 0)*(A 2)*(A' 1)*(B 1)^2*(B' 0)*(C 0)*(C 2)*(C' 2) + (A 0)*(A 2)*(A' 1)*(B 1)^2*(B' 0)*(C 2)^2*(C' 0) - (A 0)*(A 2)*(A' 1)*(B 1)^2*(B' 2)*(C 0)*(C 2)*(C' 0) + (A 0)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 2) - (A 0)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 2)*(C' 1) - (A 0)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 1)*(C 2)*(C' 0) + (A 0)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 1)*(C 0)^2*(C' 2) - (A 0)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 2)*(C' 0) + (A 0)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 2)*(C 0)^2*(C' 1) + (A 0)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 0) + (A 0)*(A 2)*(A' 1)*(B 2)^2*(B' 0)*(C 0)*(C 1)*(C' 1) - (A 0)*(A 2)*(A' 1)*(B 2)^2*(B' 1)*(C 0)^2*(C' 1) + (A 0)*(A 2)*(A' 1)*(B 2)^2*(B' 1)*(C 0)*(C 1)*(C' 0) + (A 0)*(A 2)*(A' 2)*(B 0)^2*(B' 1)*(C 1)^2*(C' 2) - (A 0)*(A 2)*(A' 2)*(B 0)^2*(B' 1)*(C 1)*(C 2)*(C' 1) + (A 0)*(A 2)*(A' 2)*(B 0)^2*(B' 2)*(C 1)^2*(C' 1) - (A 0)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 0)*(C 1)^2*(C' 2) + (A 0)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 0)*(C 1)*(C 2)*(C' 1) - (A 0)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 1)*(C 0)*(C 1)*(C' 2) + (A 0)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 1)*(C 0)*(C 2)*(C' 1) + (A 0)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 1)*(C 1)*(C 2)*(C' 0) - (A 0)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 2)*(C 0)*(C 1)*(C' 1) - (A 0)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 2)*(C 1)^2*(C' 0) - (A 0)*(A 2)*(A' 2)*(B 0)*(B 2)*(B' 0)*(C 1)^2*(C' 1) - (A 0)*(A 2)*(A' 2)*(B 0)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 1) - (A 0)*(A 2)*(A' 2)*(B 0)*(B 2)*(B' 1)*(C 1)^2*(C' 0) + (A 0)*(A 2)*(A' 2)*(B 1)^2*(B' 0)*(C 0)*(C 1)*(C' 2) - (A 0)*(A 2)*(A' 2)*(B 1)^2*(B' 0)*(C 0)*(C 2)*(C' 1) - (A 0)*(A 2)*(A' 2)*(B 1)^2*(B' 0)*(C 1)*(C 2)*(C' 0) - (A 0)*(A 2)*(A' 2)*(B 1)^2*(B' 1)*(C 0)*(C 2)*(C' 0) + (A 0)*(A 2)*(A' 2)*(B 1)^2*(B' 2)*(C 0)*(C 1)*(C' 0) + (A 0)*(A 2)*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 1) + (A 0)*(A 2)*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 1)^2*(C' 0) + (A 0)*(A 2)*(A' 2)*(B 1)*(B 2)*(B' 1)*(C 0)^2*(C' 1) + (A 0)*(A 2)*(A' 2)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 0) - (A 1)^2*(A' 0)*(B 0)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 2) - (A 1)^2*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 2)*(C' 2) + (A 1)^2*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 2)^2*(C' 0) + (A 1)^2*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 0)^2*(C' 2) - (A 1)^2*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 2)*(C' 0) + (A 1)^2*(A' 0)*(B 2)^2*(B' 0)*(C 0)*(C 1)*(C' 2) - (A 1)^2*(A' 0)*(B 2)^2*(B' 0)*(C 1)*(C 2)*(C' 0) + (A 1)^2*(A' 0)*(B 2)^2*(B' 2)*(C 0)*(C 1)*(C' 0) + (A 1)^2*(A' 2)*(B 0)^2*(B' 2)*(C 0)*(C 1)*(C' 2) - (A 1)^2*(A' 2)*(B 0)*(B 1)*(B' 2)*(C 0)^2*(C' 2) - (A 1)^2*(A' 2)*(B 0)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 2) - (A 1)^2*(A' 2)*(B 0)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 0) + (A 1)^2*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 0)^2*(C' 2) - (A 1)^2*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 2)*(C' 0) + (A 1)^2*(A' 2)*(B 1)*(B 2)*(B' 2)*(C 0)^2*(C' 0) + (A 1)^2*(A' 2)*(B 2)^2*(B' 0)*(C 0)*(C 1)*(C' 0) + (A 1)*(A 2)*(A' 0)*(B 0)*(B 1)*(B' 2)*(C 0)*(C 1)*(C' 2) + (A 1)*(A 2)*(A' 0)*(B 0)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 2) + (A 1)*(A 2)*(A' 0)*(B 0)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 1) + (A 1)*(A 2)*(A' 0)*(B 1)^2*(B' 0)*(C 0)*(C 2)*(C' 2) - (A 1)*(A 2)*(A' 0)*(B 1)^2*(B' 0)*(C 2)^2*(C' 0) - (A 1)*(A 2)*(A' 0)*(B 1)^2*(B' 2)*(C 0)^2*(C' 2) + (A 1)*(A 2)*(A' 0)*(B 1)^2*(B' 2)*(C 0)*(C 2)*(C' 0) - (A 1)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 2) + (A 1)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 2)*(C' 1) - (A 1)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 0)^2*(C' 2) + (A 1)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 2)*(C' 0) - (A 1)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 0)^2*(C' 1) - (A 1)*(A 2)*(A' 0)*(B 1)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 0) - (A 1)*(A 2)*(A' 0)*(B 2)^2*(B' 0)*(C 0)*(C 1)*(C' 1) + (A 1)*(A 2)*(A' 0)*(B 2)^2*(B' 0)*(C 1)^2*(C' 0) - (A 1)*(A 2)*(A' 0)*(B 2)^2*(B' 1)*(C 0)*(C 1)*(C' 0) - (A 1)*(A 2)*(A' 1)*(B 0)^2*(B' 2)*(C 0)*(C 1)*(C' 2) + (A 1)*(A 2)*(A' 1)*(B 0)*(B 1)*(B' 2)*(C 0)^2*(C' 2) + (A 1)*(A 2)*(A' 1)*(B 0)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 2) + (A 1)*(A 2)*(A' 1)*(B 0)*(B 2)*(B' 2)*(C 0)*(C 1)*(C' 0) - (A 1)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 0)^2*(C' 2) + (A 1)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 2)*(C' 0) - (A 1)*(A 2)*(A' 1)*(B 1)*(B 2)*(B' 2)*(C 0)^2*(C' 0) - (A 1)*(A 2)*(A' 1)*(B 2)^2*(B' 0)*(C 0)*(C 1)*(C' 0) - (A 1)*(A 2)*(A' 2)*(B 0)^2*(B' 1)*(C 0)*(C 1)*(C' 2) - (A 1)*(A 2)*(A' 2)*(B 0)^2*(B' 2)*(C 0)*(C 1)*(C' 1) + (A 1)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 0)*(C 0)*(C 1)*(C' 2) + (A 1)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 1)*(C 0)^2*(C' 2) + (A 1)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 2)*(C 0)^2*(C' 1) + (A 1)*(A 2)*(A' 2)*(B 0)*(B 1)*(B' 2)*(C 0)*(C 1)*(C' 0) + (A 1)*(A 2)*(A' 2)*(B 0)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 1) + (A 1)*(A 2)*(A' 2)*(B 0)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 0) - (A 1)*(A 2)*(A' 2)*(B 1)^2*(B' 0)*(C 0)^2*(C' 2) + (A 1)*(A 2)*(A' 2)*(B 1)^2*(B' 0)*(C 0)*(C 2)*(C' 0) - (A 1)*(A 2)*(A' 2)*(B 1)^2*(B' 2)*(C 0)^2*(C' 0) - (A 1)*(A 2)*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 0)^2*(C' 1) - (A 1)*(A 2)*(A' 2)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 0) - (A 1)*(A 2)*(A' 2)*(B 1)*(B 2)*(B' 1)*(C 0)^2*(C' 0) - (A 2)^2*(A' 0)*(B 0)*(B 1)*(B' 1)*(C 0)*(C 1)*(C' 2) + (A 2)^2*(A' 0)*(B 0)*(B 1)*(B' 1)*(C 0)*(C 2)*(C' 1) - (A 2)^2*(A' 0)*(B 0)*(B 1)*(B' 2)*(C 0)*(C 1)*(C' 1) - (A 2)^2*(A' 0)*(B 0)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 1) - (A 2)^2*(A' 0)*(B 1)^2*(B' 0)*(C 0)*(C 2)*(C' 1) + (A 2)^2*(A' 0)*(B 1)^2*(B' 0)*(C 1)*(C 2)*(C' 0) + (A 2)^2*(A' 0)*(B 1)^2*(B' 1)*(C 0)^2*(C' 2) - (A 2)^2*(A' 0)*(B 1)^2*(B' 1)*(C 0)*(C 2)*(C' 0) + (A 2)^2*(A' 0)*(B 1)^2*(B' 2)*(C 0)^2*(C' 1) + (A 2)^2*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 1) - (A 2)^2*(A' 0)*(B 1)*(B 2)*(B' 0)*(C 1)^2*(C' 0) + (A 2)^2*(A' 0)*(B 1)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 0) + (A 2)^2*(A' 1)*(B 0)^2*(B' 1)*(C 0)*(C 1)*(C' 2) - (A 2)^2*(A' 1)*(B 0)^2*(B' 1)*(C 0)*(C 2)*(C' 1) + (A 2)^2*(A' 1)*(B 0)^2*(B' 2)*(C 0)*(C 1)*(C' 1) - (A 2)^2*(A' 1)*(B 0)*(B 1)*(B' 0)*(C 0)*(C 1)*(C' 2) + (A 2)^2*(A' 1)*(B 0)*(B 1)*(B' 0)*(C 0)*(C 2)*(C' 1) - (A 2)^2*(A' 1)*(B 0)*(B 1)*(B' 1)*(C 0)^2*(C' 2) + (A 2)^2*(A' 1)*(B 0)*(B 1)*(B' 1)*(C 0)*(C 2)*(C' 0) - (A 2)^2*(A' 1)*(B 0)*(B 1)*(B' 2)*(C 0)^2*(C' 1) - (A 2)^2*(A' 1)*(B 0)*(B 1)*(B' 2)*(C 0)*(C 1)*(C' 0) - (A 2)^2*(A' 1)*(B 0)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 1) + (A 2)^2*(A' 1)*(B 0)*(B 2)*(B' 1)*(C 0)^2*(C' 1) - (A 2)^2*(A' 1)*(B 0)*(B 2)*(B' 1)*(C 0)*(C 1)*(C' 0) + (A 2)^2*(A' 1)*(B 1)^2*(B' 0)*(C 0)^2*(C' 2) - (A 2)^2*(A' 1)*(B 1)^2*(B' 0)*(C 0)*(C 2)*(C' 0) + (A 2)^2*(A' 1)*(B 1)^2*(B' 2)*(C 0)^2*(C' 0) + (A 2)^2*(A' 1)*(B 1)*(B 2)*(B' 0)*(C 0)*(C 1)*(C' 0) + (A 2)^2*(A' 2)*(B 0)^2*(B' 1)*(C 0)*(C 1)*(C' 1) - (A 2)^2*(A' 2)*(B 0)*(B 1)*(B' 0)*(C 0)*(C 1)*(C' 1) - (A 2)^2*(A' 2)*(B 0)*(B 1)*(B' 1)*(C 0)^2*(C' 1) - (A 2)^2*(A' 2)*(B 0)*(B 1)*(B' 1)*(C 0)*(C 1)*(C' 0) + (A 2)^2*(A' 2)*(B 1)^2*(B' 0)*(C 0)^2*(C' 1) + (A 2)^2*(A' 2)*(B 1)^2*(B' 1)*(C 0)^2*(C' 0)) * hA'B'C'

-- ============================================================
-- PART 5: Main Pappus Theorem
-- ============================================================

/-- **Pappus's Hexagon Theorem over any CommRing K**

    Given collinear A, B, C and A', B', C' (on respective projective lines),
    the three cross-join intersection points are collinear.

    Proof structure:
    1. Lagrange: Express P, Q, R as d_i·vector − d_j·vector
    2. pappus_det_multilinear: Reduce det(P,Q,R) to 4-term expression (ring, degree 6)
    3. pappus_core_identity: Show 4-term expression = 0 (CAS-proved, degree-9 coefficients)

    Note: Commutativity of K is essential — Pappus fails over non-commutative rings. -/
theorem pappus_K (A B C A' B' C' : Fin 3 → K)
    (hABC : collinear_K A B C)
    (hA'B'C' : collinear_K A' B' C') :
    collinear_K
      (cross3 (cross3 A B') (cross3 A' B))
      (cross3 (cross3 A C') (cross3 A' C))
      (cross3 (cross3 B C') (cross3 B' C)) := by
  unfold collinear_K at *
  -- Step 1: Apply Lagrange to express each cross-join as a linear combination
  -- P = cross(cross(A,B'), cross(A',B)) = det(A,B',B)·A' − det(A,B',A')·B
  have hP := lagrange_cross_K A B' A' B
  -- Q = cross(cross(A,C'), cross(A',C)) = det(A,C',C)·A' − det(A,C',A')·C
  have hQ := lagrange_cross_K A C' A' C
  -- R = cross(cross(B,C'), cross(B',C)) = det(B,C',C)·B' − det(B,C',B')·C
  have hR := lagrange_cross_K B C' B' C
  -- Rewrite P, Q, R using Lagrange identities
  rw [show cross3 (cross3 A B') (cross3 A' B) =
      fun i => (threeVecMat A B' B).det * A' i - (threeVecMat A B' A').det * B i from hP,
    show cross3 (cross3 A C') (cross3 A' C) =
      fun i => (threeVecMat A C' C).det * A' i - (threeVecMat A C' A').det * C i from hQ,
    show cross3 (cross3 B C') (cross3 B' C) =
      fun i => (threeVecMat B C' C).det * B' i - (threeVecMat B C' B').det * C i from hR]
  -- Step 2: Apply multilinear expansion with ABSTRACT d_i's (degree-6 ring identity)
  rw [pappus_det_multilinear
      (threeVecMat A B' B).det (threeVecMat A B' A').det
      (threeVecMat A C' C).det (threeVecMat A C' A').det
      (threeVecMat B C' C).det (threeVecMat B C' B').det
      A' B C B']
  -- Step 3: Apply the core Pappus identity
  exact pappus_core_identity A B C A' B' C' hABC hA'B'C'

-- ============================================================
-- PART 6: Corollaries for Specific Rings
-- ============================================================

/-- Pappus's Theorem over ℚ -/
theorem pappus_Q (A B C A' B' C' : Fin 3 → ℚ)
    (hABC : collinear_K A B C)
    (hA'B'C' : collinear_K A' B' C') :
    collinear_K
      (cross3 (cross3 A B') (cross3 A' B))
      (cross3 (cross3 A C') (cross3 A' C))
      (cross3 (cross3 B C') (cross3 B' C)) :=
  pappus_K A B C A' B' C' hABC hA'B'C'

/-- Pappus's Theorem over ℤ -/
theorem pappus_Z (A B C A' B' C' : Fin 3 → ℤ)
    (hABC : collinear_K A B C)
    (hA'B'C' : collinear_K A' B' C') :
    collinear_K
      (cross3 (cross3 A B') (cross3 A' B))
      (cross3 (cross3 A C') (cross3 A' C))
      (cross3 (cross3 B C') (cross3 B' C)) :=
  pappus_K A B C A' B' C' hABC hA'B'C'

/-- Pappus's Theorem over 𝔽_p -/
theorem pappus_Fp (p : ℕ) [Fact (Nat.Prime p)]
    (A B C A' B' C' : Fin 3 → ZMod p)
    (hABC : collinear_K A B C)
    (hA'B'C' : collinear_K A' B' C') :
    collinear_K
      (cross3 (cross3 A B') (cross3 A' B))
      (cross3 (cross3 A C') (cross3 A' C))
      (cross3 (cross3 B C') (cross3 B' C)) :=
  pappus_K A B C A' B' C' hABC hA'B'C'

-- ============================================================
-- PART 7: Desargues Theorem (Reproduced)
-- ============================================================

/-
## Desargues's Theorem via the Same Framework

For completeness, we reprove the Desargues forward direction using this infrastructure.
This demonstrates the unified nature of the algebraic approach.
-/

set_option maxHeartbeats 400000000 in
/-- **Desargues's Theorem — Forward Direction** (using Pappus infrastructure)

    If triangles (A,B,C) and (A',B',C') are perspective from a point
    (det(A×A', B×B', C×C') = 0), then they are perspective from a line
    (the three intersection points P, Q, R are collinear). -/
theorem desargues_forward_K (A B C A' B' C' : Fin 3 → K)
    (h_persp : (threeVecMat (cross3 A A') (cross3 B B') (cross3 C C')).det = 0) :
    collinear_K
      (cross3 (cross3 A B) (cross3 A' B'))
      (cross3 (cross3 B C) (cross3 B' C'))
      (cross3 (cross3 C A) (cross3 C' A')) := by
  unfold collinear_K
  set d1 := (threeVecMat A B B').det
  set d2 := (threeVecMat A B A').det
  set d3 := (threeVecMat B C C').det
  set d4 := (threeVecMat B C B').det
  set d5 := (threeVecMat C A A').det
  set d6 := (threeVecMat C A C').det
  rw [show cross3 (cross3 A B) (cross3 A' B') =
      fun i => d1 * A' i - d2 * B' i from lagrange_cross_K A B A' B',
    show cross3 (cross3 B C) (cross3 B' C') =
      fun i => d3 * B' i - d4 * C' i from lagrange_cross_K B C B' C',
    show cross3 (cross3 C A) (cross3 C' A') =
      fun i => d5 * C' i - d6 * A' i from lagrange_cross_K C A C' A']
  have hLHS : (threeVecMat
        (fun i => d1 * A' i - d2 * B' i)
        (fun i => d3 * B' i - d4 * C' i)
        (fun i => d5 * C' i - d6 * A' i)).det =
      (d1 * d3 * d5 - d2 * d4 * d6) * (threeVecMat A' B' C').det := by
    simp only [threeVecMat_det_explicit]; ring
  have hCore : d1 * d3 * d5 - d2 * d4 * d6 =
      (threeVecMat (cross3 A A') (cross3 B B') (cross3 C C')).det *
      (threeVecMat A B C).det := by
    unfold_let d1 d2 d3 d4 d5 d6
    simp only [threeVecMat_det_explicit, cross3_zero, cross3_one, cross3_two]; ring
  rw [hLHS, hCore, h_persp, zero_mul, zero_mul]

-- ============================================================
-- PART 8: Numerical Verification
-- ============================================================

/-
## Verified Pappus Configurations

We verify concrete instances of Pappus's theorem using `ring` (or `decide`)
without relying on pappus_K, so these are unconditional.
-/

section Verification

private def qvec (a b c : ℚ) : Fin 3 → ℚ := ![a, b, c]

/-
### Configuration 1: Standard affine configuration
  L₁: y = 0 line: A = (0,0,1), B = (1,0,1), C = (2,0,1)
  L₂: y = 1 line: A' = (0,1,1), B' = (1,1,1), C' = (2,1,1)
  Cross joins: P = AB'∩A'B, Q = AC'∩A'C, R = BC'∩B'C
-/

-- Both sets of points are collinear
example : collinear_K (qvec 0 0 1) (qvec 1 0 1) (qvec 2 0 1) := by
  unfold collinear_K threeVecMat
  simp [Matrix.det_fin_three, Matrix.of_apply, qvec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]

example : collinear_K (qvec 0 1 1) (qvec 1 1 1) (qvec 2 1 1) := by
  unfold collinear_K threeVecMat
  simp [Matrix.det_fin_three, Matrix.of_apply, qvec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]

-- Pappus conclusion holds (verified directly without pappus_K)
example : collinear_K
    (cross3 (cross3 (qvec 0 0 1) (qvec 1 1 1)) (cross3 (qvec 0 1 1) (qvec 1 0 1)))
    (cross3 (cross3 (qvec 0 0 1) (qvec 2 1 1)) (cross3 (qvec 0 1 1) (qvec 2 0 1)))
    (cross3 (cross3 (qvec 1 0 1) (qvec 2 1 1)) (cross3 (qvec 1 1 1) (qvec 2 0 1))) := by
  unfold collinear_K cross3 threeVecMat
  simp [Matrix.det_fin_three, Matrix.of_apply, qvec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  ring

/-
### Configuration 2: Bertrand/Chasles configuration
  A = (1,0,0), B = (0,1,0), C = (1,1,0) [det = 0: z=0 line]
  A' = (1,0,1), B' = (0,1,1), C' = (1,1,2) [det = 0: on another line]
-/

example : collinear_K (qvec 1 0 0) (qvec 0 1 0) (qvec 1 1 0) := by
  unfold collinear_K threeVecMat
  simp [Matrix.det_fin_three, Matrix.of_apply, qvec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]

example : collinear_K (qvec 1 0 1) (qvec 0 1 1) (qvec 1 1 2) := by
  unfold collinear_K threeVecMat
  simp [Matrix.det_fin_three, Matrix.of_apply, qvec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]

-- Pappus conclusion for Configuration 2
example : collinear_K
    (cross3 (cross3 (qvec 1 0 0) (qvec 0 1 1)) (cross3 (qvec 1 0 1) (qvec 0 1 0)))
    (cross3 (cross3 (qvec 1 0 0) (qvec 1 1 2)) (cross3 (qvec 1 0 1) (qvec 1 1 0)))
    (cross3 (cross3 (qvec 0 1 0) (qvec 1 1 2)) (cross3 (qvec 0 1 1) (qvec 1 1 0))) := by
  unfold collinear_K cross3 threeVecMat
  simp [Matrix.det_fin_three, Matrix.of_apply, qvec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  ring

/-
### Configuration 3: Symmetric configuration
  A = (1,2,1), B = (2,1,1), C = (3,3,2) [det = 0]
  A' = (1,0,1), B' = (0,1,1), C' = (1,1,2) [det = 0]
-/

example : collinear_K (qvec 1 2 1) (qvec 2 1 1) (qvec 3 3 2) := by
  unfold collinear_K threeVecMat
  simp [Matrix.det_fin_three, Matrix.of_apply, qvec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]

-- Pappus conclusion for Configuration 3
example : collinear_K
    (cross3 (cross3 (qvec 1 2 1) (qvec 0 1 1)) (cross3 (qvec 1 0 1) (qvec 2 1 1)))
    (cross3 (cross3 (qvec 1 2 1) (qvec 1 1 2)) (cross3 (qvec 1 0 1) (qvec 3 3 2)))
    (cross3 (cross3 (qvec 2 1 1) (qvec 1 1 2)) (cross3 (qvec 0 1 1) (qvec 3 3 2))) := by
  unfold collinear_K cross3 threeVecMat
  simp [Matrix.det_fin_three, Matrix.of_apply, qvec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  ring

end Verification

-- ============================================================
-- PART 9: Commutativity is Essential
-- ============================================================

/-
## Why Commutativity is Required for Pappus

The proof of `pappus_K` uses the `ring` tactic in `pappus_det_multilinear`,
which relies on commutativity of multiplication. Over a non-commutative ring,
the identity fails.

Classical theorem: A projective plane satisfies Pappus's theorem if and only if
it is coordinatizable by a field (commutative division ring).

Desargues's theorem, by contrast, holds over any division ring (commutative or not).
This is the algebraic significance of the Pappus-Desargues relationship:
  Pappus ↔ commutativity
  Desargues ↔ associativity (division ring structure)

The hierarchy: Fields ⊂ Division rings ⊂ Rings
              Pappus   Desargues
-/

end PappusTheoremOQ02
