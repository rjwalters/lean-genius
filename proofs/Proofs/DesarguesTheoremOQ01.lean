import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-
# Desargues's Theorem Over Arbitrary Commutative Rings

## Open Question
Can the full algebraic proof of Desargues's theorem be completed without sorries
using Mathlib's linear algebra?

## Answer: YES — and it generalizes to any commutative ring

The existing DesarguesTheorem.lean uses Mathlib's crossProduct notation which was
deprecated in Mathlib 4.26.0, so it no longer builds. This file proves Desargues
over ANY commutative ring K using a custom cross product definition and a structured
algebraic proof.

## Proof Strategy

1. **Lagrange identity**: cross(cross(A,B), cross(A',B')) = det(A,B,B')·A' − det(A,B,A')·B'
   → Expresses intersection points P, Q, R as linear combinations of A', B', C'

2. **Multilinearity**: det(d1·A'−d2·B', d3·B'−d4·C', d5·C'−d6·A')
                     = (d1·d3·d5 − d2·d4·d6) · det(A',B',C')
   → Computes det(P,Q,R) in terms of 6 scalar determinants

3. **Core identity** (degree-9 ring proof):
   d1·d3·d5 − d2·d4·d6 = det(A×A', B×B', C×C') · det(A,B,C)
   → Connects the scalar product to the perspectivity determinant

4. **Conclusion**: det(P,Q,R) = det(AA',BB',CC') · det(A,B,C) · det(A',B',C')

## Status
- [x] Complete proof (no sorries)
- [x] Works over arbitrary CommRing (forward direction)
- [x] Works over IntegralDomain (converse)
- [x] Forward direction over ℚ, ℤ, 𝔽_p as immediate corollaries
-/

namespace DesarguesTheoremOQ01

open Matrix

variable {K : Type*} [CommRing K]

-- ============================================================
-- PART 1: Cross Product Setup over K
-- ============================================================

/-- The cross product of two vectors in K³, defined componentwise. -/
def cross3 (a b : Fin 3 → K) : Fin 3 → K :=
  fun i => match i with
    | 0 => a 1 * b 2 - a 2 * b 1
    | 1 => a 2 * b 0 - a 0 * b 2
    | 2 => a 0 * b 1 - a 1 * b 0

theorem cross3_zero (a b : Fin 3 → K) : cross3 a b 0 = a 1 * b 2 - a 2 * b 1 := rfl
theorem cross3_one  (a b : Fin 3 → K) : cross3 a b 1 = a 2 * b 0 - a 0 * b 2 := rfl
theorem cross3_two  (a b : Fin 3 → K) : cross3 a b 2 = a 0 * b 1 - a 1 * b 0 := rfl

theorem cross3_self (a : Fin 3 → K) : cross3 a a = 0 := by
  ext i; fin_cases i <;> simp [cross3] <;> ring

theorem cross3_anticomm (a b : Fin 3 → K) : cross3 a b = -cross3 b a := by
  ext i; fin_cases i <;> simp [cross3] <;> ring

/-- The 3×3 matrix formed by three vectors as rows over K. -/
def threeVecMat (u v w : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j =>
    match i with
    | 0 => u j
    | 1 => v j
    | 2 => w j

/-- Determinant of threeVecMat expanded explicitly. -/
theorem threeVecMat_det_explicit (u v w : Fin 3 → K) :
    (threeVecMat u v w).det =
      u 0 * (v 1 * w 2 - v 2 * w 1) -
      u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0) := by
  simp only [threeVecMat, Matrix.det_fin_three, Matrix.of_apply]
  ring

-- ============================================================
-- PART 2: Key Algebraic Lemmas
-- ============================================================

set_option maxHeartbeats 400000000 in
/-- **Lagrange Cross Product Identity over any CommRing K**

(a×b)×(c×d) = det(a,b,d)·c − det(a,b,c)·d

This is the vector quadruple product formula. It expresses the
intersection point of two lines as a linear combination of two
reference vectors with determinant coefficients.

Proved by ring on degree-4 polynomial in 12 variables. -/
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
-- PART 3: Collinearity and Concurrence over K
-- ============================================================

def collinear_K (p q r : Fin 3 → K) : Prop :=
  (threeVecMat p q r).det = 0

def concurrent_K (l m n : Fin 3 → K) : Prop :=
  (threeVecMat l m n).det = 0

-- ============================================================
-- PART 4: The Desargues Identity Over K
-- ============================================================

/-
## Proof of the Core Desargues Identity

The proof proceeds in three steps:

**Step 1 (Lagrange):** Express P, Q, R using the Lagrange identity:
  P = (A×B)×(A'×B') = d1·A' − d2·B'   where d1=det(A,B,B'), d2=det(A,B,A')
  Q = (B×C)×(B'×C') = d3·B' − d4·C'   where d3=det(B,C,C'), d4=det(B,C,B')
  R = (C×A)×(C'×A') = d5·C' − d6·A'   where d5=det(C,A,A'), d6=det(C,A,C')

**Step 2 (Multilinearity):** Compute det(P,Q,R):
  det(d1·A'−d2·B', d3·B'−d4·C', d5·C'−d6·A')
  = (d1·d3·d5 − d2·d4·d6) · det(A',B',C')
  [Proved by ring as a polynomial identity in {d1,...,d6, A'₀,...,C'₂}]

**Step 3 (Core identity):** Connect to the perspectivity determinant:
  d1·d3·d5 − d2·d4·d6 = det(A×A', B×B', C×C') · det(A,B,C)
  [Proved by degree-9 ring call after expanding all determinants to coordinates]

**Conclusion:**
  det(P,Q,R) = det(A×A', B×B', C×C') · det(A,B,C) · det(A',B',C')
-/

set_option maxHeartbeats 400000000 in
/-- **The Desargues Identity over any CommRing K**

det(P,Q,R) = det(AA', BB', CC') · det(A,B,C) · det(A',B',C')

where P = (AB ∩ A'B'), Q = (BC ∩ B'C'), R = (CA ∩ C'A') are the
three intersection points of corresponding sides. -/
theorem desargues_identity_K (A B C A' B' C' : Fin 3 → K) :
    (threeVecMat
        (cross3 (cross3 A B) (cross3 A' B'))
        (cross3 (cross3 B C) (cross3 B' C'))
        (cross3 (cross3 C A) (cross3 C' A'))).det =
      (threeVecMat (cross3 A A') (cross3 B B') (cross3 C C')).det *
      ((threeVecMat A B C).det * (threeVecMat A' B' C').det) := by
  -- Name the 6 scalar determinants
  set d1 := (threeVecMat A B B').det with hd1
  set d2 := (threeVecMat A B A').det with hd2
  set d3 := (threeVecMat B C C').det with hd3
  set d4 := (threeVecMat B C B').det with hd4
  set d5 := (threeVecMat C A A').det with hd5
  set d6 := (threeVecMat C A C').det with hd6
  -- Step 1: Lagrange identities give intersection points as linear combinations
  have hP : cross3 (cross3 A B) (cross3 A' B') = fun i => d1 * A' i - d2 * B' i :=
    lagrange_cross_K A B A' B'
  have hQ : cross3 (cross3 B C) (cross3 B' C') = fun i => d3 * B' i - d4 * C' i :=
    lagrange_cross_K B C B' C'
  have hR : cross3 (cross3 C A) (cross3 C' A') = fun i => d5 * C' i - d6 * A' i :=
    lagrange_cross_K C A C' A'
  -- Step 2: Multilinearity of det reduces to a scalar factor times det(A',B',C')
  have hLHS : (threeVecMat
        (fun i => d1 * A' i - d2 * B' i)
        (fun i => d3 * B' i - d4 * C' i)
        (fun i => d5 * C' i - d6 * A' i)).det =
      (d1 * d3 * d5 - d2 * d4 * d6) * (threeVecMat A' B' C').det := by
    simp only [threeVecMat_det_explicit]
    ring
  -- Step 3: Core algebraic identity (degree-9 polynomial)
  -- d1·d3·d5 − d2·d4·d6 = det(AA', BB', CC') · det(A,B,C)
  have hCore : d1 * d3 * d5 - d2 * d4 * d6 =
      (threeVecMat (cross3 A A') (cross3 B B') (cross3 C C')).det *
      (threeVecMat A B C).det := by
    simp only [hd1, hd2, hd3, hd4, hd5, hd6,
               threeVecMat_det_explicit, cross3_zero, cross3_one, cross3_two]
    ring
  -- Conclude: det(P,Q,R) = det(AA',BB',CC') · det(A,B,C) · det(A',B',C')
  rw [hP, hQ, hR, hLHS, hCore]
  ring

-- ============================================================
-- PART 5: Main Theorems
-- ============================================================

def perspectiveFromPoint_K (A B C A' B' C' : Fin 3 → K) : Prop :=
  concurrent_K (cross3 A A') (cross3 B B') (cross3 C C')

def perspectiveFromLine_K (A B C A' B' C' : Fin 3 → K) : Prop :=
  collinear_K
    (cross3 (cross3 A B) (cross3 A' B'))
    (cross3 (cross3 B C) (cross3 B' C'))
    (cross3 (cross3 C A) (cross3 C' A'))

/-- **Desargues's Theorem — Forward Direction — over any CommRing K**

If two triangles are in perspective from a point, then they are in perspective from a line. -/
theorem desargues_forward_K (A B C A' B' C' : Fin 3 → K)
    (h : perspectiveFromPoint_K A B C A' B' C') :
    perspectiveFromLine_K A B C A' B' C' := by
  unfold perspectiveFromLine_K collinear_K
  unfold perspectiveFromPoint_K concurrent_K at h
  rw [desargues_identity_K, h, zero_mul]

/-- The non-degeneracy factor: det(A,B,C) · det(A',B',C').
    Zero iff at least one triangle is degenerate (collinear vertices). -/
def desargues_K_factor (A B C A' B' C' : Fin 3 → K) : K :=
  (threeVecMat A B C).det * (threeVecMat A' B' C').det

theorem desargues_identity_K' (A B C A' B' C' : Fin 3 → K) :
    (threeVecMat
        (cross3 (cross3 A B) (cross3 A' B'))
        (cross3 (cross3 B C) (cross3 B' C'))
        (cross3 (cross3 C A) (cross3 C' A'))).det =
      (threeVecMat (cross3 A A') (cross3 B B') (cross3 C C')).det *
      desargues_K_factor A B C A' B' C' :=
  desargues_identity_K A B C A' B' C'

/-- **Desargues's Theorem — Converse — over any IntegralDomain K**

If two non-degenerate triangles are in perspective from a line, then they are
in perspective from a point. The non-degeneracy condition ensures the factor
det(A,B,C)·det(A',B',C') is nonzero. -/
theorem desargues_converse_K [IsDomain K] (A B C A' B' C' : Fin 3 → K)
    (hline : perspectiveFromLine_K A B C A' B' C')
    (hK : desargues_K_factor A B C A' B' C' ≠ 0) :
    perspectiveFromPoint_K A B C A' B' C' := by
  unfold perspectiveFromPoint_K concurrent_K
  unfold perspectiveFromLine_K collinear_K at hline
  rw [desargues_identity_K'] at hline
  exact (mul_eq_zero.mp hline).elim id (absurd · hK)

/-- **Desargues's Theorem — Biconditional — over IntegralDomains**

For non-degenerate triangles (det(A,B,C)·det(A',B',C') ≠ 0), the two triangles
are in perspective from a point if and only if they are in perspective from a line. -/
theorem desargues_iff_K [IsDomain K] (A B C A' B' C' : Fin 3 → K)
    (hK : desargues_K_factor A B C A' B' C' ≠ 0) :
    perspectiveFromPoint_K A B C A' B' C' ↔ perspectiveFromLine_K A B C A' B' C' :=
  ⟨desargues_forward_K A B C A' B' C', fun h => desargues_converse_K A B C A' B' C' h hK⟩

-- ============================================================
-- PART 6: Corollaries for Specific Rings
-- ============================================================

theorem desargues_forward_Q (A B C A' B' C' : Fin 3 → ℚ)
    (h : perspectiveFromPoint_K A B C A' B' C') :
    perspectiveFromLine_K A B C A' B' C' :=
  desargues_forward_K A B C A' B' C' h

theorem desargues_forward_Z (A B C A' B' C' : Fin 3 → ℤ)
    (h : perspectiveFromPoint_K A B C A' B' C') :
    perspectiveFromLine_K A B C A' B' C' :=
  desargues_forward_K A B C A' B' C' h

theorem desargues_forward_Fp (p : ℕ) [Fact (Nat.Prime p)]
    (A B C A' B' C' : Fin 3 → ZMod p)
    (h : perspectiveFromPoint_K A B C A' B' C') :
    perspectiveFromLine_K A B C A' B' C' :=
  desargues_forward_K A B C A' B' C' h

theorem desargues_forward_poly (A B C A' B' C' : Fin 3 → Polynomial K)
    (h : perspectiveFromPoint_K A B C A' B' C') :
    perspectiveFromLine_K A B C A' B' C' :=
  desargues_forward_K A B C A' B' C' h

end DesarguesTheoremOQ01
