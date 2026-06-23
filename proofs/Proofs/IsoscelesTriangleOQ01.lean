import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-
  Euclid I.5 — Original Proof Formalization (Pons Asinorum)

  This file formalizes the isosceles triangle theorem following Pappus of
  Alexandria's self-congruence proof. The companion file IsoscelesTriangle.lean
  proves the same result via direct Mathlib delegation; this file exposes the
  inner structure of the argument, relating the theorem to the symmetry of
  equal-norm vectors.

  ## Two Proofs of Euclid I.5

  **Euclid's original proof** (Elements I.5, c. 300 BCE):
    1. Extend AB beyond B to F, extend AC beyond C to G, with AF = AG
    2. Prove △AFC ≅ △AGB (SAS: AF=AG, ∠A shared, AC=AB)
    3. Prove △BFC ≅ △CGB (SSS using BF=CG, BC=CB, FC=GB from step 2)
    4. Subtract equal angles: ∠ABG−∠CBG = ∠ACF−∠BCF gives ∠ABC = ∠ACB

  **Pappus's proof** (c. 340 AD):
    - Triangle ABC ≅ Triangle ACB by SAS: AB=AC, ∠A=∠A, AC=AB
    - Therefore ∠ABC = ∠ACB (corresponding angles)

  ## Algebraic Realization in Lean

  Setting p = A −ᵥ B and q = A −ᵥ C (the "apex vectors" from each base vertex
  back to the apex), the hypothesis dist A B = dist A C gives ‖p‖ = ‖q‖. Since:
    - C −ᵥ B = p − q   (vsub cancellation + negation)
    - B −ᵥ C = q − p   (negation of above)

  we have:
    ∠ABC = angle(A−ᵥB, C−ᵥB) = angle(p, p−q)
    ∠ACB = angle(A−ᵥC, B−ᵥC) = angle(q, q−p)

  And Mathlib's InnerProductGeometry.angle_sub_eq_angle_sub_rev_of_norm_eq
  proves exactly angle(p, p−q) = angle(q, q−p) when ‖p‖ = ‖q‖. This is
  the inner product space realization of Pappus's SAS argument.
-/

namespace IsoscelesTriangleOQ01

open EuclideanGeometry InnerProductGeometry

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

-- ============================================================================
-- Auxiliary Lemmas: vsub Arithmetic
-- ============================================================================

/-- The "apex-relative" decomposition of the base vector:
    C −ᵥ B = (A −ᵥ B) − (A −ᵥ C)

    Geometrically: the vector from B to C equals the difference of the two vectors
    from the base vertices to the apex A. This is the key structural observation
    in Pappus's proof: the base vector lies in the span of the two apex vectors. -/
private lemma vsub_eq_apex_diff (A B C : P) :
    (C -ᵥ B : V) = (A -ᵥ B) - (A -ᵥ C) := by
  have step1 : (C -ᵥ B : V) = (C -ᵥ A) + (A -ᵥ B) :=
    (vsub_add_vsub_cancel C A B).symm
  have step2 : (C -ᵥ A : V) = -(A -ᵥ C) :=
    (neg_vsub_eq_vsub_rev A C).symm
  rw [step1, step2]; abel

/-- The negated base vector: B −ᵥ C = (A −ᵥ C) − (A −ᵥ B) -/
private lemma vsub_neg_eq_apex_diff (A B C : P) :
    (B -ᵥ C : V) = (A -ᵥ C) - (A -ᵥ B) := by
  rw [show (B -ᵥ C : V) = -(C -ᵥ B) from (neg_vsub_eq_vsub_rev C B).symm,
      vsub_eq_apex_diff A B C]
  abel

-- ============================================================================
-- Main Theorem: Pappus's Proof of Pons Asinorum
-- ============================================================================

/-- **Euclid I.5 via Pappus's Self-Congruence** (Pons Asinorum)

    In an isosceles triangle ABC with dist A B = dist A C, the base angles satisfy
    ∠ A B C = ∠ A C B.

    **Proof**: Pappus (c. 340 AD) observed that triangle ABC is congruent to
    triangle ACB by SAS: (i) AB = AC, (ii) ∠BAC = ∠CAB (same angle), (iii) AC = AB.
    The corresponding angles ∠ABC and ∠ACB are therefore equal.

    In Lean's inner product framework, this is the identity
    angle(p, p−q) = angle(q, q−p) for equal-norm vectors p = A−ᵥB, q = A−ᵥC,
    proved by InnerProductGeometry.angle_sub_eq_angle_sub_rev_of_norm_eq. -/
theorem pappus_isosceles {A B C : P} (h : dist A B = dist A C) :
    ∠ A B C = ∠ A C B := by
  -- Unfold EuclideanGeometry.angle to InnerProductGeometry.angle
  show InnerProductGeometry.angle (A -ᵥ B) (C -ᵥ B) =
       InnerProductGeometry.angle (A -ᵥ C) (B -ᵥ C)
  -- Express base vectors as differences of apex vectors
  rw [vsub_eq_apex_diff A B C, vsub_neg_eq_apex_diff A B C]
  -- Apply Pappus's angle symmetry for equal-norm vectors
  apply InnerProductGeometry.angle_sub_eq_angle_sub_rev_of_norm_eq
  -- Convert dist hypothesis to norm hypothesis
  simpa only [← dist_eq_norm_vsub] using h

-- ============================================================================
-- Euclid's Original Auxiliary Construction (Documented)
-- ============================================================================

/-
  The following lemma documents Euclid's original first step: given auxiliary
  points F and G beyond B and C (with AF = AG), the "outer segments" BF and CG
  are equal. This corresponds to Step 1 of Euclid's four-step proof.

  In Lean's affine space framework, the auxiliary points are parameterized as
  F = A +ᵥ (t • (B −ᵥ A)) for t > 1 (placing F beyond B on the ray from A).
-/

/-- **Euclid's Outer Segment Equality** (Step 1 of Euclid I.5):
    With AF = AG and AB = AC, the outer segments satisfy BF = CG.

    If F = A + s*(B−A) and G = A + t*(C−A) are on extensions of AB and AC
    respectively, with AF = s·AB and AG = t·AC, and AF = AG, then since
    AB = AC we get s = t and therefore BF = (s−1)·AB = (t−1)·AC = CG. -/
lemma euclid_outer_segs_eq {A B C : P} (s t : ℝ)
    (_hs : 1 < s) (_ht : 1 < t)
    (hAB_eq_AC : dist A B = dist A C)
    (hAF_eq_AG : s * dist A B = t * dist A C) :
    (s - 1) * dist A B = (t - 1) * dist A C := by
  have key : s * dist A B = t * dist A B := hAB_eq_AC ▸ hAF_eq_AG
  calc (s - 1) * dist A B = s * dist A B - dist A B := by ring
    _ = t * dist A B - dist A B := by rw [key]
    _ = (t - 1) * dist A B := by ring
    _ = (t - 1) * dist A C := by rw [hAB_eq_AC]

-- ============================================================================
-- Summary
-- ============================================================================

/-- Pons Asinorum (Euclid I.5): identical to pappus_isosceles, exposed under
    Euclid's name for documentation purposes. -/
theorem euclid_i5 {A B C : P} (h : dist A B = dist A C) :
    ∠ A B C = ∠ A C B :=
  pappus_isosceles h

#check @pappus_isosceles
#check @euclid_i5

end IsoscelesTriangleOQ01
