import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic

/-
# Hyperbolic AAA Congruence — Angles Determine the Triangle

## Research Problem: law-of-cosines-oq-03-oq-03

A follow-up to the Hyperbolic Law of Cosines (`law-of-cosines-oq-03`) and the
Hyperbolic Law of Sines (`law-of-cosines-oq-03-oq-02`).

## Open Question

In Euclidean geometry, knowing the three angles A, B, C of a triangle does **not**
determine its size — there are infinitely many similar triangles. What happens in
hyperbolic geometry?

## Answer: AAA congruence holds

The **second hyperbolic law of cosines**

  cos C = -cos A · cos B + sin A · sin B · cosh c

can be **inverted** to express each side purely in terms of the three angles:

  cosh c = (cos C + cos A · cos B) / (sin A · sin B)

(and symmetrically for cosh a, cosh b). Since `cosh` is injective on `[0, ∞)`, the
three angles *determine the three sides*. Two hyperbolic triangles with the same
angles are congruent — there are **no non-trivial similar triangles** in hyperbolic
geometry.

Two further consequences are formalized here:

* **Internal consistency.** The angle formula `(cos C + cos A cos B)/(sin A sin B)`
  exceeds `1` *exactly because* of the angular defect `A + B + C < π`. The defect is
  what makes the formula yield a valid value `cosh c > 1`. This connects the defect
  (= area) directly to the existence of the side.

* **Equilateral closed form.** For an equilateral hyperbolic triangle with common
  angle θ, every side satisfies `cosh(side) = cos θ / (1 - cos θ)`.

## Status (0 sorries; structure-encoded geometric assumptions)

The three second-law-of-cosines relations are encoded as structure fields (assumptions
about a hyperbolic triangle, exactly as in the parent `law-of-cosines-oq-03`), together
with strict side positivity `a, b, c > 0`. All theorems below are derived from those
assumptions with no additional axioms and no sorries.

The angular defect `A + B + C < π` is **not** a structure field: it is proved as
`HyperbolicTriangle.defect` from the three laws and side positivity, reducing the
structural-assumption count from 7 to 6 (see PART 1b).

## References
- Ratcliffe (2006): "Foundations of Hyperbolic Manifolds", Ch. 3 (AAA congruence)
- Thurston (1997): "Three-Dimensional Geometry and Topology"
-/

set_option linter.unusedVariables false

namespace HyperbolicAAA

open Real Set

-- ============================================================
-- A hyperbolic triangle via its angles and the second law of cosines
-- ============================================================

/-- A hyperbolic triangle, specified by its three side lengths `a, b, c` and the
    three opposite angles `A, B, C`. The geometric content is encoded in the three
    **second laws of cosines** (one per angle). These are the same kind of
    structure-encoded assumptions used in the parent `law-of-cosines-oq-03`.

    The angular defect `A + B + C < π` is **not** assumed as a field: it is *derived*
    from the three laws together with strict side positivity (`ha, hb, hc`) — see
    `HyperbolicTriangle.defect` below. This drops the structural-assumption count from
    7 to 6. -/
structure HyperbolicTriangle where
  a : ℝ
  b : ℝ
  c : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  hA : 0 < A
  hB : 0 < B
  hC : 0 < C
  hA_lt : A < Real.pi
  hB_lt : B < Real.pi
  hC_lt : C < Real.pi
  /-- Second law of cosines at vertex A. -/
  lawA : Real.cos A = -Real.cos B * Real.cos C + Real.sin B * Real.sin C * Real.cosh a
  /-- Second law of cosines at vertex B. -/
  lawB : Real.cos B = -Real.cos A * Real.cos C + Real.sin A * Real.sin C * Real.cosh b
  /-- Second law of cosines at vertex C. -/
  lawC : Real.cos C = -Real.cos A * Real.cos B + Real.sin A * Real.sin B * Real.cosh c

-- ============================================================
-- PART 1: Angles are strictly between 0 and π ⟹ sines are positive
-- ============================================================

theorem sin_A_pos (t : HyperbolicTriangle) : 0 < Real.sin t.A :=
  Real.sin_pos_of_pos_of_lt_pi t.hA t.hA_lt

theorem sin_B_pos (t : HyperbolicTriangle) : 0 < Real.sin t.B :=
  Real.sin_pos_of_pos_of_lt_pi t.hB t.hB_lt

theorem sin_C_pos (t : HyperbolicTriangle) : 0 < Real.sin t.C :=
  Real.sin_pos_of_pos_of_lt_pi t.hC t.hC_lt

-- ============================================================
-- PART 1b: The angular defect is DERIVED, not assumed (7 → 6 assumptions)
-- ============================================================

/-- **Half-angle sign lemma.** If `cos P + cos Q > 0`, the half-sum and half-difference
    cosines have a positive product. Immediate from the sum-to-product identity
    `cos P + cos Q = 2 cos((P+Q)/2) cos((P-Q)/2)`. -/
private theorem cos_half_prod_pos {P Q : ℝ} (h : 0 < Real.cos P + Real.cos Q) :
    0 < Real.cos ((P + Q) / 2) * Real.cos ((P - Q) / 2) := by
  have e := Real.cos_add_cos P Q
  nlinarith [e, h]

/-- **The angular defect is a theorem, not an axiom.** For three angles each in `(0, π)`,
    the two numerator inequalities that side positivity forces (`cosh a, cosh c > 1`,
    equivalently `sin·sin < cos + cos·cos`) already imply `A + B + C < π`.

    Proof sketch. Writing `m = (A+B+C)/2`, the sum-to-product identity turns each numerator
    inequality into `cos m · cos(half-difference) > 0`. Since `m ∈ [π/2, 3π/2)` forces
    `cos m ≤ 0`, and the products are nonzero, `cos m < 0`; then both half-differences are
    negative, forcing `A+B−C > π` and `B+C−A > π`, whose sum gives `B > π` — impossible. -/
theorem defect_of_laws (A B C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAlt : A < Real.pi) (hBlt : B < Real.pi) (hClt : C < Real.pi)
    (hIC : Real.sin A * Real.sin B < Real.cos C + Real.cos A * Real.cos B)
    (hIA : Real.sin B * Real.sin C < Real.cos A + Real.cos B * Real.cos C) :
    A + B + C < Real.pi := by
  by_contra hcon
  push_neg at hcon  -- hcon : Real.pi ≤ A + B + C
  -- Recast the two inequalities in `0 < cos P + cos Q` form.
  have hPC : 0 < Real.cos (A + B) + Real.cos C := by rw [Real.cos_add]; linarith
  have hPA : 0 < Real.cos (B + C) + Real.cos A := by rw [Real.cos_add]; linarith
  -- Sum-to-product: positive products sharing the half-sum m = (A+B+C)/2.
  have qC := cos_half_prod_pos hPC
  have qA := cos_half_prod_pos hPA
  rw [show (B + C + A) / 2 = (A + B + C) / 2 by ring] at qA
  -- cos m ≤ 0 because m ∈ [π/2, 3π/2).
  have hm_lo : Real.pi / 2 ≤ (A + B + C) / 2 := by linarith
  have hm_hi : (A + B + C) / 2 ≤ Real.pi + Real.pi / 2 := by linarith
  have hcm_le : Real.cos ((A + B + C) / 2) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hm_lo hm_hi
  -- cos m ≠ 0 (else the product qC would vanish), hence cos m < 0.
  have hcm_ne : Real.cos ((A + B + C) / 2) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at qC; exact lt_irrefl 0 qC
  have hcm_neg : Real.cos ((A + B + C) / 2) < 0 := lt_of_le_of_ne hcm_le hcm_ne
  -- Both half-differences are therefore negative.
  have hu1_neg : Real.cos ((A + B - C) / 2) < 0 := by
    by_contra h; push_neg at h; nlinarith [qC, hcm_neg, h]
  have hu2_neg : Real.cos ((B + C - A) / 2) < 0 := by
    by_contra h; push_neg at h; nlinarith [qA, hcm_neg, h]
  -- Each negative half-difference cosine forces its argument past π/2.
  have harg1_lo : -(Real.pi / 2) ≤ (A + B - C) / 2 := by linarith
  have harg2_lo : -(Real.pi / 2) ≤ (B + C - A) / 2 := by linarith
  have hd1 : Real.pi / 2 < (A + B - C) / 2 := by
    by_contra h; push_neg at h
    exact absurd (Real.cos_nonneg_of_neg_pi_div_two_le_of_le harg1_lo h) (not_le.mpr hu1_neg)
  have hd2 : Real.pi / 2 < (B + C - A) / 2 := by
    by_contra h; push_neg at h
    exact absurd (Real.cos_nonneg_of_neg_pi_div_two_le_of_le harg2_lo h) (not_le.mpr hu2_neg)
  -- Adding: π < A+B−C and π < B+C−A give π < B, contradicting B < π.
  linarith [hd1, hd2, hBlt]

/-- **The angular defect** `A + B + C < π`, derived (not assumed) from the three second
    laws of cosines and strict side positivity. Since `cosh a, cosh c > 1` (each side is a
    genuine positive length), the second-law numerators dominate, and `defect_of_laws`
    closes the angle sum. This replaces the former `defect` structure field. -/
theorem HyperbolicTriangle.defect (t : HyperbolicTriangle) :
    t.A + t.B + t.C < Real.pi := by
  have hcc : 1 < Real.cosh t.c := Real.one_lt_cosh.mpr t.hc.ne'
  have hca : 1 < Real.cosh t.a := Real.one_lt_cosh.mpr t.ha.ne'
  have hsAB : 0 < Real.sin t.A * Real.sin t.B := mul_pos (sin_A_pos t) (sin_B_pos t)
  have hsBC : 0 < Real.sin t.B * Real.sin t.C := mul_pos (sin_B_pos t) (sin_C_pos t)
  have hIC : Real.sin t.A * Real.sin t.B < Real.cos t.C + Real.cos t.A * Real.cos t.B := by
    nlinarith [t.lawC, mul_lt_mul_of_pos_left hcc hsAB]
  have hIA : Real.sin t.B * Real.sin t.C < Real.cos t.A + Real.cos t.B * Real.cos t.C := by
    nlinarith [t.lawA, mul_lt_mul_of_pos_left hca hsBC]
  exact defect_of_laws t.A t.B t.C t.hA t.hB t.hC t.hA_lt t.hB_lt t.hC_lt hIC hIA

-- ============================================================
-- PART 2: Inverting the second law — each side as a function of the angles
-- ============================================================

/-- **Side `c` as a function of the angles.** Inverting the second law of cosines:

      cosh c = (cos C + cos A · cos B) / (sin A · sin B).

    The right-hand side depends only on the angles. -/
theorem cosh_c_eq (t : HyperbolicTriangle) :
    Real.cosh t.c =
      (Real.cos t.C + Real.cos t.A * Real.cos t.B) / (Real.sin t.A * Real.sin t.B) := by
  have hne : Real.sin t.A * Real.sin t.B ≠ 0 :=
    mul_ne_zero (sin_A_pos t).ne' (sin_B_pos t).ne'
  rw [eq_div_iff hne]
  linear_combination -t.lawC

/-- **Side `a` as a function of the angles.** -/
theorem cosh_a_eq (t : HyperbolicTriangle) :
    Real.cosh t.a =
      (Real.cos t.A + Real.cos t.B * Real.cos t.C) / (Real.sin t.B * Real.sin t.C) := by
  have hne : Real.sin t.B * Real.sin t.C ≠ 0 :=
    mul_ne_zero (sin_B_pos t).ne' (sin_C_pos t).ne'
  rw [eq_div_iff hne]
  linear_combination -t.lawA

/-- **Side `b` as a function of the angles.** -/
theorem cosh_b_eq (t : HyperbolicTriangle) :
    Real.cosh t.b =
      (Real.cos t.B + Real.cos t.A * Real.cos t.C) / (Real.sin t.A * Real.sin t.C) := by
  have hne : Real.sin t.A * Real.sin t.C ≠ 0 :=
    mul_ne_zero (sin_A_pos t).ne' (sin_C_pos t).ne'
  rw [eq_div_iff hne]
  linear_combination -t.lawB

-- ============================================================
-- PART 3: Internal consistency — the defect makes cosh > 1
-- ============================================================

/-- **The angular defect makes the angle formula valid.** Using only the angle bounds
    and the defect `A + B + C < π` (no reference to the side `c`), the formula for
    `cosh c` exceeds `1`:

      (cos C + cos A · cos B) / (sin A · sin B) > 1.

    The key step is `cos(A+B) > cos(π - C) = -cos C`, which holds precisely because the
    defect gives `A + B < π - C`. Thus the angular defect is exactly what guarantees a
    valid hyperbolic side exists. -/
theorem angle_formula_gt_one (t : HyperbolicTriangle) :
    1 < (Real.cos t.C + Real.cos t.A * Real.cos t.B) / (Real.sin t.A * Real.sin t.B) := by
  have hden : 0 < Real.sin t.A * Real.sin t.B := mul_pos (sin_A_pos t) (sin_B_pos t)
  rw [lt_div_iff₀ hden, one_mul]
  -- Goal: sin A · sin B < cos C + cos A · cos B.
  have hAB_pos : (0 : ℝ) ≤ t.A + t.B := by linarith [t.hA, t.hB]
  have hpi : Real.pi - t.C ≤ Real.pi := by linarith [t.hC]
  have hAB_lt : t.A + t.B < Real.pi - t.C := by linarith [t.defect]
  -- cos is strictly antitone on [0, π]:  A+B < π-C  ⟹  cos(π-C) < cos(A+B).
  have hlt : Real.cos (Real.pi - t.C) < Real.cos (t.A + t.B) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hAB_pos hpi hAB_lt
  rw [Real.cos_pi_sub, Real.cos_add] at hlt
  -- hlt : -cos C < cos A · cos B - sin A · sin B
  linarith

/-- **The hyperbolic side is genuine.** `cosh c > 1`, derived from the angle formula and
    the defect. (Consistent with `c > 0`, but proved here from the angles alone.) -/
theorem cosh_c_gt_one (t : HyperbolicTriangle) : 1 < Real.cosh t.c := by
  rw [cosh_c_eq t]
  exact angle_formula_gt_one t

-- ============================================================
-- PART 4: AAA congruence — equal angles force equal sides
-- ============================================================

/-- Each `cosh`-side is determined by the angles: triangles with equal angles have
    equal `cosh c`. -/
theorem cosh_c_determined (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C = t₂.C) :
    Real.cosh t₁.c = Real.cosh t₂.c := by
  rw [cosh_c_eq t₁, cosh_c_eq t₂, hA, hB, hC]

theorem cosh_a_determined (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C = t₂.C) :
    Real.cosh t₁.a = Real.cosh t₂.a := by
  rw [cosh_a_eq t₁, cosh_a_eq t₂, hA, hB, hC]

theorem cosh_b_determined (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C = t₂.C) :
    Real.cosh t₁.b = Real.cosh t₂.b := by
  rw [cosh_b_eq t₁, cosh_b_eq t₂, hA, hB, hC]

/-- The side itself (not just its `cosh`) is determined, since `cosh` is injective on
    `[0, ∞)` and side lengths are positive. -/
theorem c_determined (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C = t₂.C) :
    t₁.c = t₂.c :=
  Real.cosh_strictMonoOn.injOn (mem_Ici.mpr t₁.hc.le) (mem_Ici.mpr t₂.hc.le)
    (cosh_c_determined t₁ t₂ hA hB hC)

theorem a_determined (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C = t₂.C) :
    t₁.a = t₂.a :=
  Real.cosh_strictMonoOn.injOn (mem_Ici.mpr t₁.ha.le) (mem_Ici.mpr t₂.ha.le)
    (cosh_a_determined t₁ t₂ hA hB hC)

theorem b_determined (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C = t₂.C) :
    t₁.b = t₂.b :=
  Real.cosh_strictMonoOn.injOn (mem_Ici.mpr t₁.hb.le) (mem_Ici.mpr t₂.hb.le)
    (cosh_b_determined t₁ t₂ hA hB hC)

/-- **Hyperbolic AAA congruence.** Two hyperbolic triangles with the same three angles
    have the same three sides. Unlike Euclidean geometry, there are no non-trivial
    similar triangles: angles determine the triangle up to congruence. -/
theorem aaa_congruence (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C = t₂.C) :
    t₁.a = t₂.a ∧ t₁.b = t₂.b ∧ t₁.c = t₂.c :=
  ⟨a_determined t₁ t₂ hA hB hC, b_determined t₁ t₂ hA hB hC, c_determined t₁ t₂ hA hB hC⟩

-- ============================================================
-- PART 4a: Side–angle order WITHIN one triangle (greater angle ⟹ greater side)
-- ============================================================

/-- **Isosceles ⟸ equal angles.** Within a single hyperbolic triangle, two equal
    angles force the two opposite sides to be equal: the angle-only formulas for
    `cosh a` and `cosh b` coincide when `A = B`, and `cosh` is injective on `[0, ∞)`.
    The hyperbolic base-angles theorem, recovered from AAA-type inversion. -/
theorem isosceles_of_angle_eq (t : HyperbolicTriangle) (h : t.A = t.B) : t.a = t.b := by
  have hcosh : Real.cosh t.a = Real.cosh t.b := by
    rw [cosh_a_eq t, cosh_b_eq t, h]
  exact Real.cosh_strictMonoOn.injOn (mem_Ici.mpr t.ha.le) (mem_Ici.mpr t.hb.le) hcosh

/-- **Greater angle, greater side (single triangle).** Within one hyperbolic triangle,
    `A < B` forces `a < b`: the opposite side of the larger angle is strictly longer.
    This is the hyperbolic analogue of the Euclidean side–angle inequality.

    Proof: comparing the angle-only closed forms `cosh a` and `cosh b`, the sign of
    `cosh b − cosh a` factors (via `sin²+cos² = 1`) as
    `sin C · sin(B−A) · (cos C + cos(A+B))`.  The first factor is positive, the second
    positive since `A < B`, and the third positive by the angular defect
    (`angle_formula_gt_one`: `sin A sin B < cos C + cos A cos B`, i.e. `cos C + cos(A+B) > 0`).
    Hence `cosh a < cosh b`, and `cosh` is strictly monotone on `[0, ∞)`. -/
theorem side_lt_of_angle_lt (t : HyperbolicTriangle) (hAB : t.A < t.B) : t.a < t.b := by
  have hsA := sin_A_pos t
  have hsB := sin_B_pos t
  have hsC := sin_C_pos t
  -- Angular-defect fact: cos C + cos A cos B − sin A sin B > 0  (= cos C + cos (A+B) > 0).
  have hf := angle_formula_gt_one t
  rw [lt_div_iff₀ (mul_pos hsA hsB), one_mul] at hf
  have hkey :
      0 < Real.cos t.C + Real.cos t.A * Real.cos t.B - Real.sin t.A * Real.sin t.B := by
    linarith
  -- sin (B − A) > 0, in expanded form.
  have hsub : 0 < Real.sin (t.B - t.A) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [t.hB_lt, t.hA])
  have hsubcs : 0 < Real.sin t.B * Real.cos t.A - Real.cos t.B * Real.sin t.A := by
    rw [← Real.sin_sub]; exact hsub
  -- Compare cosh a and cosh b via the angle-only closed forms.
  have hcosh : Real.cosh t.a < Real.cosh t.b := by
    rw [cosh_a_eq t, cosh_b_eq t,
        div_lt_div_iff₀ (mul_pos hsB hsC) (mul_pos hsA hsC)]
    have pA := Real.sin_sq_add_cos_sq t.A
    have pB := Real.sin_sq_add_cos_sq t.B
    have hLpos :
        0 < (Real.cos t.B + Real.cos t.A * Real.cos t.C) * (Real.sin t.B * Real.sin t.C)
              - (Real.cos t.A + Real.cos t.B * Real.cos t.C) * (Real.sin t.A * Real.sin t.C) := by
      have hkeyid :
          (Real.cos t.B + Real.cos t.A * Real.cos t.C) * (Real.sin t.B * Real.sin t.C)
            - (Real.cos t.A + Real.cos t.B * Real.cos t.C) * (Real.sin t.A * Real.sin t.C)
            = Real.sin t.C * ((Real.sin t.B * Real.cos t.A - Real.cos t.B * Real.sin t.A)
                * (Real.cos t.C + Real.cos t.A * Real.cos t.B - Real.sin t.A * Real.sin t.B)) := by
        linear_combination (-(Real.sin t.C * Real.sin t.B * Real.cos t.B)) * pA
          + (Real.sin t.C * Real.sin t.A * Real.cos t.A) * pB
      rw [hkeyid]
      exact mul_pos hsC (mul_pos hsubcs hkey)
    linarith
  exact (Real.cosh_strictMonoOn.lt_iff_lt (mem_Ici.mpr t.ha.le) (mem_Ici.mpr t.hb.le)).mp hcosh

/-- **Relabeling a hyperbolic triangle by swapping vertices `A` and `B`** (fixing `C`).
    The three second-law-of-cosines fields are symmetric under `(A,a) ↔ (B,b)`
    (`lawA ↔ lawB`, `lawC` invariant up to commutativity), so the swap is again a valid
    `HyperbolicTriangle`.  It lets the `A`-vs-`B` ordering lemmas be applied with the two
    roles exchanged, without re-deriving the `cosh` comparison. -/
def HyperbolicTriangle.swapAB (t : HyperbolicTriangle) : HyperbolicTriangle where
  a := t.b; b := t.a; c := t.c
  A := t.B; B := t.A; C := t.C
  ha := t.hb; hb := t.ha; hc := t.hc
  hA := t.hB; hB := t.hA; hC := t.hC
  hA_lt := t.hB_lt; hB_lt := t.hA_lt; hC_lt := t.hC_lt
  lawA := t.lawB
  lawB := t.lawA
  lawC := by rw [t.lawC]; ring

/-- **Smaller angle, shorter side (the `B`-side companion).** `B < A` forces `b < a`,
    obtained from `side_lt_of_angle_lt` applied to the `A ↔ B` relabeling `swapAB`. -/
theorem side_gt_of_angle_gt (t : HyperbolicTriangle) (hBA : t.B < t.A) : t.b < t.a :=
  side_lt_of_angle_lt t.swapAB hBA

/-- **Converse side–angle inequality: shorter side ⟹ smaller opposite angle.** Within one
    hyperbolic triangle, `a < b` forces `A < B`. Together with `side_lt_of_angle_lt` this is
    the full order-equivalence `a < b ↔ A < B` (`side_lt_iff_angle_lt`). Proof by trichotomy on
    `A` vs `B`: equality would give `a = b` (`isosceles_of_angle_eq`) and `B < A` would give
    `b < a` (`side_gt_of_angle_gt`), both contradicting `a < b`. -/
theorem angle_lt_of_side_lt (t : HyperbolicTriangle) (hab : t.a < t.b) : t.A < t.B := by
  rcases lt_trichotomy t.A t.B with h | h | h
  · exact h
  · exact absurd (isosceles_of_angle_eq t h) (ne_of_lt hab)
  · exact absurd (side_gt_of_angle_gt t h) (not_lt.mpr hab.le)

/-- **Converse of the isosceles criterion: equal sides ⟹ equal opposite angles.**
    `a = b → A = B`, completing `isosceles_of_angle_eq` to the equivalence
    `a = b ↔ A = B` (`side_eq_iff_angle_eq`). Trichotomy on `A` vs `B`: either strict order
    would force the corresponding strict side inequality, contradicting `a = b`. -/
theorem angle_eq_of_side_eq (t : HyperbolicTriangle) (h : t.a = t.b) : t.A = t.B := by
  rcases lt_trichotomy t.A t.B with hlt | heq | hgt
  · exact absurd (side_lt_of_angle_lt t hlt) (by rw [h]; exact lt_irrefl _)
  · exact heq
  · exact absurd (side_gt_of_angle_gt t hgt) (by rw [h]; exact lt_irrefl _)

/-- **Hyperbolic side–angle order-equivalence (strict).** `a < b ↔ A < B`: the opposite side
    of the larger angle is strictly longer, and conversely. Packages `angle_lt_of_side_lt`
    with `side_lt_of_angle_lt`. -/
theorem side_lt_iff_angle_lt (t : HyperbolicTriangle) : t.a < t.b ↔ t.A < t.B :=
  ⟨angle_lt_of_side_lt t, side_lt_of_angle_lt t⟩

/-- **Hyperbolic side–angle equality-equivalence.** `a = b ↔ A = B`: a hyperbolic triangle is
    isosceles in two sides iff it is isosceles in the two opposite angles. -/
theorem side_eq_iff_angle_eq (t : HyperbolicTriangle) : t.a = t.b ↔ t.A = t.B :=
  ⟨angle_eq_of_side_eq t, isosceles_of_angle_eq t⟩

/-- **Hyperbolic side–angle order-equivalence (non-strict).** `a ≤ b ↔ A ≤ B`, the `≤`
    companion completing the order trio with `side_lt_iff_angle_lt` (`<`) and
    `side_eq_iff_angle_eq` (`=`). Immediate by splitting each `≤` into `<` or `=`. -/
theorem side_le_iff_angle_le (t : HyperbolicTriangle) : t.a ≤ t.b ↔ t.A ≤ t.B := by
  rw [le_iff_lt_or_eq, side_lt_iff_angle_lt, side_eq_iff_angle_eq, ← le_iff_lt_or_eq]

-- ============================================================
-- PART 4b: Angle–side monotonicity — a larger opposite angle forces a shorter side
-- ============================================================

/-- **Monotonicity of `cosh c` in the opposite angle `C`.** For two hyperbolic triangles
    sharing the angles `A` and `B` but with `t₁.C < t₂.C`, we have
    `cosh t₂.c < cosh t₁.c`. This is immediate from the inversion
    `cosh c = (cos C + cos A cos B)/(sin A sin B)`: the numerator is strictly antitone in
    `C` (since `cos` is antitone on `[0, π]`) while the positive denominator is unchanged. -/
theorem cosh_c_antitone_in_C (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C < t₂.C) :
    Real.cosh t₂.c < Real.cosh t₁.c := by
  have hden : 0 < Real.sin t₂.A * Real.sin t₂.B := mul_pos (sin_A_pos t₂) (sin_B_pos t₂)
  have hcos : Real.cos t₂.C < Real.cos t₁.C :=
    Real.cos_lt_cos_of_nonneg_of_le_pi t₁.hC.le t₂.hC_lt.le hC
  rw [cosh_c_eq t₁, cosh_c_eq t₂, hA, hB, div_lt_div_iff_of_pos_right hden]
  linarith [hcos]

/-- **Hyperbolic angle–side comparison.** Holding two angles fixed, increasing the third
    angle strictly *shortens* the opposite side: if `t₁.A = t₂.A`, `t₁.B = t₂.B` and
    `t₁.C < t₂.C`, then `t₂.c < t₁.c`. This refines AAA congruence into a strict
    monotonicity statement and is the hyperbolic analogue of the Euclidean "larger angle
    opposite longer side" — but here the correspondence is *reversed and quantitative*,
    because in hyperbolic geometry the side is a decreasing function of its opposite angle
    once the other two angles are pinned. -/
theorem side_antitone_in_angle (t₁ t₂ : HyperbolicTriangle)
    (hA : t₁.A = t₂.A) (hB : t₁.B = t₂.B) (hC : t₁.C < t₂.C) :
    t₂.c < t₁.c :=
  (Real.cosh_strictMonoOn.lt_iff_lt (mem_Ici.mpr t₂.hc.le) (mem_Ici.mpr t₁.hc.le)).mp
    (cosh_c_antitone_in_C t₁ t₂ hA hB hC)

-- ============================================================
-- PART 5: Equilateral closed form
-- ============================================================

/-- **Equilateral hyperbolic triangle.** If all three angles are equal to a common
    value θ (`= C`), then every side satisfies

      cosh(side) = cos θ / (1 - cos θ).

    This is a clean closed form: the side grows without bound as θ → 0 (thin, large
    triangles) and shrinks to 0 as θ → π/3 (the Euclidean limit, where the angle sum
    approaches π). -/
theorem equilateral_cosh (t : HyperbolicTriangle)
    (hAB : t.A = t.B) (hBC : t.B = t.C) :
    Real.cosh t.c = Real.cos t.C / (1 - Real.cos t.C) := by
  have hsC : Real.sin t.C ≠ 0 := (sin_C_pos t).ne'
  have hsq : Real.sin t.C * Real.sin t.C
      = (1 - Real.cos t.C) * (1 + Real.cos t.C) := by
    nlinarith [Real.sin_sq_add_cos_sq t.C]
  have hcos_ne : 1 - Real.cos t.C ≠ 0 := by
    intro hh
    apply hsC
    have : Real.sin t.C * Real.sin t.C = 0 := by rw [hsq, hh, zero_mul]
    exact mul_self_eq_zero.mp this
  rw [cosh_c_eq t, hAB, hBC, div_eq_div_iff (mul_ne_zero hsC hsC) hcos_ne, hsq]
  ring

-- ============================================================
-- PART 6: Re-exported geometric facts
-- ============================================================

/-- The hyperbolic angle sum is strictly less than π. -/
theorem angle_sum_lt_pi (t : HyperbolicTriangle) : t.A + t.B + t.C < Real.pi :=
  t.defect

/-- The angular defect (= area) is strictly positive. -/
theorem area_positive (t : HyperbolicTriangle) :
    0 < Real.pi - (t.A + t.B + t.C) := by
  linarith [t.defect]

-- ============================================================
-- PART 7: The equilateral triangle — angle bound and a concrete value
-- ============================================================

/-- **Equilateral angle bound.** An equilateral hyperbolic triangle (all three angles
    equal) has common angle strictly below `π/3`. This is the sharp hyperbolic
    counterpart of the Euclidean equilateral angle `π/3`: the angular defect
    `A + B + C < π` forces `3θ < π`, i.e. `θ < π/3`, and the closer `θ` is to `π/3`
    the smaller (more Euclidean) the triangle. -/
theorem equilateral_angle_lt_pi_third (t : HyperbolicTriangle)
    (hAB : t.A = t.B) (hBC : t.B = t.C) : t.C < Real.pi / 3 := by
  have h := t.defect
  rw [hAB, hBC] at h
  linarith

/-- **A concrete equilateral triangle.** The hyperbolic equilateral triangle whose
    three angles are all `π/4` has every side of length `arcosh (1 + √2)`:

      cosh(side) = cos(π/4) / (1 - cos(π/4)) = 1 + √2.

    (Since `π/4 < π/3`, this angle is admissible, and `1 + √2 > 1` confirms a genuine
    hyperbolic side.) A clean closed value obtained from `equilateral_cosh`. -/
theorem equilateral_pi_four_cosh (t : HyperbolicTriangle)
    (hAB : t.A = t.B) (hBC : t.B = t.C) (hC4 : t.C = Real.pi / 4) :
    Real.cosh t.c = 1 + Real.sqrt 2 := by
  rw [equilateral_cosh t hAB hBC, hC4, Real.cos_pi_div_four]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlt : Real.sqrt 2 < 2 := by nlinarith [hs, hs0]
  have hpos : (0 : ℝ) < 1 - Real.sqrt 2 / 2 := by linarith [hlt]
  rw [div_eq_iff hpos.ne']
  linear_combination (1 / 2 : ℝ) * hs

-- ============================================================
-- PART 8: The equilateral family — the side strictly decreases in the common angle
-- ============================================================

/-- **The equilateral side strictly decreases in the common angle (cosh form).**
    Two equilateral hyperbolic triangles with common angles `θ₁ < θ₂` satisfy
    `cosh(side₂) < cosh(side₁)`. Together with `equilateral_cosh` this shows the closed
    form `θ ↦ cos θ / (1 - cos θ)` is strictly decreasing across the admissible range
    `(0, π/3)`: the side blows up as `θ → 0` (thin, large triangles) and shrinks to `0`
    as `θ → π/3` (the Euclidean limit). Unlike PART 4b, which pins two angles and varies
    the third, this varies all three angles together along the equilateral family. -/
theorem equilateral_cosh_antitone (t₁ t₂ : HyperbolicTriangle)
    (h₁ : t₁.A = t₁.B) (h₁' : t₁.B = t₁.C)
    (h₂ : t₂.A = t₂.B) (h₂' : t₂.B = t₂.C)
    (hlt : t₁.C < t₂.C) :
    Real.cosh t₂.c < Real.cosh t₁.c := by
  have hcos : Real.cos t₂.C < Real.cos t₁.C :=
    Real.cos_lt_cos_of_nonneg_of_le_pi t₁.hC.le t₂.hC_lt.le hlt
  -- `1 - cos θ > 0` for `0 < θ < π`, since `cos θ < cos 0 = 1`.
  have hd₁ : 0 < 1 - Real.cos t₁.C := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) t₁.hC_lt.le t₁.hC
    rw [Real.cos_zero] at h; linarith
  have hd₂ : 0 < 1 - Real.cos t₂.C := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) t₂.hC_lt.le t₂.hC
    rw [Real.cos_zero] at h; linarith
  rw [equilateral_cosh t₁ h₁ h₁', equilateral_cosh t₂ h₂ h₂',
      div_lt_div_iff₀ hd₂ hd₁]
  nlinarith [hcos]

/-- **The equilateral side strictly decreases in the common angle.** With common angles
    `θ₁ < θ₂`, the second triangle has the strictly shorter side: `t₂.c < t₁.c`. This is
    the monotone hyperbolic counterpart of the Euclidean fact that all equilateral
    triangles are similar — here each admissible common angle pins down a *unique* size,
    refining the AAA congruence of PART 4 into a strict monotonicity along the family. -/
theorem equilateral_side_antitone (t₁ t₂ : HyperbolicTriangle)
    (h₁ : t₁.A = t₁.B) (h₁' : t₁.B = t₁.C)
    (h₂ : t₂.A = t₂.B) (h₂' : t₂.B = t₂.C)
    (hlt : t₁.C < t₂.C) :
    t₂.c < t₁.c :=
  (Real.cosh_strictMonoOn.lt_iff_lt (mem_Ici.mpr t₂.hc.le) (mem_Ici.mpr t₁.hc.le)).mp
    (equilateral_cosh_antitone t₁ t₂ h₁ h₁' h₂ h₂' hlt)

-- ============================================================
-- PART 9: The hyperbolic law of sines (from the second-law inversion)
-- ============================================================

/-- The common **Gram numerator** of a hyperbolic triangle. Expanding `cosh² - 1`
    after the inversion `cosh a = (cos A + cos B cos C)/(sin B sin C)` collapses to this
    fully symmetric expression in the three angles. Its symmetry is exactly what forces
    the law of sines: every side's `sinh` shares the same numerator. -/
noncomputable def gramNumerator (t : HyperbolicTriangle) : ℝ :=
  Real.cos t.A ^ 2 + Real.cos t.B ^ 2 + Real.cos t.C ^ 2
    + 2 * Real.cos t.A * Real.cos t.B * Real.cos t.C - 1

/-- Two positive reals with equal squares are equal. -/
private theorem eq_of_sq_eq_of_pos {x y : ℝ} (h : x ^ 2 = y ^ 2)
    (hx : 0 < x) (hy : 0 < y) : x = y := by
  have hfac : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h'
  · linarith
  · linarith [add_pos hx hy]

/-- Positivity of `sinh a` from positivity of the side `a`. -/
theorem sinh_a_pos (t : HyperbolicTriangle) : 0 < Real.sinh t.a := by
  have h := Real.sinh_strictMono t.ha
  rwa [Real.sinh_zero] at h

/-- Positivity of `sinh b`. -/
theorem sinh_b_pos (t : HyperbolicTriangle) : 0 < Real.sinh t.b := by
  have h := Real.sinh_strictMono t.hb
  rwa [Real.sinh_zero] at h

/-- Positivity of `sinh c`. -/
theorem sinh_c_pos (t : HyperbolicTriangle) : 0 < Real.sinh t.c := by
  have h := Real.sinh_strictMono t.hc
  rwa [Real.sinh_zero] at h

/-- **Gram numerator via side `a`.** `(sinh a · sin B · sin C)² = gramNumerator`.
    Squaring the side-from-angle inversion and using `sinh² = cosh² − 1`, the
    Pythagorean identities `sin² = 1 − cos²` collapse the result to the symmetric
    Gram numerator. -/
theorem sinh_a_num_sq (t : HyperbolicTriangle) :
    (Real.sinh t.a * (Real.sin t.B * Real.sin t.C)) ^ 2 = gramNumerator t := by
  have hne : Real.sin t.B * Real.sin t.C ≠ 0 :=
    mul_ne_zero (sin_B_pos t).ne' (sin_C_pos t).ne'
  have h1 : Real.cosh t.a * (Real.sin t.B * Real.sin t.C)
      = Real.cos t.A + Real.cos t.B * Real.cos t.C :=
    (eq_div_iff hne).mp (cosh_a_eq t)
  have h1sq : Real.cosh t.a ^ 2 * (Real.sin t.B ^ 2 * Real.sin t.C ^ 2)
      = (Real.cos t.A + Real.cos t.B * Real.cos t.C) ^ 2 := by
    have e : (Real.cosh t.a * (Real.sin t.B * Real.sin t.C)) ^ 2
        = Real.cosh t.a ^ 2 * (Real.sin t.B ^ 2 * Real.sin t.C ^ 2) := by ring
    rw [← e, h1]
  have hsinh : Real.sinh t.a ^ 2 = Real.cosh t.a ^ 2 - 1 := by
    have := Real.cosh_sq_sub_sinh_sq t.a; linarith
  have pB : Real.sin t.B ^ 2 = 1 - Real.cos t.B ^ 2 := by
    have := Real.sin_sq_add_cos_sq t.B; linarith
  have pC : Real.sin t.C ^ 2 = 1 - Real.cos t.C ^ 2 := by
    have := Real.sin_sq_add_cos_sq t.C; linarith
  calc (Real.sinh t.a * (Real.sin t.B * Real.sin t.C)) ^ 2
      = Real.sinh t.a ^ 2 * (Real.sin t.B ^ 2 * Real.sin t.C ^ 2) := by ring
    _ = (Real.cosh t.a ^ 2 - 1) * (Real.sin t.B ^ 2 * Real.sin t.C ^ 2) := by rw [hsinh]
    _ = Real.cosh t.a ^ 2 * (Real.sin t.B ^ 2 * Real.sin t.C ^ 2)
          - Real.sin t.B ^ 2 * Real.sin t.C ^ 2 := by ring
    _ = (Real.cos t.A + Real.cos t.B * Real.cos t.C) ^ 2
          - Real.sin t.B ^ 2 * Real.sin t.C ^ 2 := by rw [h1sq]
    _ = (Real.cos t.A + Real.cos t.B * Real.cos t.C) ^ 2
          - (1 - Real.cos t.B ^ 2) * (1 - Real.cos t.C ^ 2) := by rw [pB, pC]
    _ = gramNumerator t := by unfold gramNumerator; ring

/-- **Gram numerator via side `b`.** `(sinh b · sin A · sin C)² = gramNumerator`. -/
theorem sinh_b_num_sq (t : HyperbolicTriangle) :
    (Real.sinh t.b * (Real.sin t.A * Real.sin t.C)) ^ 2 = gramNumerator t := by
  have hne : Real.sin t.A * Real.sin t.C ≠ 0 :=
    mul_ne_zero (sin_A_pos t).ne' (sin_C_pos t).ne'
  have h1 : Real.cosh t.b * (Real.sin t.A * Real.sin t.C)
      = Real.cos t.B + Real.cos t.A * Real.cos t.C :=
    (eq_div_iff hne).mp (cosh_b_eq t)
  have h1sq : Real.cosh t.b ^ 2 * (Real.sin t.A ^ 2 * Real.sin t.C ^ 2)
      = (Real.cos t.B + Real.cos t.A * Real.cos t.C) ^ 2 := by
    have e : (Real.cosh t.b * (Real.sin t.A * Real.sin t.C)) ^ 2
        = Real.cosh t.b ^ 2 * (Real.sin t.A ^ 2 * Real.sin t.C ^ 2) := by ring
    rw [← e, h1]
  have hsinh : Real.sinh t.b ^ 2 = Real.cosh t.b ^ 2 - 1 := by
    have := Real.cosh_sq_sub_sinh_sq t.b; linarith
  have pA : Real.sin t.A ^ 2 = 1 - Real.cos t.A ^ 2 := by
    have := Real.sin_sq_add_cos_sq t.A; linarith
  have pC : Real.sin t.C ^ 2 = 1 - Real.cos t.C ^ 2 := by
    have := Real.sin_sq_add_cos_sq t.C; linarith
  calc (Real.sinh t.b * (Real.sin t.A * Real.sin t.C)) ^ 2
      = Real.sinh t.b ^ 2 * (Real.sin t.A ^ 2 * Real.sin t.C ^ 2) := by ring
    _ = (Real.cosh t.b ^ 2 - 1) * (Real.sin t.A ^ 2 * Real.sin t.C ^ 2) := by rw [hsinh]
    _ = Real.cosh t.b ^ 2 * (Real.sin t.A ^ 2 * Real.sin t.C ^ 2)
          - Real.sin t.A ^ 2 * Real.sin t.C ^ 2 := by ring
    _ = (Real.cos t.B + Real.cos t.A * Real.cos t.C) ^ 2
          - Real.sin t.A ^ 2 * Real.sin t.C ^ 2 := by rw [h1sq]
    _ = (Real.cos t.B + Real.cos t.A * Real.cos t.C) ^ 2
          - (1 - Real.cos t.A ^ 2) * (1 - Real.cos t.C ^ 2) := by rw [pA, pC]
    _ = gramNumerator t := by unfold gramNumerator; ring

/-- **Gram numerator via side `c`.** `(sinh c · sin A · sin B)² = gramNumerator`. -/
theorem sinh_c_num_sq (t : HyperbolicTriangle) :
    (Real.sinh t.c * (Real.sin t.A * Real.sin t.B)) ^ 2 = gramNumerator t := by
  have hne : Real.sin t.A * Real.sin t.B ≠ 0 :=
    mul_ne_zero (sin_A_pos t).ne' (sin_B_pos t).ne'
  have h1 : Real.cosh t.c * (Real.sin t.A * Real.sin t.B)
      = Real.cos t.C + Real.cos t.A * Real.cos t.B :=
    (eq_div_iff hne).mp (cosh_c_eq t)
  have h1sq : Real.cosh t.c ^ 2 * (Real.sin t.A ^ 2 * Real.sin t.B ^ 2)
      = (Real.cos t.C + Real.cos t.A * Real.cos t.B) ^ 2 := by
    have e : (Real.cosh t.c * (Real.sin t.A * Real.sin t.B)) ^ 2
        = Real.cosh t.c ^ 2 * (Real.sin t.A ^ 2 * Real.sin t.B ^ 2) := by ring
    rw [← e, h1]
  have hsinh : Real.sinh t.c ^ 2 = Real.cosh t.c ^ 2 - 1 := by
    have := Real.cosh_sq_sub_sinh_sq t.c; linarith
  have pA : Real.sin t.A ^ 2 = 1 - Real.cos t.A ^ 2 := by
    have := Real.sin_sq_add_cos_sq t.A; linarith
  have pB : Real.sin t.B ^ 2 = 1 - Real.cos t.B ^ 2 := by
    have := Real.sin_sq_add_cos_sq t.B; linarith
  calc (Real.sinh t.c * (Real.sin t.A * Real.sin t.B)) ^ 2
      = Real.sinh t.c ^ 2 * (Real.sin t.A ^ 2 * Real.sin t.B ^ 2) := by ring
    _ = (Real.cosh t.c ^ 2 - 1) * (Real.sin t.A ^ 2 * Real.sin t.B ^ 2) := by rw [hsinh]
    _ = Real.cosh t.c ^ 2 * (Real.sin t.A ^ 2 * Real.sin t.B ^ 2)
          - Real.sin t.A ^ 2 * Real.sin t.B ^ 2 := by ring
    _ = (Real.cos t.C + Real.cos t.A * Real.cos t.B) ^ 2
          - Real.sin t.A ^ 2 * Real.sin t.B ^ 2 := by rw [h1sq]
    _ = (Real.cos t.C + Real.cos t.A * Real.cos t.B) ^ 2
          - (1 - Real.cos t.A ^ 2) * (1 - Real.cos t.B ^ 2) := by rw [pA, pB]
    _ = gramNumerator t := by unfold gramNumerator; ring

/-- **The Gram numerator is nonnegative.** It equals a square, so a valid hyperbolic
    triangle always has `cos²A + cos²B + cos²C + 2 cos A cos B cos C ≥ 1`. -/
theorem gramNumerator_nonneg (t : HyperbolicTriangle) : 0 ≤ gramNumerator t := by
  rw [← sinh_a_num_sq t]; positivity

/-- **The Gram numerator is strictly positive.** Strengthening `gramNumerator_nonneg`: it
    equals `(sinh a · sin B · sin C)²`, whose base is a product of the strictly positive
    quantities `sinh a`, `sin B`, `sin C`, so the square is `> 0`. Thus a genuine hyperbolic
    triangle satisfies `cos²A + cos²B + cos²C + 2 cos A cos B cos C > 1` strictly — the
    inequality is never tight (tightness would force a degenerate side or a straight angle). -/
theorem gramNumerator_pos (t : HyperbolicTriangle) : 0 < gramNumerator t := by
  rw [← sinh_a_num_sq t]
  exact pow_pos (mul_pos (sinh_a_pos t) (mul_pos (sin_B_pos t) (sin_C_pos t))) 2

/-- **Hyperbolic law of sines, pair `a,b` (cross form).**
    `sinh a · sin B = sinh b · sin A`. Both `(sinh a · sin B · sin C)²` and
    `(sinh b · sin A · sin C)²` equal the Gram numerator; cancelling the common
    `sin² C` and taking the positive square root yields the identity. -/
theorem law_of_sines_ab (t : HyperbolicTriangle) :
    Real.sinh t.a * Real.sin t.B = Real.sinh t.b * Real.sin t.A := by
  have h : (Real.sinh t.a * (Real.sin t.B * Real.sin t.C)) ^ 2
      = (Real.sinh t.b * (Real.sin t.A * Real.sin t.C)) ^ 2 := by
    rw [sinh_a_num_sq, sinh_b_num_sq]
  have hsC : Real.sin t.C ^ 2 ≠ 0 := pow_ne_zero 2 (sin_C_pos t).ne'
  have hsq : (Real.sinh t.a * Real.sin t.B) ^ 2 = (Real.sinh t.b * Real.sin t.A) ^ 2 := by
    have e : (Real.sinh t.a * Real.sin t.B) ^ 2 * Real.sin t.C ^ 2
        = (Real.sinh t.b * Real.sin t.A) ^ 2 * Real.sin t.C ^ 2 := by linear_combination h
    exact mul_right_cancel₀ hsC e
  exact eq_of_sq_eq_of_pos hsq
    (mul_pos (sinh_a_pos t) (sin_B_pos t)) (mul_pos (sinh_b_pos t) (sin_A_pos t))

/-- **Hyperbolic law of sines, pair `b,c` (cross form).**
    `sinh b · sin C = sinh c · sin B`. -/
theorem law_of_sines_bc (t : HyperbolicTriangle) :
    Real.sinh t.b * Real.sin t.C = Real.sinh t.c * Real.sin t.B := by
  have h : (Real.sinh t.b * (Real.sin t.A * Real.sin t.C)) ^ 2
      = (Real.sinh t.c * (Real.sin t.A * Real.sin t.B)) ^ 2 := by
    rw [sinh_b_num_sq, sinh_c_num_sq]
  have hsA : Real.sin t.A ^ 2 ≠ 0 := pow_ne_zero 2 (sin_A_pos t).ne'
  have hsq : (Real.sinh t.b * Real.sin t.C) ^ 2 = (Real.sinh t.c * Real.sin t.B) ^ 2 := by
    have e : (Real.sinh t.b * Real.sin t.C) ^ 2 * Real.sin t.A ^ 2
        = (Real.sinh t.c * Real.sin t.B) ^ 2 * Real.sin t.A ^ 2 := by linear_combination h
    exact mul_right_cancel₀ hsA e
  exact eq_of_sq_eq_of_pos hsq
    (mul_pos (sinh_b_pos t) (sin_C_pos t)) (mul_pos (sinh_c_pos t) (sin_B_pos t))

/-- **Hyperbolic law of sines, pair `a,c` (cross form).**
    `sinh a · sin C = sinh c · sin A`. -/
theorem law_of_sines_ac (t : HyperbolicTriangle) :
    Real.sinh t.a * Real.sin t.C = Real.sinh t.c * Real.sin t.A := by
  have h : (Real.sinh t.a * (Real.sin t.B * Real.sin t.C)) ^ 2
      = (Real.sinh t.c * (Real.sin t.A * Real.sin t.B)) ^ 2 := by
    rw [sinh_a_num_sq, sinh_c_num_sq]
  have hsB : Real.sin t.B ^ 2 ≠ 0 := pow_ne_zero 2 (sin_B_pos t).ne'
  have hsq : (Real.sinh t.a * Real.sin t.C) ^ 2 = (Real.sinh t.c * Real.sin t.A) ^ 2 := by
    have e : (Real.sinh t.a * Real.sin t.C) ^ 2 * Real.sin t.B ^ 2
        = (Real.sinh t.c * Real.sin t.A) ^ 2 * Real.sin t.B ^ 2 := by linear_combination h
    exact mul_right_cancel₀ hsB e
  exact eq_of_sq_eq_of_pos hsq
    (mul_pos (sinh_a_pos t) (sin_C_pos t)) (mul_pos (sinh_c_pos t) (sin_A_pos t))

/-- **The hyperbolic law of sines.** In any hyperbolic triangle the ratios of `sinh`
    of a side to the sine of its opposite angle agree:

      sinh a / sin A = sinh b / sin B = sinh c / sin C.

    This is the exact hyperbolic analogue of the Euclidean law of sines, obtained here
    as a corollary of the *second* law of cosines: the shared symmetric Gram numerator
    forces the three ratios to coincide. Together with the two laws of cosines already
    in this file it completes the elementary trigonometry of the hyperbolic triangle. -/
theorem hyperbolic_law_of_sines (t : HyperbolicTriangle) :
    Real.sinh t.a / Real.sin t.A = Real.sinh t.b / Real.sin t.B
      ∧ Real.sinh t.b / Real.sin t.B = Real.sinh t.c / Real.sin t.C := by
  have hA : Real.sin t.A ≠ 0 := (sin_A_pos t).ne'
  have hB : Real.sin t.B ≠ 0 := (sin_B_pos t).ne'
  have hC : Real.sin t.C ≠ 0 := (sin_C_pos t).ne'
  refine ⟨?_, ?_⟩
  · rw [div_eq_div_iff hA hB]; linear_combination law_of_sines_ab t
  · rw [div_eq_div_iff hB hC]; linear_combination law_of_sines_bc t

/-- **Hyperbolic law of sines, outer ratio `a,c`.** `sinh a / sin A = sinh c / sin C`, the
    remaining pair of the three equal ratios (`hyperbolic_law_of_sines` records the two
    adjacent equalities `a=b` and `b=c`; this is their transitive consequence, stated
    directly from `law_of_sines_ac` for convenience). -/
theorem hyperbolic_law_of_sines_ac (t : HyperbolicTriangle) :
    Real.sinh t.a / Real.sin t.A = Real.sinh t.c / Real.sin t.C := by
  have hA : Real.sin t.A ≠ 0 := (sin_A_pos t).ne'
  have hC : Real.sin t.C ≠ 0 := (sin_C_pos t).ne'
  rw [div_eq_div_iff hA hC]; linear_combination law_of_sines_ac t

-- ============================================================
-- PART 10: Realizability — the defect condition A+B+C<π is SUFFICIENT
-- ============================================================

/-- **The defect inequality.** For any three angles in `(0, π)` with positive angular
    defect `A + B + C < π`, the second-law numerator dominates: `sin A · sin B < cos C +
    cos A · cos B`. This is the raw-real form of the inequality inside
    `angle_formula_gt_one`, extracted so it can be applied to a *hypothetical* angle triple
    (before any triangle is known to exist). Only `C > 0` and the defect are needed. -/
theorem angle_ineq (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hdef : A + B + C < Real.pi) :
    Real.sin A * Real.sin B < Real.cos C + Real.cos A * Real.cos B := by
  have hAB_pos : (0 : ℝ) ≤ A + B := by linarith
  have hpi : Real.pi - C ≤ Real.pi := by linarith
  have hAB_lt : A + B < Real.pi - C := by linarith
  have hlt : Real.cos (Real.pi - C) < Real.cos (A + B) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hAB_pos hpi hAB_lt
  rw [Real.cos_pi_sub, Real.cos_add] at hlt
  linarith

/-- **Realizability: positive defect is sufficient.** Every angle triple with each angle in
    `(0, π)` and angle sum `< π` is realized by an actual hyperbolic triangle. This is the
    converse to `HyperbolicTriangle.defect` (which shows the defect is *necessary*).

    The construction is direct: because the three second laws are **decoupled** — the law at
    a vertex constrains only that vertex's opposite side — each side is defined independently
    by inverting its own law, `cosh a = (cos A + cos B cos C)/(sin B sin C)`, etc. The three
    angle inequalities (all instances of `angle_ineq` with the angles permuted, since the
    defect is symmetric) make each quotient exceed `1`, so `arcosh` returns a genuine positive
    length. -/
theorem exists_triangle_of_defect (A B C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAlt : A < Real.pi) (hBlt : B < Real.pi) (hClt : C < Real.pi)
    (hdef : A + B + C < Real.pi) :
    ∃ t : HyperbolicTriangle, t.A = A ∧ t.B = B ∧ t.C = C := by
  have hsA := Real.sin_pos_of_pos_of_lt_pi hA hAlt
  have hsB := Real.sin_pos_of_pos_of_lt_pi hB hBlt
  have hsC := Real.sin_pos_of_pos_of_lt_pi hC hClt
  have hsAne := hsA.ne'
  have hsBne := hsB.ne'
  have hsCne := hsC.ne'
  -- Three angle inequalities (the defect is symmetric in A, B, C).
  have hIa : Real.sin B * Real.sin C < Real.cos A + Real.cos B * Real.cos C :=
    angle_ineq B C A hB hC hA (by linarith)
  have hIb : Real.sin A * Real.sin C < Real.cos B + Real.cos A * Real.cos C :=
    angle_ineq A C B hA hC hB (by linarith)
  have hIc : Real.sin A * Real.sin B < Real.cos C + Real.cos A * Real.cos B :=
    angle_ineq A B C hA hB hC hdef
  -- Each inverted side value exceeds 1.
  have hva1 : 1 < (Real.cos A + Real.cos B * Real.cos C) / (Real.sin B * Real.sin C) := by
    rw [lt_div_iff₀ (mul_pos hsB hsC), one_mul]; exact hIa
  have hvb1 : 1 < (Real.cos B + Real.cos A * Real.cos C) / (Real.sin A * Real.sin C) := by
    rw [lt_div_iff₀ (mul_pos hsA hsC), one_mul]; exact hIb
  have hvc1 : 1 < (Real.cos C + Real.cos A * Real.cos B) / (Real.sin A * Real.sin B) := by
    rw [lt_div_iff₀ (mul_pos hsA hsB), one_mul]; exact hIc
  refine ⟨{ a := Real.arcosh ((Real.cos A + Real.cos B * Real.cos C) / (Real.sin B * Real.sin C))
            b := Real.arcosh ((Real.cos B + Real.cos A * Real.cos C) / (Real.sin A * Real.sin C))
            c := Real.arcosh ((Real.cos C + Real.cos A * Real.cos B) / (Real.sin A * Real.sin B))
            A := A, B := B, C := C
            ha := Real.arcosh_pos hva1
            hb := Real.arcosh_pos hvb1
            hc := Real.arcosh_pos hvc1
            hA := hA, hB := hB, hC := hC
            hA_lt := hAlt, hB_lt := hBlt, hC_lt := hClt
            lawA := by rw [Real.cosh_arcosh hva1.le]; field_simp; ring
            lawB := by rw [Real.cosh_arcosh hvb1.le]; field_simp; ring
            lawC := by rw [Real.cosh_arcosh hvc1.le]; field_simp; ring }, rfl, rfl, rfl⟩

/-- **Full realizability (bijection characterization).** A triple of angles, each in
    `(0, π)`, is realized by a hyperbolic triangle **iff** the angle sum is `< π`. The forward
    direction is `HyperbolicTriangle.defect`; the converse is `exists_triangle_of_defect`.
    Combined with the AAA congruence of PART 4, the map (angles) ↦ (triangle) is a bijection
    between the open defect region `{(A,B,C) : 0 < A,B,C < π, A+B+C < π}` and congruence
    classes of hyperbolic triangles — the exact hyperbolic replacement for the Euclidean
    angle-sum identity `A + B + C = π`. -/
theorem exists_iff_defect (A B C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAlt : A < Real.pi) (hBlt : B < Real.pi) (hClt : C < Real.pi) :
    (∃ t : HyperbolicTriangle, t.A = A ∧ t.B = B ∧ t.C = C) ↔ A + B + C < Real.pi := by
  constructor
  · rintro ⟨t, hta, htb, htc⟩
    have h := t.defect; rw [hta, htb, htc] at h; exact h
  · intro hdef
    exact exists_triangle_of_defect A B C hA hB hC hAlt hBlt hClt hdef

/-- **Existence of the equilateral family.** For every admissible common angle
    `θ ∈ (0, π/3)`, a hyperbolic equilateral triangle with all three angles `θ` exists. This
    specializes `exists_triangle_of_defect` to `A = B = C = θ`; the bound `θ < π/3` is exactly
    the defect condition `3θ < π`, matching `equilateral_angle_lt_pi_third`. It shows the
    equilateral results (PARTS 5, 7, 8) are non-vacuous across the whole range `(0, π/3)`. -/
theorem exists_equilateral (θ : ℝ) (hθ : 0 < θ) (hθ3 : θ < Real.pi / 3) :
    ∃ t : HyperbolicTriangle, t.A = θ ∧ t.B = θ ∧ t.C = θ := by
  have hθpi : θ < Real.pi := by linarith [Real.pi_pos]
  exact exists_triangle_of_defect θ θ θ hθ hθ hθ hθpi hθpi hθpi (by linarith)

-- ============================================================
-- PART 11: Equilateral side lengths in closed form (explicit arcosh)
-- ============================================================

/-- **The equilateral side length in closed form.** Upgrading `equilateral_cosh` from the
    `cosh` of the side to the side itself: an equilateral hyperbolic triangle with common
    angle `θ` has every side equal to `arcosh(cos θ / (1 - cos θ))`. Because the side is
    nonnegative, `arcosh` inverts `cosh` (`Real.arcosh_cosh`), turning the implicit length of
    PART 5 into an explicit formula and confirming that the closed form of PART 5 really is
    the metric length of the side (not merely its hyperbolic cosine). -/
theorem equilateral_side (t : HyperbolicTriangle)
    (hAB : t.A = t.B) (hBC : t.B = t.C) :
    t.c = Real.arcosh (Real.cos t.C / (1 - Real.cos t.C)) := by
  rw [← equilateral_cosh t hAB hBC, Real.arcosh_cosh t.hc.le]

/-- **The concrete equilateral side length.** The hyperbolic equilateral triangle with all
    three angles `π/4` has every side exactly `arcosh(1 + √2)` — the explicit length promised
    by the docstring of `equilateral_pi_four_cosh`, which only established the `cosh` value.
    Immediate from `equilateral_pi_four_cosh` and `Real.arcosh_cosh` (the side is
    nonnegative). -/
theorem equilateral_pi_four_side (t : HyperbolicTriangle)
    (hAB : t.A = t.B) (hBC : t.B = t.C) (hC4 : t.C = Real.pi / 4) :
    t.c = Real.arcosh (1 + Real.sqrt 2) := by
  rw [← equilateral_pi_four_cosh t hAB hBC hC4, Real.arcosh_cosh t.hc.le]

end HyperbolicAAA
