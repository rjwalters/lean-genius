import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

The three second-law-of-cosines relations and the angular defect are encoded as
structure fields (assumptions about a hyperbolic triangle, exactly as in the parent
`law-of-cosines-oq-03`). All theorems below are derived from those assumptions with
no additional axioms and no sorries.

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
    **second laws of cosines** (one per angle) together with the angular defect
    `A + B + C < π`. These are the same kind of structure-encoded assumptions used in
    the parent `law-of-cosines-oq-03`. -/
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
  /-- Angular defect: the hyperbolic angle sum is strictly less than π. -/
  defect : A + B + C < Real.pi
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

end HyperbolicAAA
