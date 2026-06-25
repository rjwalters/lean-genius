import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Isosceles triangle OQ-02-OQ-01: Converse Pons Asinorum in hyperbolic and spherical geometry

The parent entry (`isosceles-triangle-oq-02`) proves **Pons Asinorum** (Euclid I.5,
"equal sides ⟹ equal base angles") in spherical and hyperbolic geometry, working purely
from the *laws of cosines* with no inner product space. It lists as its first open question:

> *Prove the converse (equal base angles ⟹ equal opposite sides) in spherical and
> hyperbolic geometry, using the dual law of cosines that expresses sides in terms of angles.*

This file does so. The engine is the **dual (polar) law of cosines**, which expresses a
side in terms of the three angles:

* spherical:   `cos a = (cos A + cos B · cos C) / (sin B · sin C)`,
* hyperbolic:  `cosh a = (cos A + cos B · cos C) / (sin B · sin C)`,

where `A` is the angle opposite side `a` and `B, C` are the other two angles. The right-hand
side is the *same symmetric expression* in both geometries — only the left-hand side changes
(`cos a` spherically, `cosh a` hyperbolically). When two angles are equal (`A = B`) the
two opposite-side expressions coincide, so `cos a = cos b` (resp. `cosh a = cosh b`); since
`cos` is injective on `[0, π]` (spherical sides) and `cosh` is injective on `[0, ∞)`
(hyperbolic sides), the opposite sides are equal.

This is the exact dual of the parent's argument: there, equal sides forced equal
angle-cosines via the law of cosines; here, equal angles force equal side-(co)sines via the
dual law of cosines.

## Main results

* `sphCosSide` / `hypCoshSide` : the dual-law expression for `cos a` / `cosh a` from the angles.
* `sph_converse_eq` / `hyp_converse_eq` : equal angles `A = B` give equal side expressions.
* `spherical_isosceles_converse` / `hyperbolic_isosceles_converse` : **Converse Pons
  Asinorum** in each geometry (equal base angles ⟹ equal opposite sides).
* `spherical_equiangular` / `hyperbolic_equiangular` : equiangular ⟹ equilateral.

No inner product space and no axioms are used.
-/

namespace IsoscelesTriangleOQ02OQ01

open Real Set

/-- `cos` of the side `a` opposite angle `A` in a **spherical** triangle with angles
    `A, B, C`, obtained from the dual (polar) law of cosines
    `cos a = (cos A + cos B · cos C) / (sin B · sin C)`. -/
noncomputable def sphCosSide (A B C : ℝ) : ℝ := (cos A + cos B * cos C) / (sin B * sin C)

/-- `cosh` of the side `a` opposite angle `A` in a **hyperbolic** triangle with angles
    `A, B, C`, obtained from the dual (polar) law of cosines
    `cosh a = (cos A + cos B · cos C) / (sin B · sin C)`. The right-hand side is identical to
    the spherical case; only the left-hand side (`cosh a` vs `cos a`) differs. -/
noncomputable def hypCoshSide (A B C : ℝ) : ℝ := (cos A + cos B * cos C) / (sin B * sin C)

/-- **Algebraic core (spherical).** Equal angles `A = B` force the two opposite-side cosines
    to coincide: `cos a = cos b`. -/
theorem sph_converse_eq {A B C : ℝ} (h : A = B) : sphCosSide A B C = sphCosSide B A C := by
  subst h; rfl

/-- **Algebraic core (hyperbolic).** Equal angles `A = B` force `cosh a = cosh b`. -/
theorem hyp_converse_eq {A B C : ℝ} (h : A = B) : hypCoshSide A B C = hypCoshSide B A C := by
  subst h; rfl

/-- **Converse Pons Asinorum, spherical geometry.** In a spherical triangle whose angles
    `A, B, C` and sides `a, b ∈ [0, π]` satisfy the dual law of cosines, equal base angles
    `A = B` imply equal opposite sides `a = b`. No inner product space is used. -/
theorem spherical_isosceles_converse {a b A B C : ℝ} (ha : a ∈ Icc 0 π) (hb : b ∈ Icc 0 π)
    (lawa : cos a = sphCosSide A B C) (lawb : cos b = sphCosSide B A C) (h : A = B) : a = b := by
  apply Real.injOn_cos ha hb
  rw [lawa, lawb, sph_converse_eq h]

/-- **Converse Pons Asinorum, hyperbolic geometry.** Same statement with the hyperbolic dual
    law of cosines and sides `a, b ≥ 0`: equal base angles imply equal opposite sides, with
    no inner product space. Injectivity of `cosh` on `[0, ∞)` replaces injectivity of `cos`
    on `[0, π]`. -/
theorem hyperbolic_isosceles_converse {a b A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (lawa : cosh a = hypCoshSide A B C) (lawb : cosh b = hypCoshSide B A C) (h : A = B) :
    a = b := by
  apply StrictMonoOn.injOn Real.cosh_strictMonoOn (mem_Ici.mpr ha) (mem_Ici.mpr hb)
  rw [lawa, lawb, hyp_converse_eq h]

/-- **Equiangular ⟹ equilateral, spherical geometry.** A spherical triangle with all angles
    equal has all sides equal. -/
theorem spherical_equiangular {a b c A : ℝ}
    (ha : a ∈ Icc 0 π) (hb : b ∈ Icc 0 π) (hc : c ∈ Icc 0 π)
    (lawa : cos a = sphCosSide A A A) (lawb : cos b = sphCosSide A A A)
    (lawc : cos c = sphCosSide A A A) : a = b ∧ b = c := by
  refine ⟨Real.injOn_cos ha hb ?_, Real.injOn_cos hb hc ?_⟩
  · rw [lawa, lawb]
  · rw [lawb, lawc]

/-- **Equiangular ⟹ equilateral, hyperbolic geometry.** -/
theorem hyperbolic_equiangular {a b c A : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (lawa : cosh a = hypCoshSide A A A) (lawb : cosh b = hypCoshSide A A A)
    (lawc : cosh c = hypCoshSide A A A) : a = b ∧ b = c := by
  refine ⟨StrictMonoOn.injOn Real.cosh_strictMonoOn (mem_Ici.mpr ha) (mem_Ici.mpr hb) ?_,
    StrictMonoOn.injOn Real.cosh_strictMonoOn (mem_Ici.mpr hb) (mem_Ici.mpr hc) ?_⟩
  · rw [lawa, lawb]
  · rw [lawb, lawc]

end IsoscelesTriangleOQ02OQ01
