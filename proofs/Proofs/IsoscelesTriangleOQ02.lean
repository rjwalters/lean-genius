import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Isosceles triangle OQ-02: Pons Asinorum in hyperbolic and spherical geometry

The parent entry (`isosceles-triangle`) proves the isosceles triangle theorem (Euclid I.5,
"Pons Asinorum": equal sides ⟹ equal base angles) in Euclidean geometry using Mathlib's
inner-product-space machinery. It lists as an open question:

> *Prove the isosceles triangle theorem in hyperbolic and spherical geometry, where the
> inner product space structure is unavailable.*

This file does so **without any inner product space**, working purely from the
non-Euclidean **laws of cosines**:

* spherical:   `cos a = cos b · cos c + sin b · sin c · cos A`,
* hyperbolic:  `cosh a = cosh b · cosh c − sinh b · sinh c · cos A`,

where `A` is the angle opposite side `a`. Solving for `cos A` gives a symmetric expression
in the two adjacent sides `b, c`; when the triangle is isosceles (`a = b`) the base-angle
cosines coincide, and since `cos` is injective on `[0, π]` the base angles are equal. The
same algebra, with `cos/sin` replaced by `cosh/sinh`, handles the hyperbolic case.

## Main results

* `sphCosA` / `hypCosA` : `cos` of the angle opposite a side, from the law of cosines.
* `sph_isosceles_cos` / `hyp_isosceles_cos` : equal legs give equal base-angle cosines.
* `spherical_isosceles` / `hyperbolic_isosceles` : **Pons Asinorum** in each geometry.
* `spherical_equilateral` / `hyperbolic_equilateral` : equilateral ⟹ equiangular.
-/

namespace IsoscelesTriangleOQ02

open Real Set

/-- `cos` of the angle opposite side `a` in a **spherical** triangle with sides `a, b, c`,
    obtained from the spherical law of cosines `cos a = cos b·cos c + sin b·sin c·cos A`. -/
noncomputable def sphCosA (a b c : ℝ) : ℝ := (cos a - cos b * cos c) / (sin b * sin c)

/-- `cos` of the angle opposite side `a` in a **hyperbolic** triangle with sides `a, b, c`,
    obtained from the hyperbolic law of cosines `cosh a = cosh b·cosh c − sinh b·sinh c·cos A`. -/
noncomputable def hypCosA (a b c : ℝ) : ℝ := (cosh b * cosh c - cosh a) / (sinh b * sinh c)

/-- **Algebraic core (spherical).** Equal legs `a = b` force the two base-angle cosines to
    coincide: `cos A = cos B`. -/
theorem sph_isosceles_cos {a b c : ℝ} (h : a = b) : sphCosA a b c = sphCosA b a c := by
  subst h; rfl

/-- **Algebraic core (hyperbolic).** Equal legs `a = b` force `cos A = cos B`. -/
theorem hyp_isosceles_cos {a b c : ℝ} (h : a = b) : hypCosA a b c = hypCosA b a c := by
  subst h; rfl

/-- **Pons Asinorum, spherical geometry.** In a spherical triangle whose sides `a, b, c` and
    base angles `A, B ∈ [0, π]` satisfy the spherical law of cosines, equal legs `a = b`
    imply equal base angles `A = B`. No inner product space is used. -/
theorem spherical_isosceles {a b c A B : ℝ} (hA : A ∈ Icc 0 π) (hB : B ∈ Icc 0 π)
    (lawA : cos A = sphCosA a b c) (lawB : cos B = sphCosA b a c) (h : a = b) : A = B := by
  apply Real.injOn_cos hA hB
  rw [lawA, lawB, sph_isosceles_cos h]

/-- **Pons Asinorum, hyperbolic geometry.** Same statement with the hyperbolic law of
    cosines: equal legs imply equal base angles, with no inner product space. -/
theorem hyperbolic_isosceles {a b c A B : ℝ} (hA : A ∈ Icc 0 π) (hB : B ∈ Icc 0 π)
    (lawA : cos A = hypCosA a b c) (lawB : cos B = hypCosA b a c) (h : a = b) : A = B := by
  apply Real.injOn_cos hA hB
  rw [lawA, lawB, hyp_isosceles_cos h]

/-- **Equilateral ⟹ equiangular, spherical geometry.** A spherical triangle with all sides
    equal has all angles equal. -/
theorem spherical_equilateral {a A B C : ℝ}
    (hA : A ∈ Icc 0 π) (hB : B ∈ Icc 0 π) (hC : C ∈ Icc 0 π)
    (lawA : cos A = sphCosA a a a) (lawB : cos B = sphCosA a a a)
    (lawC : cos C = sphCosA a a a) : A = B ∧ B = C := by
  refine ⟨Real.injOn_cos hA hB ?_, Real.injOn_cos hB hC ?_⟩
  · rw [lawA, lawB]
  · rw [lawB, lawC]

/-- **Equilateral ⟹ equiangular, hyperbolic geometry.** -/
theorem hyperbolic_equilateral {a A B C : ℝ}
    (hA : A ∈ Icc 0 π) (hB : B ∈ Icc 0 π) (hC : C ∈ Icc 0 π)
    (lawA : cos A = hypCosA a a a) (lawB : cos B = hypCosA a a a)
    (lawC : cos C = hypCosA a a a) : A = B ∧ B = C := by
  refine ⟨Real.injOn_cos hA hB ?_, Real.injOn_cos hB hC ?_⟩
  · rw [lawA, lawB]
  · rw [lawB, lawC]

end IsoscelesTriangleOQ02
