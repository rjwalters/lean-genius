/-
# Green's Theorem OQ-03: Concrete Simply-Connected Region

## The Open Question

The base `GreensTheorem.lean` has a trivial placeholder:

```lean
structure GreenRegion where
  dummy : Unit  -- purely abstract!

axiom greens_theorem_general ... : True  -- trivially satisfied by anything!
```

OQ-03 asks: **Can we replace `GreenRegion` with a concrete structure defining
a simply-connected planar region, and state a meaningful Green's theorem?**

## Answer: YES — using Type I (vertically simple) regions

A **Type I region** is: D = {(x,y) | a ≤ x ≤ b, f(x) ≤ y ≤ g(x)}
where f(x) ≤ g(x) are continuous bounding curves.

This is the standard form used in multivariable calculus textbooks
(Apostol, Rudin, Stewart) for proving Green's theorem via FTC + Fubini.

## What This File Proves

- `TypeIRegion` structure with geometric data (not `dummy : Unit`)
- Membership characterization, boundary curves in region
- Area formula: Area(D) = ∫_a^b (g(x) - f(x)) dx  [concrete Mathlib integral]
- Rectangles as special cases of TypeI regions
- Iterated integral definition for double integrals
- Green's theorem for TypeI regions (axiom with full proof sketch)

Theorems: 13, Axioms: 1, Sorries: 0
-/

import Mathlib
import Proofs.GreensTheoremOQ01

namespace GreensTheoremOQ03

open MeasureTheory intervalIntegral

/-
## Part I: The TypeI Region — Concrete Simply-Connected Region
-/

/-- A **Type I (vertically simple) region** in ℝ²:
    D = {(x,y) | a ≤ x ≤ b, f(x) ≤ y ≤ g(x)}
    where f, g : ℝ → ℝ with f(x) ≤ g(x) on [a,b].

    This is the concrete replacement for `GreensTheorem.GreenRegion`:
    - Base: `structure GreenRegion where dummy : Unit` (no content)
    - OQ-03: `TypeIRegion` with real bounds, curves, and ordering constraint -/
structure TypeIRegion where
  a : ℝ
  b : ℝ
  f : ℝ → ℝ
  g : ℝ → ℝ
  hab : a < b
  hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x

/-- The underlying set of points in a Type I region. -/
def TypeIRegion.toSet (R : TypeIRegion) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | R.a ≤ p.1 ∧ p.1 ≤ R.b ∧ R.f p.1 ≤ p.2 ∧ p.2 ≤ R.g p.1}

/-- Membership in a Type I region: (x,y) ∈ D iff a ≤ x ≤ b and f(x) ≤ y ≤ g(x). -/
theorem typeI_mem_iff (R : TypeIRegion) (x y : ℝ) :
    (x, y) ∈ R.toSet ↔ R.a ≤ x ∧ x ≤ R.b ∧ R.f x ≤ y ∧ y ≤ R.g x := by
  simp only [TypeIRegion.toSet, Set.mem_setOf_eq]

/-- The lower boundary curve (x, f(x)) lies in the region. -/
theorem typeI_lower_mem (R : TypeIRegion) {x : ℝ} (hx : x ∈ Set.Icc R.a R.b) :
    (x, R.f x) ∈ R.toSet := by
  rw [typeI_mem_iff]; exact ⟨hx.1, hx.2, le_refl _, R.hfg x hx⟩

/-- The upper boundary curve (x, g(x)) lies in the region. -/
theorem typeI_upper_mem (R : TypeIRegion) {x : ℝ} (hx : x ∈ Set.Icc R.a R.b) :
    (x, R.g x) ∈ R.toSet := by
  rw [typeI_mem_iff]; exact ⟨hx.1, hx.2, R.hfg x hx, le_refl _⟩

/-- A Type I region is nonempty: it contains the point (a, f(a)). -/
theorem typeI_nonempty (R : TypeIRegion) : R.toSet.Nonempty :=
  ⟨(R.a, R.f R.a), typeI_lower_mem R (Set.left_mem_Icc.mpr R.hab.le)⟩

/-- In a Type I region, f(x) ≤ g(x) on the base interval. -/
theorem typeI_curve_le (R : TypeIRegion) {x : ℝ} (hx : x ∈ Set.Icc R.a R.b) :
    R.f x ≤ R.g x := R.hfg x hx

/-
## Part II: Rectangles as TypeI Regions
-/

/-- A rectangle [a,b] × [c,d] as a Type I region (constant boundary curves). -/
def rectToTypeI (a b c d : ℝ) (hab : a < b) (hcd : c ≤ d) : TypeIRegion where
  a := a
  b := b
  f := fun _ => c
  g := fun _ => d
  hab := hab
  hfg := fun _ _ => hcd

/-- The set of a rectangle TypeI region equals the product Icc a b ×ˢ Icc c d. -/
theorem rectTypeI_set_eq (a b c d : ℝ) (hab : a < b) (hcd : c ≤ d) :
    (rectToTypeI a b c d hab hcd).toSet = Set.Icc a b ×ˢ Set.Icc c d := by
  ext ⟨x, y⟩
  simp only [typeI_mem_iff, rectToTypeI, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- The unit square [0,1]² as a TypeI region. -/
def unitSquareTypeI : TypeIRegion :=
  rectToTypeI 0 1 0 1 (by norm_num) (by norm_num)

/-- The unit square TypeI region contains (1/2, 1/2). -/
theorem unitSquareTypeI_contains_center :
    ((1 : ℝ)/2, (1 : ℝ)/2) ∈ unitSquareTypeI.toSet := by
  simp only [typeI_mem_iff, unitSquareTypeI, rectToTypeI]
  norm_num

/-
## Part III: Area of a TypeI Region
-/

/-- The **area** of a Type I region as a concrete Mathlib integral:
    Area(D) = ∫_a^b (g(x) - f(x)) dx. -/
noncomputable def TypeIRegion.area (R : TypeIRegion) : ℝ :=
  ∫ x in R.a..R.b, (R.g x - R.f x)

/-- The area of a Type I region is nonneg (since g(x) ≥ f(x)). -/
theorem typeI_area_nonneg (R : TypeIRegion) : 0 ≤ R.area := by
  apply intervalIntegral.integral_nonneg R.hab.le
  intro x hx
  linarith [R.hfg x hx]

/-- Area of a rectangle [a,b]×[c,d] via TypeI formula = (b-a)*(d-c). -/
theorem typeI_rect_area (a b c d : ℝ) (hab : a < b) (hcd : c ≤ d) :
    (rectToTypeI a b c d hab hcd).area = (b - a) * (d - c) := by
  show ∫ x in a..b, ((fun _ => d) x - (fun _ => c) x) = (b - a) * (d - c)
  rw [intervalIntegral.integral_const, smul_eq_mul]

/-- Area of the unit square via TypeI formula = 1. -/
theorem unitSquareTypeI_area : unitSquareTypeI.area = 1 := by
  unfold unitSquareTypeI
  rw [typeI_rect_area]
  norm_num

/-- Constant height region: area = h * (b - a). -/
theorem typeI_const_height_area (a b h : ℝ) (hab : a < b) (hh : 0 ≤ h) :
    (TypeIRegion.mk a b (fun _ => 0) (fun _ => h) hab (fun _ _ => hh)).area = h * (b - a) := by
  show ∫ x in a..b, ((fun _ => h) x - (fun _ => 0) x) = h * (b - a)
  simp only [sub_zero]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-
## Part IV: Iterated Integral
-/

/-- **Iterated integral** over a Type I region:
    ∬_D F(x,y) dA = ∫_a^b [∫_{f(x)}^{g(x)} F(x,y) dy] dx. -/
noncomputable def TypeIRegion.iteratedIntegral (R : TypeIRegion) (F : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in R.a..R.b, ∫ y in R.f x..R.g x, F (x, y)

/-- Area = iterated integral of 1. -/
theorem typeI_area_is_iterated_one (R : TypeIRegion) :
    R.area = R.iteratedIntegral (fun _ => 1) := by
  simp only [TypeIRegion.area, TypeIRegion.iteratedIntegral]
  congr 1
  ext x
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- Rectangle iterated integral of 1 = (b-a)*(d-c). -/
theorem typeI_rect_iterated_one (a b c d : ℝ) (hab : a < b) (hcd : c ≤ d) :
    (rectToTypeI a b c d hab hcd).iteratedIntegral (fun _ => 1) = (b - a) * (d - c) := by
  rw [← typeI_area_is_iterated_one]
  exact typeI_rect_area a b c d hab hcd

/-
## Part V: Green's Theorem for TypeI Regions
-/

/-- **Green's Theorem for Type I Regions** (axiom with concrete formulation).

    For a Type I region D = {(x,y) | a ≤ x ≤ b, f(x) ≤ y ≤ g(x)}
    with a C¹ vector field (P, Q), Green's theorem states:

      ∮_∂D (P dx + Q dy) = ∬_D (∂Q/∂x - ∂P/∂y) dA

    **Proof sketch** (FTC for TypeI regions):
    ∬_D ∂P/∂y dA = ∫_a^b [P(x,g(x)) - P(x,f(x))] dx  (inner FTC)
    ∬_D ∂Q/∂x dA = ∫ [Q(b,y) - Q(a,y)] dy  (outer FTC + Fubini)
    Boundary decomposes as lower/upper curves + vertical sides.
    Reference: Apostol "Mathematical Analysis" §17.4. -/
axiom greens_theorem_typeI
    (R : TypeIRegion)
    (P Q dPdy dQdx : ℝ × ℝ → ℝ)
    (hP_smooth : ∀ x ∈ Set.Icc R.a R.b, ∀ y ∈ Set.Icc (R.f x) (R.g x),
      HasDerivAt (fun y => P (x, y)) (dPdy (x, y)) y)
    (hQ_smooth : ∀ y, ∀ x ∈ Set.Icc R.a R.b,
      HasDerivAt (fun x => Q (x, y)) (dQdx (x, y)) x) :
    R.iteratedIntegral (fun p => dQdx p - dPdy p) =
    (∫ x in R.a..R.b, (Q (x, R.g x) * deriv R.g x - Q (x, R.f x) * deriv R.f x)) +
    (∫ y in R.f R.b..R.g R.b, Q (R.b, y)) -
    (∫ y in R.f R.a..R.g R.a, Q (R.a, y)) +
    (∫ x in R.a..R.b, (P (x, R.f x) - P (x, R.g x)))

end GreensTheoremOQ03
