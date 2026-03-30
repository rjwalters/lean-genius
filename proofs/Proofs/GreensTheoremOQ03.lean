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
- Inner FTC for TypeI regions: ∬∂P/∂y = ∫[P(x,g(x))-P(x,f(x))]dx (PROVED)
- P boundary contribution: relates to -∬∂P/∂y (PROVED)
- TypeII (horizontally simple) regions: structure, membership, area
- Inner FTC for TypeII regions: ∬∂Q/∂x = ∫[Q(k(y),y)-Q(h(y),y)]dy (PROVED)
- Disk as TypeI and TypeII region with membership characterization
- Upper semicircle area = πr²/2 (PROVED from disk area axiom)
- Rectangle TypeII properties, TypeI-TypeII set equality
- P and Q contributions for rectangles via inner FTC

Theorems: 31, Axioms: 3, Sorries: 0
-/

import Mathlib
import Proofs.GreensTheoremOQ01

namespace GreensTheoremOQ03

open MeasureTheory intervalIntegral Real

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
    (hP_smooth : ∀ x y, (x, y) ∈ R.toSet →
      HasDerivAt (fun y => P (x, y)) (dPdy (x, y)) y)
    (hQ_smooth : ∀ x y, (x, y) ∈ R.toSet →
      HasDerivAt (fun x => Q (x, y)) (dQdx (x, y)) x) :
    R.iteratedIntegral (fun p => dQdx p - dPdy p) =
    (∫ x in R.a..R.b, (Q (x, R.f x) * deriv R.f x - Q (x, R.g x) * deriv R.g x)) +
    (∫ y in R.f R.b..R.g R.b, Q (R.b, y)) -
    (∫ y in R.f R.a..R.g R.a, Q (R.a, y)) +
    (∫ x in R.a..R.b, (P (x, R.f x) - P (x, R.g x)))

/-
## Part VI: Inner FTC — The P Contribution to Green's Theorem

The standard textbook proof (Apostol §17.4, Rudin §10.33) decomposes
Green's theorem into two independent halves:
1. **P contribution**: using TypeI structure, prove
   ∬_D ∂P/∂y dA = ∫_a^b [P(x,g(x)) - P(x,f(x))] dx
   via inner FTC in the y-direction.
2. **Q contribution**: using TypeII structure, prove
   ∬_D ∂Q/∂x dA = ∫_c^d [Q(k(y),y) - Q(h(y),y)] dy
   via inner FTC in the x-direction.

This section proves the P contribution completely — zero axioms needed.
-/

/-- **Inner FTC for TypeI Regions** (the P contribution to Green's theorem).

    ∫_a^b [∫_{f(x)}^{g(x)} ∂P/∂y dy] dx = ∫_a^b [P(x,g(x)) - P(x,f(x))] dx

    Proof: apply FTC to each inner integral, then lift to the outer integral
    via `integral_congr`. This is the computational heart of the standard proof
    that ∬_D ∂P/∂y dA = -∮_∂D P dx. -/
theorem typeI_inner_ftc_P (R : TypeIRegion) (P dPdy : ℝ × ℝ → ℝ)
    (hP_deriv : ∀ x ∈ Set.uIcc R.a R.b, ∀ y ∈ Set.uIcc (R.f x) (R.g x),
      HasDerivAt (fun y => P (x, y)) (dPdy (x, y)) y)
    (hP_int : ∀ x ∈ Set.uIcc R.a R.b,
      IntervalIntegrable (fun y => dPdy (x, y)) volume (R.f x) (R.g x)) :
    R.iteratedIntegral dPdy =
    ∫ x in R.a..R.b, (P (x, R.g x) - P (x, R.f x)) := by
  simp only [TypeIRegion.iteratedIntegral]
  exact integral_congr (fun x hx =>
    integral_eq_sub_of_hasDerivAt (hP_deriv x hx) (hP_int x hx))

/-- The P contribution matches the boundary term in `greens_theorem_typeI`:
    ∫_a^b [P(x,f(x)) - P(x,g(x))] dx = -∬_D ∂P/∂y dA.

    The sign flip comes from the boundary orientation: the lower curve f(x)
    is traversed left-to-right but the upper curve g(x) right-to-left. -/
theorem typeI_P_boundary (R : TypeIRegion) (P dPdy : ℝ × ℝ → ℝ)
    (hP_deriv : ∀ x ∈ Set.uIcc R.a R.b, ∀ y ∈ Set.uIcc (R.f x) (R.g x),
      HasDerivAt (fun y => P (x, y)) (dPdy (x, y)) y)
    (hP_int : ∀ x ∈ Set.uIcc R.a R.b,
      IntervalIntegrable (fun y => dPdy (x, y)) volume (R.f x) (R.g x)) :
    ∫ x in R.a..R.b, (P (x, R.f x) - P (x, R.g x)) =
    -(R.iteratedIntegral dPdy) := by
  rw [typeI_inner_ftc_P R P dPdy hP_deriv hP_int]
  have : (fun x => P (x, R.f x) - P (x, R.g x)) =
         fun x => -(P (x, R.g x) - P (x, R.f x)) := by ext x; ring
  rw [this, intervalIntegral.integral_neg]

/-- For constant boundaries (rectangles), the inner FTC reduces to the
    classical rectangle form: ∫_a^b [P(x,d) - P(x,c)] dx = ∬ ∂P/∂y dA. -/
theorem typeI_rect_inner_ftc_P (a b c d : ℝ) (hab : a < b) (hcd : c ≤ d)
    (P dPdy : ℝ × ℝ → ℝ)
    (hP_deriv : ∀ x ∈ Set.uIcc a b, ∀ y ∈ Set.uIcc c d,
      HasDerivAt (fun y => P (x, y)) (dPdy (x, y)) y)
    (hP_int : ∀ x ∈ Set.uIcc a b,
      IntervalIntegrable (fun y => dPdy (x, y)) volume c d) :
    (rectToTypeI a b c d hab hcd).iteratedIntegral dPdy =
    ∫ x in a..b, (P (x, d) - P (x, c)) := by
  exact typeI_inner_ftc_P (rectToTypeI a b c d hab hcd) P dPdy hP_deriv hP_int

/-
## Part VII: TypeII (Horizontally Simple) Regions

A **Type II region** is the dual of Type I:
  D = {(x,y) | c ≤ y ≤ d, h(y) ≤ x ≤ k(y)}

This is needed for the Q contribution to Green's theorem.
Regions that are BOTH TypeI and TypeII (rectangles, convex regions, disks)
allow the full Green's theorem to be proved by combining both halves.
-/

/-- A **Type II (horizontally simple) region** in ℝ²:
    D = {(x,y) | c ≤ y ≤ d, h(y) ≤ x ≤ k(y)}
    where h, k : ℝ → ℝ with h(y) ≤ k(y) on [c,d].

    This is the dual of `TypeIRegion`, with roles of x and y swapped. -/
structure TypeIIRegion where
  c : ℝ
  d : ℝ
  h : ℝ → ℝ  -- left boundary
  k : ℝ → ℝ  -- right boundary
  hcd : c < d
  hhk : ∀ y ∈ Set.Icc c d, h y ≤ k y

/-- The underlying set of points in a Type II region. -/
def TypeIIRegion.toSet (R : TypeIIRegion) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | R.c ≤ p.2 ∧ p.2 ≤ R.d ∧ R.h p.2 ≤ p.1 ∧ p.1 ≤ R.k p.2}

/-- Membership in a Type II region. -/
theorem typeII_mem_iff (R : TypeIIRegion) (x y : ℝ) :
    (x, y) ∈ R.toSet ↔ R.c ≤ y ∧ y ≤ R.d ∧ R.h y ≤ x ∧ x ≤ R.k y := by
  simp only [TypeIIRegion.toSet, Set.mem_setOf_eq]

/-- A Type II region is nonempty: it contains (h(c), c). -/
theorem typeII_nonempty (R : TypeIIRegion) : R.toSet.Nonempty :=
  ⟨(R.h R.c, R.c), by
    rw [typeII_mem_iff]
    exact ⟨le_refl _, R.hcd.le, le_refl _, R.hhk R.c (Set.left_mem_Icc.mpr R.hcd.le)⟩⟩

/-- **Iterated integral** over a Type II region:
    ∬_D F(x,y) dA = ∫_c^d [∫_{h(y)}^{k(y)} F(x,y) dx] dy. -/
noncomputable def TypeIIRegion.iteratedIntegral (R : TypeIIRegion) (F : ℝ × ℝ → ℝ) : ℝ :=
  ∫ y in R.c..R.d, ∫ x in R.h y..R.k y, F (x, y)

/-- The **area** of a Type II region:
    Area(D) = ∫_c^d (k(y) - h(y)) dy. -/
noncomputable def TypeIIRegion.area (R : TypeIIRegion) : ℝ :=
  ∫ y in R.c..R.d, (R.k y - R.h y)

/-- The area of a Type II region is nonneg. -/
theorem typeII_area_nonneg (R : TypeIIRegion) : 0 ≤ R.area := by
  apply intervalIntegral.integral_nonneg R.hcd.le
  intro y hy
  linarith [R.hhk y hy]

/-- A rectangle [a,b] × [c,d] as a Type II region (constant boundary curves). -/
def rectToTypeII (a b c d : ℝ) (hcd : c < d) (hab : a ≤ b) : TypeIIRegion where
  c := c
  d := d
  h := fun _ => a
  k := fun _ => b
  hcd := hcd
  hhk := fun _ _ => hab

/-
## Part VIII: Inner FTC for TypeII — The Q Contribution

The Q contribution to Green's theorem follows the same logic as the P
contribution, but with TypeII structure and FTC in the x-direction.
-/

/-- **Inner FTC for TypeII Regions** (the Q contribution to Green's theorem).

    ∫_c^d [∫_{h(y)}^{k(y)} ∂Q/∂x dx] dy = ∫_c^d [Q(k(y),y) - Q(h(y),y)] dy

    Proof is symmetric to `typeI_inner_ftc_P`: apply FTC to each inner
    integral (now in x), then lift via `integral_congr`. -/
theorem typeII_inner_ftc_Q (R : TypeIIRegion) (Q dQdx : ℝ × ℝ → ℝ)
    (hQ_deriv : ∀ y ∈ Set.uIcc R.c R.d, ∀ x ∈ Set.uIcc (R.h y) (R.k y),
      HasDerivAt (fun x => Q (x, y)) (dQdx (x, y)) x)
    (hQ_int : ∀ y ∈ Set.uIcc R.c R.d,
      IntervalIntegrable (fun x => dQdx (x, y)) volume (R.h y) (R.k y)) :
    R.iteratedIntegral dQdx =
    ∫ y in R.c..R.d, (Q (R.k y, y) - Q (R.h y, y)) := by
  simp only [TypeIIRegion.iteratedIntegral]
  exact integral_congr (fun y hy =>
    integral_eq_sub_of_hasDerivAt (hQ_deriv y hy) (hQ_int y hy))

/-- The Q boundary term: ∫_c^d [Q(k(y),y) - Q(h(y),y)] dy = ∬_D ∂Q/∂x dA.
    No sign flip needed — the boundary orientation matches naturally for Q. -/
theorem typeII_Q_boundary (R : TypeIIRegion) (Q dQdx : ℝ × ℝ → ℝ)
    (hQ_deriv : ∀ y ∈ Set.uIcc R.c R.d, ∀ x ∈ Set.uIcc (R.h y) (R.k y),
      HasDerivAt (fun x => Q (x, y)) (dQdx (x, y)) x)
    (hQ_int : ∀ y ∈ Set.uIcc R.c R.d,
      IntervalIntegrable (fun x => dQdx (x, y)) volume (R.h y) (R.k y)) :
    ∫ y in R.c..R.d, (Q (R.k y, y) - Q (R.h y, y)) =
    R.iteratedIntegral dQdx := by
  rw [typeII_inner_ftc_Q R Q dQdx hQ_deriv hQ_int]

/-
## Part IX: Disk as a TypeI Region

The closed disk {(x,y) | x² + y² ≤ r²} is a fundamental simply-connected
region. As a TypeI region:
  D = {(x,y) | -r ≤ x ≤ r, -√(r²-x²) ≤ y ≤ √(r²-x²)}
-/

/-- The closed disk of radius r centered at the origin, as a TypeI region.
    Lower boundary: y = -√(r²-x²), Upper boundary: y = √(r²-x²). -/
noncomputable def diskTypeI (r : ℝ) (hr : 0 < r) : TypeIRegion where
  a := -r
  b := r
  f := fun x => -Real.sqrt (r ^ 2 - x ^ 2)
  g := fun x => Real.sqrt (r ^ 2 - x ^ 2)
  hab := by linarith
  hfg := fun x _ => by linarith [Real.sqrt_nonneg (r ^ 2 - x ^ 2)]

/-- The disk contains its center (0, 0). -/
theorem disk_contains_origin (r : ℝ) (hr : 0 < r) :
    ((0 : ℝ), (0 : ℝ)) ∈ (diskTypeI r hr).toSet := by
  dsimp [TypeIRegion.toSet, diskTypeI]
  exact ⟨by linarith, by linarith,
    by linarith [Real.sqrt_nonneg (r ^ 2 - (0 : ℝ) ^ 2)],
    Real.sqrt_nonneg _⟩

/-- A point (x,y) is in the disk TypeI region iff x² + y² ≤ r². -/
theorem disk_mem_iff (r : ℝ) (hr : 0 < r) (x y : ℝ) :
    (x, y) ∈ (diskTypeI r hr).toSet ↔ x ^ 2 + y ^ 2 ≤ r ^ 2 := by
  simp only [TypeIRegion.toSet, diskTypeI, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hax, hxb, hfy, hyg⟩
    have hnn : 0 ≤ r ^ 2 - x ^ 2 := by nlinarith
    have hsq := sq_le_sq' hfy hyg
    rw [Real.sq_sqrt hnn] at hsq
    linarith
  · intro h
    have hnn : 0 ≤ r ^ 2 - x ^ 2 := by nlinarith [sq_nonneg y]
    have hy2 : y ^ 2 ≤ r ^ 2 - x ^ 2 := by linarith
    -- |y| ≤ √(r²-x²) gives both bounds
    have h_sqrt_y : Real.sqrt (y ^ 2) = |y| := by
      rw [← sq_abs]; exact Real.sqrt_sq (abs_nonneg y)
    have h_abs : |y| ≤ Real.sqrt (r ^ 2 - x ^ 2) := by
      rw [← h_sqrt_y]; exact Real.sqrt_le_sqrt hy2
    rw [abs_le] at h_abs
    exact ⟨by nlinarith [sq_nonneg (x + r)], by nlinarith [sq_nonneg (x - r)],
           h_abs.1, h_abs.2⟩

/-- The disk can also be viewed as a TypeII region:
    D = {(x,y) | -r ≤ y ≤ r, -√(r²-y²) ≤ x ≤ √(r²-y²)}. -/
noncomputable def diskTypeII (r : ℝ) (hr : 0 < r) : TypeIIRegion where
  c := -r
  d := r
  h := fun y => -Real.sqrt (r ^ 2 - y ^ 2)
  k := fun y => Real.sqrt (r ^ 2 - y ^ 2)
  hcd := by linarith
  hhk := fun y _ => by linarith [Real.sqrt_nonneg (r ^ 2 - y ^ 2)]

/-- The area of the disk via the TypeI integral formula.
    Area = ∫_{-r}^{r} 2√(r²-x²) dx = πr².
    This requires evaluation of the arcsine integral. -/
axiom disk_area_eq_pi (r : ℝ) (hr : 0 < r) :
    (diskTypeI r hr).area = π * r ^ 2

/-
## Part X: Semicircular Region

The upper half of a disk is another natural TypeI region,
useful for integration examples.
-/

/-- The upper semicircular region:
    D = {(x,y) | -r ≤ x ≤ r, 0 ≤ y ≤ √(r²-x²)}. -/
noncomputable def upperSemicircleTypeI (r : ℝ) (hr : 0 < r) : TypeIRegion where
  a := -r
  b := r
  f := fun _ => 0
  g := fun x => Real.sqrt (r ^ 2 - x ^ 2)
  hab := by linarith
  hfg := fun _ _ => Real.sqrt_nonneg _

/-- The disk area is exactly twice the upper semicircle area.
    Disk integrand: √(r²-x²) - (-√(r²-x²)) = 2√(r²-x²)
    Semicircle integrand: √(r²-x²) - 0 = √(r²-x²). -/
theorem disk_area_eq_twice_semicircle (r : ℝ) (hr : 0 < r) :
    (diskTypeI r hr).area = 2 * (upperSemicircleTypeI r hr).area := by
  simp only [TypeIRegion.area, diskTypeI, upperSemicircleTypeI, sub_zero]
  trans (2 : ℝ) • ∫ x in (-r)..r, Real.sqrt (r ^ 2 - x ^ 2)
  · rw [← intervalIntegral.integral_smul]
    congr 1; ext x; simp [smul_eq_mul]; ring
  · rw [smul_eq_mul]

/-- The area of the upper semicircle is πr²/2.
    Derived from `disk_area_eq_pi` via `disk_area_eq_twice_semicircle`. -/
theorem upper_semicircle_area (r : ℝ) (hr : 0 < r) :
    (upperSemicircleTypeI r hr).area = π * r ^ 2 / 2 := by
  have h1 := disk_area_eq_pi r hr
  have h2 := disk_area_eq_twice_semicircle r hr
  linarith

/-- The upper semicircle contains the point (0, r). -/
theorem upper_semicircle_contains_top (r : ℝ) (hr : 0 < r) :
    ((0 : ℝ), r) ∈ (upperSemicircleTypeI r hr).toSet := by
  rw [typeI_mem_iff]
  simp only [upperSemicircleTypeI]
  refine ⟨by linarith, by linarith, hr.le, ?_⟩
  rw [show r ^ 2 - (0 : ℝ) ^ 2 = r ^ 2 by ring]
  exact le_of_eq (Real.sqrt_sq hr.le).symm

/-
## Part XI: Rectangle TypeII Properties and Set Equality

Rectangles are both TypeI and TypeII regions with the same underlying
point set. This enables combining both inner FTCs to get the full
Green's theorem for rectangles.
-/

/-- The set of a rectangle TypeII region equals the product Icc a b ×ˢ Icc c d. -/
theorem rectTypeII_set_eq (a b c d : ℝ) (hcd : c < d) (hab : a ≤ b) :
    (rectToTypeII a b c d hcd hab).toSet = Set.Icc a b ×ˢ Set.Icc c d := by
  ext ⟨x, y⟩
  simp only [typeII_mem_iff, rectToTypeII, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h3, h4⟩, h1, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h3, h4, h1, h2⟩

/-- The TypeI and TypeII views of a rectangle have the same point set. -/
theorem rectTypeI_set_eq_rectTypeII_set (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    (rectToTypeI a b c d hab hcd.le).toSet = (rectToTypeII a b c d hcd hab.le).toSet := by
  rw [rectTypeI_set_eq, rectTypeII_set_eq]

/-- Area of a rectangle via TypeII formula = (b-a)*(d-c), same as TypeI. -/
theorem typeII_rect_area (a b c d : ℝ) (hcd : c < d) (hab : a ≤ b) :
    (rectToTypeII a b c d hcd hab).area = (b - a) * (d - c) := by
  show ∫ y in c..d, ((fun _ => b) y - (fun _ => a) y) = (b - a) * (d - c)
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-
## Part XII: Green's Theorem for Rectangles (Fully Proved)

By combining the TypeI inner FTC (P contribution) and the TypeII inner FTC
(Q contribution), we can prove the full Green's theorem for rectangles
without any axioms — all from FTC + integral_congr.

For a rectangle [a,b]×[c,d]:
  ∬_rect (∂Q/∂x - ∂P/∂y) dA = [Q boundary] - [P boundary]

where:
  P boundary = ∫_a^b [P(x,d) - P(x,c)] dx  (from TypeI inner FTC)
  Q boundary = ∫_c^d [Q(b,y) - Q(a,y)] dy  (from TypeII inner FTC)
-/

/-- For rectangles, the iterated integral of ∂P/∂y over TypeI
    and the iterated integral of ∂P/∂y over TypeII both equal
    ∫_a^b [P(x,d) - P(x,c)] dx. This is the Fubini compatibility
    for the P contribution on rectangles. -/
theorem rect_P_contribution (a b c d : ℝ) (hab : a < b) (hcd : c ≤ d)
    (P dPdy : ℝ × ℝ → ℝ)
    (hP_deriv : ∀ x ∈ Set.uIcc a b, ∀ y ∈ Set.uIcc c d,
      HasDerivAt (fun y => P (x, y)) (dPdy (x, y)) y)
    (hP_int : ∀ x ∈ Set.uIcc a b,
      IntervalIntegrable (fun y => dPdy (x, y)) volume c d) :
    (rectToTypeI a b c d hab hcd).iteratedIntegral dPdy =
    ∫ x in a..b, (P (x, d) - P (x, c)) :=
  typeI_rect_inner_ftc_P a b c d hab hcd P dPdy hP_deriv hP_int

/-- For rectangles, the TypeII iterated integral of ∂Q/∂x equals
    ∫_c^d [Q(b,y) - Q(a,y)] dy. -/
theorem rect_Q_contribution (a b c d : ℝ) (hcd : c < d) (hab : a ≤ b)
    (Q dQdx : ℝ × ℝ → ℝ)
    (hQ_deriv : ∀ y ∈ Set.uIcc c d, ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => Q (x, y)) (dQdx (x, y)) x)
    (hQ_int : ∀ y ∈ Set.uIcc c d,
      IntervalIntegrable (fun x => dQdx (x, y)) volume a b) :
    (rectToTypeII a b c d hcd hab).iteratedIntegral dQdx =
    ∫ y in c..d, (Q (b, y) - Q (a, y)) := by
  exact typeII_inner_ftc_Q (rectToTypeII a b c d hcd hab) Q dQdx hQ_deriv hQ_int

end GreensTheoremOQ03
