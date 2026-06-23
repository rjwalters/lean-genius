import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Product of Segments of Chords — 3D Generalization (OQ-01)

## Open Question

From the parent theorem (Wiedijk #55 — intersecting chords in 2D circles):
> Generalization to 3D: for a sphere with center O and radius r, is the product
> PA * PB = |d² - r²| still invariant for all secant lines through P?

## Answer: YES — and the proof works in ANY inner product space.

The algebraic argument in the 2D proof uses only:
- Inner product expansion: ⟨P + t·dir, P + t·dir⟩ = ‖P‖² + 2t⟨P,dir⟩ + t²‖dir‖²
- Vieta's product formula for a monic quadratic
- The norm-squared identity ‖v‖² = ⟨v,v⟩

None of these depend on the dimension. Therefore the theorem holds for spheres in ℝ³,
in ℝⁿ, and more generally in any real inner product space.

## Main Results

1. `chord_quadratic_sphere`: Intersection points satisfy the same quadratic equation in any IPS.
2. `chord_roots_product_sphere`: Product of roots equals ‖P-O‖² - r² (Vieta).
3. `sphere_power_invariant`: |t₁|·|t₂| = r² - ‖P-O‖² (the power of a point, general).
4. `sphere_power_eq_chord_products`: Any two chords through P give equal products (3D statement).

## Status
- [x] Full proof with no sorries
- [x] Works in any real inner product space (subsumes 2D, 3D, nD)
- [x] Explicit 3D corollary
-/

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ── Part 1: The chord quadratic in a general inner product space ─── -/

/-- **Chord Quadratic (General)**

If `dir` is a unit vector and `P + t·dir` lies on the sphere of radius r centered at O
(translated so O = 0), then t satisfies: t² + 2t⟨P,dir⟩ + (‖P‖² - r²) = 0.

This is dimension-independent: the inner product expansion is the same in ℝ², ℝ³, and ℝⁿ. -/
theorem chord_quadratic_sphere (r : ℝ) (P dir : E) (t : ℝ)
    (hdir : ‖dir‖ = 1)
    (hOnSphere : ‖P + t • dir‖ = r) :
    t^2 + 2 * t * ⟪P, dir⟫_ℝ + (‖P‖^2 - r^2) = 0 := by
  have h1 : ‖P + t • dir‖^2 = r^2 := by rw [hOnSphere]; ring
  simp only [sq] at h1
  rw [← real_inner_self_eq_norm_mul_norm] at h1
  have expand : ⟪P + t • dir, P + t • dir⟫_ℝ =
      ⟪P, P⟫_ℝ + 2 * t * ⟪P, dir⟫_ℝ + t^2 * ⟪dir, dir⟫_ℝ := by
    rw [inner_add_left, inner_add_right, inner_add_right]
    rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    rw [real_inner_comm dir P]
    ring
  rw [expand] at h1
  have hdir2 : ⟪dir, dir⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, hdir]; ring
  rw [hdir2, real_inner_self_eq_norm_mul_norm] at h1
  simp only [sq]; linarith

/-! ── Part 2: Product of roots via Vieta's formula ─── -/

/-- **Sphere Chord Roots Product (General)**

If two distinct parameters t₁ ≠ t₂ both give points on the sphere along direction `dir`,
then t₁ · t₂ = ‖P‖² - r². This is Vieta's product formula for the chord quadratic. -/
theorem chord_roots_product_sphere (r : ℝ) (hr : 0 < r) (P dir : E) (t₁ t₂ : ℝ)
    (hdir : ‖dir‖ = 1)
    (hP : ‖P‖ < r)
    (ht₁ : ‖P + t₁ • dir‖ = r) (ht₂ : ‖P + t₂ • dir‖ = r)
    (hdiff : t₁ ≠ t₂) :
    t₁ * t₂ = ‖P‖^2 - r^2 := by
  have q1 := chord_quadratic_sphere r P dir t₁ hdir ht₁
  have q2 := chord_quadratic_sphere r P dir t₂ hdir ht₂
  -- Subtract the two quadratic equations to get (t₁ - t₂)(t₁ + t₂ + 2⟨P,dir⟩) = 0
  have hfactor : (t₁ - t₂) * (t₁ + t₂ + 2 * ⟪P, dir⟫_ℝ) = 0 := by ring_nf; linarith
  have hsum : t₁ + t₂ = -2 * ⟪P, dir⟫_ℝ := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact absurd (sub_eq_zero.mp h) hdiff
    · linarith
  -- Sum of squares from adding q1 + q2
  have hss : t₁^2 + t₂^2 + 2 * (t₁ + t₂) * ⟪P, dir⟫_ℝ + 2 * (‖P‖^2 - r^2) = 0 := by
    linarith
  rw [hsum] at hss
  -- (t₁ + t₂)² = t₁² + 2t₁t₂ + t₂²
  have hvieta : 4 * ⟪P, dir⟫_ℝ^2 = t₁^2 + t₂^2 + 2 * t₁ * t₂ := by
    have : (t₁ + t₂)^2 = t₁^2 + 2 * t₁ * t₂ + t₂^2 := by ring
    rw [hsum] at this; linarith
  linarith

/-- For P inside the sphere, the two chord parameters have opposite signs. -/
private theorem chord_roots_opp_signs_sphere (r : ℝ) (hr : 0 < r) (P dir : E) (t₁ t₂ : ℝ)
    (hdir : ‖dir‖ = 1) (hP : ‖P‖ < r)
    (ht₁ : ‖P + t₁ • dir‖ = r) (ht₂ : ‖P + t₂ • dir‖ = r)
    (hdiff : t₁ ≠ t₂) :
    t₁ * t₂ < 0 := by
  rw [chord_roots_product_sphere r hr P dir t₁ t₂ hdir hP ht₁ ht₂ hdiff]
  have : ‖P‖^2 < r^2 := by nlinarith [norm_nonneg P]
  linarith

/-! ── Part 3: The main theorem — power of a point in any IPS ─── -/

/-- **Sphere Power of a Point (General Inner Product Space)**

For a sphere with center O and radius r in any inner product space (including ℝ³, ℝⁿ),
if P is an interior point, then for any line through P with unit direction `dir`:

  |t₁| · |t₂| = r² - ‖P - O‖²

where t₁, t₂ are the parameters of the two intersection points with the sphere.

This answers OQ-01 affirmatively: the product of chord segments is invariant under
rotation of the secant line, in any dimension. -/
theorem sphere_power_invariant (O P : E) (r : ℝ) (hr : 0 < r)
    (hP : ‖P - O‖ < r)
    (dir : E) (hdir : ‖dir‖ = 1)
    (t₁ t₂ : ℝ) (hdiff : t₁ ≠ t₂)
    (ht₁ : ‖(P - O) + t₁ • dir‖ = r)
    (ht₂ : ‖(P - O) + t₂ • dir‖ = r) :
    |t₁| * |t₂| = r^2 - ‖P - O‖^2 := by
  -- Work with Q = P - O (translate so center is at origin)
  set Q := P - O with hQ
  have hprod := chord_roots_product_sphere r hr Q dir t₁ t₂ hdir hP ht₁ ht₂ hdiff
  have hneg := chord_roots_opp_signs_sphere r hr Q dir t₁ t₂ hdir hP ht₁ ht₂ hdiff
  rw [← abs_mul, abs_of_neg hneg, hprod]
  ring

/-- **Main Theorem: Chord Product Invariance on Spheres**

Any two secant lines through an interior point P of a sphere yield equal products
of chord segments. This is the n-dimensional Power of a Point theorem. -/
theorem sphere_chord_products_equal (O P : E) (r : ℝ) (hr : 0 < r)
    (hP : ‖P - O‖ < r)
    (dir₁ dir₂ : E) (hd₁ : ‖dir₁‖ = 1) (hd₂ : ‖dir₂‖ = 1)
    (s₁ s₂ t₁ t₂ : ℝ)
    (hs₁t₁ : s₁ ≠ s₂) (ht₁t₂ : t₁ ≠ t₂)
    (hs₁ : ‖(P - O) + s₁ • dir₁‖ = r) (hs₂ : ‖(P - O) + s₂ • dir₁‖ = r)
    (ht₁ : ‖(P - O) + t₁ • dir₂‖ = r) (ht₂ : ‖(P - O) + t₂ • dir₂‖ = r) :
    |s₁| * |s₂| = |t₁| * |t₂| := by
  rw [sphere_power_invariant O P r hr hP dir₁ hd₁ s₁ s₂ hs₁t₁ hs₁ hs₂,
      sphere_power_invariant O P r hr hP dir₂ hd₂ t₁ t₂ ht₁t₂ ht₁ ht₂]

/-! ── Part 4: Explicit 3D corollary ─── -/

/-- A sphere in 3D Euclidean space. -/
structure Sphere3D where
  center : EuclideanSpace ℝ (Fin 3)
  radius : ℝ
  radius_pos : 0 < radius

/-- A point lies on a sphere. -/
def onSphere (P : EuclideanSpace ℝ (Fin 3)) (S : Sphere3D) : Prop :=
  ‖P - S.center‖ = S.radius

/-- **Product of Chord Segments on a 3D Sphere**

For a sphere in ℝ³, if P is an interior point and two secant lines through P
intersect the sphere at (A₁, A₂) and (B₁, B₂), then PA₁·PA₂ = PB₁·PB₂.

This answers OQ-01: yes, the invariance holds in 3D. -/
theorem sphere3d_chord_products_equal (S : Sphere3D) (P : EuclideanSpace ℝ (Fin 3))
    (hP : ‖P - S.center‖ < S.radius)
    (A₁ A₂ B₁ B₂ : EuclideanSpace ℝ (Fin 3))
    (hA₁ : onSphere A₁ S) (hA₂ : onSphere A₂ S)
    (hB₁ : onSphere B₁ S) (hB₂ : onSphere B₂ S)
    -- A₁ = P + s₁·d₁, A₂ = P + s₂·d₁ (collinear with P along d₁)
    (d₁ : EuclideanSpace ℝ (Fin 3)) (hd₁ : ‖d₁‖ = 1) (s₁ s₂ : ℝ) (hs : s₁ ≠ s₂)
    (hA₁_eq : A₁ = P + s₁ • d₁) (hA₂_eq : A₂ = P + s₂ • d₁)
    -- B₁ = P + t₁·d₂, B₂ = P + t₂·d₂ (collinear with P along d₂)
    (d₂ : EuclideanSpace ℝ (Fin 3)) (hd₂ : ‖d₂‖ = 1) (t₁ t₂ : ℝ) (ht : t₁ ≠ t₂)
    (hB₁_eq : B₁ = P + t₁ • d₂) (hB₂_eq : B₂ = P + t₂ • d₂) :
    ‖A₁ - P‖ * ‖A₂ - P‖ = ‖B₁ - P‖ * ‖B₂ - P‖ := by
  -- Rewrite distances in terms of parameters
  have hPA₁ : ‖A₁ - P‖ = |s₁| := by
    rw [hA₁_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hd₁, mul_one]
  have hPA₂ : ‖A₂ - P‖ = |s₂| := by
    rw [hA₂_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hd₁, mul_one]
  have hPB₁ : ‖B₁ - P‖ = |t₁| := by
    rw [hB₁_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hd₂, mul_one]
  have hPB₂ : ‖B₂ - P‖ = |t₂| := by
    rw [hB₂_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hd₂, mul_one]
  rw [hPA₁, hPA₂, hPB₁, hPB₂]
  -- Convert onSphere to the parametric form
  have hs₁_circ : ‖(P - S.center) + s₁ • d₁‖ = S.radius := by
    have : A₁ - S.center = (P - S.center) + s₁ • d₁ := by rw [hA₁_eq]; abel
    rwa [← this, ← hA₁]
  have hs₂_circ : ‖(P - S.center) + s₂ • d₁‖ = S.radius := by
    have : A₂ - S.center = (P - S.center) + s₂ • d₁ := by rw [hA₂_eq]; abel
    rwa [← this, ← hA₂]
  have ht₁_circ : ‖(P - S.center) + t₁ • d₂‖ = S.radius := by
    have : B₁ - S.center = (P - S.center) + t₁ • d₂ := by rw [hB₁_eq]; abel
    rwa [← this, ← hB₁]
  have ht₂_circ : ‖(P - S.center) + t₂ • d₂‖ = S.radius := by
    have : B₂ - S.center = (P - S.center) + t₂ • d₂ := by rw [hB₂_eq]; abel
    rwa [← this, ← hB₂]
  exact sphere_chord_products_equal S.center P S.radius S.radius_pos hP
    d₁ d₂ hd₁ hd₂ s₁ s₂ t₁ t₂ hs ht hs₁_circ hs₂_circ ht₁_circ ht₂_circ

/-!
## Conclusion

The open question OQ-01 is resolved:

**Theorem**: For a sphere with center O and radius r in ℝⁿ (or any inner product space),
and an interior point P with distance d = ‖P - O‖ < r, the product of chord segment
lengths is invariant:

  PA · PB = r² - d²

for any secant line through P with endpoints A, B on the sphere.

**Proof**: The algebraic argument is dimension-independent. The chord intersection
equation `t² + 2t⟨P-O, dir⟩ + (‖P-O‖² - r²) = 0` involves only inner products and norms,
which are defined in any inner product space. Vieta's formula gives t₁·t₂ = ‖P-O‖² - r²,
and since t₁, t₂ have opposite signs (P inside the sphere), |t₁|·|t₂| = r² - ‖P-O‖².
-/

#check @sphere_power_invariant
#check @sphere_chord_products_equal
#check @sphere3d_chord_products_equal
