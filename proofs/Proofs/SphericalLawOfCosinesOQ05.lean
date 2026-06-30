/-
# Spherical Law of Cosines — OQ-05: the Haversine Formula

This file is the S1 OBSERVE scaffold for OQ-05 of the parent
gallery entry `spherical-law-of-cosines`.

## The OPEN question

The parent `SphericalLawOfCosines.lean` proves

  cos(c) = cos(a)·cos(b) + sin(a)·sin(b)·cos(C)

for a spherical triangle with sides `a, b, c` and dihedral angle
`C` opposite side `c`.

OQ-05 asks to formalise the *haversine* form:

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C)

where `hav(θ) := sin²(θ/2) = (1 − cos θ) / 2`.

This is the numerically stable formulation of the spherical
law of cosines used in navigation and GPS coordinate
computations: for tiny great-circle distances the standard
`arccos` form suffers from catastrophic cancellation, whereas
the haversine remains well-conditioned because `hav` is the
half-angle squared sine.

## What this file contains

* `haversine : ℝ → ℝ` — the haversine function `sin²(θ/2)`.
* The half-angle identity `haversine_eq_one_sub_cos_div_two`.
* Elementary range/sign lemmas (`haversine_nonneg`,
  `haversine_zero`, `haversine_pi`, `haversine_eq_zero_iff`).
* The **pure algebraic** form of the haversine formula,
  proved unconditionally from the planar identity
  `cos(a − b) = cos a · cos b + sin a · sin b` plus a hypothesis
  that the spherical law of cosines holds for `(a, b, c, C)`:
  `haversine_formula_algebraic`.
* The corresponding `SphericalTriangle` version, `haversine_formula`,
  is closed in S2 via the bridge lemma
  `inner_projectPerp_eq_sin_sin_cos_angleC`, which converts the
  parent's projection-inner-product term
  `⟨projectPerp A C, projectPerp B C⟩` into the
  `sin(a) · sin(b) · cos(angleC)` form using
  `norm_projectPerp_eq_sin` from the parent file together with
  a case split on the degenerate projection (matching `angleC`'s
  dependent-`if` definition).

## Strategy for `haversine_formula` (CLOSED at S2)

The proof factors through `haversine_formula_algebraic`. The
only obstacle is the parent's `spherical_law_of_cosines_trig`
states the spherical law of cosines in the form

  cos(t.sideC) = cos(t.sideB) · cos(t.sideA) +
                 ⟨projectPerp t.A t.C, projectPerp t.B t.C⟩

rather than the `sin(a)·sin(b)·cos(C)` form. Bridging requires
the identity

  ⟨projectPerp A C, projectPerp B C⟩
    = ‖projectPerp A C‖ · ‖projectPerp B C‖ · cos(angleC)
    = sin(sideB) · sin(sideA) · cos(angleC),

valid on the non-degenerate branch of `angleC` (where both
projections are nonzero, equivalently where neither `sideA` nor
`sideB` is `0` or `π`). The degenerate branch coincides with
the case `sin(sideA) · sin(sideB) = 0`, where the cross-term
vanishes on both sides — the haversine formula then degenerates
to `hav(c) = hav(a − b)`, which under either degeneracy follows
directly from `c = ±(a − b)` (mod 2π).

## Next iterations

* **S2 (this iteration, CLOSED)**: discharged `haversine_formula` from
  `haversine_formula_algebraic` via `cos_sideC_trig_form`, in turn proved
  via the bridge lemma `inner_projectPerp_eq_sin_sin_cos_angleC` with
  the planned non-degenerate / degenerate case split on `angleC`.
* **S3**: navigation / GPS applications — Mercator and ECEF
  conversion lemmas, great-circle distance computation in
  haversine form.
* **S4**: inverse formula `sideC = 2 · arcsin(√(haversine sideC))`
  for short-distance numerical stability.
-/

import Proofs.SphericalLawOfCosines

namespace SphericalLawOfCosinesOQ05

open Real SphericalLawOfCosines

set_option linter.unusedVariables false
set_option linter.unusedTactic false

/- ## Part I: The haversine function -/

/-- The haversine function: `hav(θ) := sin²(θ/2)`. -/
noncomputable def haversine (θ : ℝ) : ℝ := Real.sin (θ / 2) ^ 2

/-- The half-angle identity: `hav(θ) = (1 − cos θ) / 2`.

Derived from `Real.cos_two_mul` and `Real.sin_sq_add_cos_sq`:
`cos(2 · (θ/2)) = 2 · cos²(θ/2) − 1 = 1 − 2 · sin²(θ/2)`,
so `cos θ = 1 − 2 · sin²(θ/2)`, hence `sin²(θ/2) = (1 − cos θ)/2`. -/
theorem haversine_eq_one_sub_cos_div_two (θ : ℝ) :
    haversine θ = (1 - Real.cos θ) / 2 := by
  unfold haversine
  have h1 := Real.cos_two_mul (θ / 2)
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  have heq : 2 * (θ / 2) = θ := by ring
  rw [heq] at h1
  linarith

/-- Equivalent form: `2 · hav(θ) = 1 − cos θ`. -/
theorem two_haversine_eq (θ : ℝ) :
    2 * haversine θ = 1 - Real.cos θ := by
  rw [haversine_eq_one_sub_cos_div_two]; ring

/-- `cos θ = 1 − 2 · hav(θ)`. -/
theorem cos_eq_one_sub_two_haversine (θ : ℝ) :
    Real.cos θ = 1 - 2 * haversine θ := by
  rw [haversine_eq_one_sub_cos_div_two]; ring

/- ## Part II: Range and elementary properties -/

/-- The haversine is nonnegative. -/
theorem haversine_nonneg (θ : ℝ) : 0 ≤ haversine θ := by
  unfold haversine; exact sq_nonneg _

/-- The haversine is at most `1`. -/
theorem haversine_le_one (θ : ℝ) : haversine θ ≤ 1 := by
  rw [haversine_eq_one_sub_cos_div_two]
  have h : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  linarith

/-- `hav(0) = 0`. -/
theorem haversine_zero : haversine 0 = 0 := by
  unfold haversine; simp

/-- `hav(π) = 1`. -/
theorem haversine_pi : haversine π = 1 := by
  rw [haversine_eq_one_sub_cos_div_two, Real.cos_pi]; ring

/-- The haversine is even: `hav(−θ) = hav(θ)`. -/
theorem haversine_neg (θ : ℝ) : haversine (-θ) = haversine θ := by
  rw [haversine_eq_one_sub_cos_div_two, haversine_eq_one_sub_cos_div_two,
      Real.cos_neg]

/- ## Part III: The algebraic haversine formula

This is the content-bearing identity. Given the spherical law of
cosines `cos c = cos a · cos b + sin a · sin b · cos C` as a
hypothesis on the reals, the haversine form follows by linear
arithmetic combined with the planar identity `cos(a − b) = cos a ·
cos b + sin a · sin b`.

The proof is purely algebraic; no spherical geometry is required.
-/

/-- **Haversine formula, algebraic form.**

Given the spherical law of cosines as a hypothesis on the reals,

  cos c = cos a · cos b + sin a · sin b · cos C,

the haversine identity

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C)

follows by linear arithmetic from the planar subtraction formula
`Real.cos_sub` and the half-angle identity. -/
theorem haversine_formula_algebraic (a b c C : ℝ)
    (h_SLC : Real.cos c =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C) :
    haversine c =
      haversine (a - b) + Real.sin a * Real.sin b * haversine C := by
  rw [haversine_eq_one_sub_cos_div_two c,
      haversine_eq_one_sub_cos_div_two (a - b),
      haversine_eq_one_sub_cos_div_two C,
      Real.cos_sub a b]
  linarith [h_SLC]

/-- **Algebraic corollary**: the haversine formula is *equivalent*
to the spherical law of cosines (algebraic form). The forward
direction is `haversine_formula_algebraic`; this provides the
reverse direction. Both are linear-arithmetic restatements of the
same identity in different cordinates. -/
theorem cos_form_of_haversine_formula (a b c C : ℝ)
    (h_hav : haversine c =
      haversine (a - b) + Real.sin a * Real.sin b * haversine C) :
    Real.cos c =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C := by
  have h1 : haversine c = (1 - Real.cos c) / 2 :=
    haversine_eq_one_sub_cos_div_two c
  have h2 : haversine (a - b) = (1 - Real.cos (a - b)) / 2 :=
    haversine_eq_one_sub_cos_div_two (a - b)
  have h3 : haversine C = (1 - Real.cos C) / 2 :=
    haversine_eq_one_sub_cos_div_two C
  have h4 : Real.cos (a - b) = Real.cos a * Real.cos b +
      Real.sin a * Real.sin b := Real.cos_sub a b
  rw [h1, h2, h3] at h_hav
  linarith

/- ## Part IV: The `SphericalTriangle` version (OPEN)

This is the form OQ-05 actually asks for: the haversine identity
applied to a `SphericalTriangle` from the parent file, using the
parent's `sideA`, `sideB`, `sideC`, and `angleC`.

The bridge to `haversine_formula_algebraic` requires converting
the parent's projection-inner-product term

  ⟨projectPerp t.A t.C, projectPerp t.B t.C⟩

into the trigonometric form

  sin(t.sideB) · sin(t.sideA) · cos(t.angleC).

This conversion is non-trivial because `t.angleC` is defined via
`arccos` with a degenerate-case fallback to `0`. On the
non-degenerate branch, the identity follows from
`norm_projectPerp_eq_sin` and the standard
`cos = ⟨·,·⟩ / (‖·‖·‖·‖)` formula. The degenerate branch
(`‖projectPerp t.A t.C‖ = 0` or `‖projectPerp t.B t.C‖ = 0`) is
exactly the locus where `sin(t.sideA) · sin(t.sideB) = 0`, so the
cross-term vanishes on both sides.

This conversion is deferred to S2. -/

/- **Haversine formula for a spherical triangle.**

For any spherical triangle with sides `a := t.sideB`, `b := t.sideA`,
`c := t.sideC` and dihedral angle `C := t.angleC` at vertex `t.C`,

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C).

**Status**: CLOSED at S2. The pure algebraic identity is proved
unconditionally as `haversine_formula_algebraic`. The conversion
of the parent's projection-inner-product form of the spherical
law of cosines into the trigonometric form
`cos c = cos a · cos b + sin a · sin b · cos C` is supplied by
`inner_projectPerp_eq_sin_sin_cos_angleC` below, which case-splits
on the degenerate projection branch matching `t.angleC`'s
definition. -/

/-- **Bridge lemma (S2)**: the projection inner-product term in
`SphericalLawOfCosines.spherical_law_of_cosines_trig` equals the
trigonometric expression `sin(t.sideB) · sin(t.sideA) · cos(t.angleC)`.

This is the geometric content needed to convert the parent's
projection form

  cos(t.sideC) = cos(t.sideB) · cos(t.sideA) + ⟨projectPerp A C, projectPerp B C⟩

into the standard trigonometric form

  cos(t.sideC) = cos(t.sideB) · cos(t.sideA) + sin(t.sideB) · sin(t.sideA) · cos(t.angleC).

**Proof outline.** Let `projA := projectPerp t.A t.C`, `projB := projectPerp t.B t.C`.
By `norm_projectPerp_eq_sin` we have `‖projA‖ = sin t.sideB` and
`‖projB‖ = sin t.sideA`. Case split:

* **Non-degenerate** (`‖projA‖ ≠ 0` and `‖projB‖ ≠ 0`): `t.angleC` unfolds to
  `Real.arccos (⟨projA, projB⟩ / (‖projA‖ · ‖projB‖))`. The argument lies in `[-1, 1]`
  by Cauchy–Schwarz, so `Real.cos_arccos` applies and gives
  `cos t.angleC = ⟨projA, projB⟩ / (‖projA‖ · ‖projB‖)`. Multiplying through by
  `‖projA‖ · ‖projB‖ = sin t.sideB · sin t.sideA` recovers `⟨projA, projB⟩`.
* **Degenerate** (`‖projA‖ = 0` or `‖projB‖ = 0`): `t.angleC = 0` by definition, so
  `cos t.angleC = 1`. One of the projections is the zero vector, hence
  `⟨projA, projB⟩ = 0`. The corresponding `sin t.sideB = 0` (resp. `sin t.sideA = 0`)
  via the `norm_projectPerp_eq_sin` bridge, so the RHS is also `0`. -/
theorem inner_projectPerp_eq_sin_sin_cos_angleC (t : SphericalTriangle) :
    @inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C) =
      Real.sin t.sideB * Real.sin t.sideA * Real.cos t.angleC := by
  have h_normA : ‖projectPerp t.A t.C‖ = Real.sin t.sideB :=
    norm_projectPerp_eq_sin t.A t.C t.hA t.hC
  have h_normB : ‖projectPerp t.B t.C‖ = Real.sin t.sideA :=
    norm_projectPerp_eq_sin t.B t.C t.hB t.hC
  by_cases h_deg : ‖projectPerp t.A t.C‖ = 0 ∨ ‖projectPerp t.B t.C‖ = 0
  · -- Degenerate branch: cos t.angleC = 1 (cos 0), but the cross-term sin·sin still
    -- vanishes because one of the sines is 0.
    have h_angle_zero : t.angleC = 0 := by
      simp only [SphericalTriangle.angleC, dif_pos h_deg]
    rw [h_angle_zero, Real.cos_zero, mul_one]
    rcases h_deg with hA0 | hB0
    · have h_zeroA : projectPerp t.A t.C = 0 := norm_eq_zero.mp hA0
      have h_sinB : Real.sin t.sideB = 0 := h_normA.symm.trans hA0
      rw [h_zeroA, inner_zero_left, h_sinB, zero_mul]
    · have h_zeroB : projectPerp t.B t.C = 0 := norm_eq_zero.mp hB0
      have h_sinA : Real.sin t.sideA = 0 := h_normB.symm.trans hB0
      rw [h_zeroB, inner_zero_right, h_sinA, mul_zero]
  · -- Non-degenerate branch
    push_neg at h_deg
    obtain ⟨hA_ne, hB_ne⟩ := h_deg
    have h_normA_pos : 0 < ‖projectPerp t.A t.C‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA_ne)
    have h_normB_pos : 0 < ‖projectPerp t.B t.C‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hB_ne)
    have h_prod_pos : 0 < ‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖ :=
      mul_pos h_normA_pos h_normB_pos
    have h_prod_ne : ‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖ ≠ 0 :=
      h_prod_pos.ne'
    -- Cauchy–Schwarz: |⟨projA, projB⟩| ≤ ‖projA‖ · ‖projB‖
    have h_cs : |@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C)| ≤
        ‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖ :=
      abs_real_inner_le_norm _ _
    have h_cs' := abs_le.mp h_cs
    -- Bounds for arccos argument
    have h_div_le :
        (@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C)) /
          (‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖) ≤ 1 :=
      (div_le_one h_prod_pos).mpr h_cs'.2
    have h_div_ge :
        -1 ≤ (@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C)) /
              (‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖) := by
      rw [le_div_iff₀ h_prod_pos]; linarith [h_cs'.1]
    -- Unfold t.angleC on the non-degenerate branch
    have h_not_deg : ¬ (‖projectPerp t.A t.C‖ = 0 ∨ ‖projectPerp t.B t.C‖ = 0) :=
      not_or.mpr ⟨hA_ne, hB_ne⟩
    have h_angle_eq : t.angleC = Real.arccos
        ((@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C)) /
         (‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖)) := by
      simp only [SphericalTriangle.angleC, dif_neg h_not_deg]
    rw [h_angle_eq, Real.cos_arccos h_div_ge h_div_le, ← h_normA, ← h_normB]
    field_simp

/-- **Trigonometric form of the spherical law of cosines.** Combines the parent's
`spherical_law_of_cosines_trig` (projection-inner-product form) with the bridge
lemma `inner_projectPerp_eq_sin_sin_cos_angleC` to obtain the textbook identity. -/
theorem cos_sideC_trig_form (t : SphericalTriangle) :
    Real.cos t.sideC =
      Real.cos t.sideB * Real.cos t.sideA +
        Real.sin t.sideB * Real.sin t.sideA * Real.cos t.angleC := by
  rw [spherical_law_of_cosines_trig, inner_projectPerp_eq_sin_sin_cos_angleC]

/-- **Haversine formula for a spherical triangle (S2: CLOSED).**

For any spherical triangle with sides `a := t.sideB`, `b := t.sideA`,
`c := t.sideC` and dihedral angle `C := t.angleC` at vertex `t.C`,

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C).

Discharges the S1 `sorry` by routing through `cos_sideC_trig_form` (S2 bridge from
the parent's projection-inner-product form) and `haversine_formula_algebraic`
(unconditional algebraic identity). -/
theorem haversine_formula (t : SphericalTriangle) :
    haversine t.sideC =
      haversine (t.sideB - t.sideA) +
        Real.sin t.sideB * Real.sin t.sideA * haversine t.angleC :=
  haversine_formula_algebraic t.sideB t.sideA t.sideC t.angleC
    (cos_sideC_trig_form t)

/- ## Part V: Specialised consequences (unconditional small cases) -/

/-- **Degenerate triangle with side `b = 0`** (i.e. `t.A = t.C`):
the haversine identity reduces to the trivial `hav(c) = hav(c)`
because both the haversine of `t.sideB - t.sideA = -t.sideA` and
the cross-term `sin(t.sideB) · sin(t.sideA) · hav(angleC)`
collapse appropriately when `sideB = 0`. We record only the
shape-level fact that this case is non-vacuous. -/
theorem haversine_formula_holds_when_sin_sideA_zero
    (a b c C : ℝ) (h_sin : Real.sin a = 0)
    (h_SLC : Real.cos c =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C) :
    haversine c =
      haversine (a - b) + Real.sin a * Real.sin b * haversine C :=
  haversine_formula_algebraic a b c C h_SLC

/-- The haversine of a difference is symmetric in the arguments
(modulo sign): `hav(a − b) = hav(b − a)`. Used implicitly when
swapping the role of sides A and B. -/
theorem haversine_sub_comm (a b : ℝ) :
    haversine (a - b) = haversine (b - a) := by
  have : a - b = -(b - a) := by ring
  rw [this, haversine_neg]

/- ## Part VII: Inverse haversine formula (S3)

The forward haversine formula proved above is half of the navigation
pipeline: it computes `hav(c)` from `a, b, C`. The other half is the
inverse — recovering the great-circle distance `c` from `hav(c)`.

On the principal range `[0, π]` (which is exactly where arc-lengths
on the sphere live), the inverse is

  c = 2 · arcsin(√(hav c)).

Two facts justify this:

* `sin(c/2) ≥ 0` for `c/2 ∈ [0, π/2]`, so `√(sin²(c/2)) = sin(c/2)`,
  i.e. `√(hav c) = sin(c/2)`.
* `arcsin(sin x) = x` on `[-π/2, π/2]`, and `c/2 ∈ [0, π/2]` since
  `c ∈ [0, π]`. So `2 · arcsin(sin(c/2)) = c`.

Composed with the forward `haversine_formula`, this gives the
standard navigation identity

  c = 2 · arcsin(√(hav(a − b) + sin(a) · sin(b) · hav(C))).

The parent gallery's `arcLength_nonneg` and `arcLength_le_pi` show
that the sides of a `SphericalTriangle` always satisfy `0 ≤ side ≤ π`,
so the inverse applies unconditionally. -/

/-- `sin(θ/2) ≥ 0` for `θ ∈ [0, π]`. -/
theorem sin_half_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    0 ≤ Real.sin (θ / 2) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · linarith
  · linarith [Real.pi_pos]

/-- `√(haversine θ) = sin(θ/2)` for `θ ∈ [0, π]`. The square root
collapses because `sin(θ/2)` is nonnegative on this range. -/
theorem sqrt_haversine_eq_sin_half {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    Real.sqrt (haversine θ) = Real.sin (θ / 2) := by
  unfold haversine
  exact Real.sqrt_sq (sin_half_nonneg h0 hπ)

/-- **Inverse haversine formula (general form).** On the principal
range `[0, π]` of arc-lengths, the haversine is invertible:

  θ = 2 · arcsin(√(hav θ)).

This is the formula used in navigation pipelines to recover the
great-circle distance from the haversine. -/
theorem eq_two_arcsin_sqrt_haversine {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    θ = 2 * Real.arcsin (Real.sqrt (haversine θ)) := by
  rw [sqrt_haversine_eq_sin_half h0 hπ]
  have h1 : -(π / 2) ≤ θ / 2 := by linarith [Real.pi_pos]
  have h2 : θ / 2 ≤ π / 2 := by linarith
  rw [Real.arcsin_sin h1 h2]
  ring

/-- **Inverse haversine for `sideC`.** Recovers `t.sideC` from
`haversine t.sideC`. -/
theorem sideC_eq_two_arcsin_sqrt_haversine (t : SphericalTriangle) :
    t.sideC = 2 * Real.arcsin (Real.sqrt (haversine t.sideC)) :=
  eq_two_arcsin_sqrt_haversine
    (arcLength_nonneg t.A t.B t.hA t.hB)
    (arcLength_le_pi t.A t.B t.hA t.hB)

/-- **Inverse haversine for `sideA`.** -/
theorem sideA_eq_two_arcsin_sqrt_haversine (t : SphericalTriangle) :
    t.sideA = 2 * Real.arcsin (Real.sqrt (haversine t.sideA)) :=
  eq_two_arcsin_sqrt_haversine
    (arcLength_nonneg t.B t.C t.hB t.hC)
    (arcLength_le_pi t.B t.C t.hB t.hC)

/-- **Inverse haversine for `sideB`.** -/
theorem sideB_eq_two_arcsin_sqrt_haversine (t : SphericalTriangle) :
    t.sideB = 2 * Real.arcsin (Real.sqrt (haversine t.sideB)) :=
  eq_two_arcsin_sqrt_haversine
    (arcLength_nonneg t.A t.C t.hA t.hC)
    (arcLength_le_pi t.A t.C t.hA t.hC)

/-- **Great-circle distance via haversine (the navigation identity).**

Combines the forward `haversine_formula` with the inverse formula to
give the canonical end-to-end great-circle distance computation:

  c = 2 · arcsin(√(hav(a − b) + sin(a) · sin(b) · hav(C))).

In navigation/GPS pipelines, the arguments `a, b, C` come from
latitudes and the longitude difference; the RHS is evaluated in
floating point and produces `c` directly without ever touching
`arccos` near `1`. -/
theorem sideC_eq_great_circle_haversine (t : SphericalTriangle) :
    t.sideC = 2 * Real.arcsin (Real.sqrt
      (haversine (t.sideB - t.sideA) +
        Real.sin t.sideB * Real.sin t.sideA * haversine t.angleC)) := by
  rw [← haversine_formula t]
  exact sideC_eq_two_arcsin_sqrt_haversine t

/- ## Part IX: Strict monotonicity, injectivity, and navigation uniqueness (S4)

The forward `haversine_formula` (S2) and inverse `eq_two_arcsin_sqrt_haversine`
(S3) define a navigation pipeline that recovers the great-circle distance
`c` from `(a, b, C)`. For this pipeline to be unambiguous, the haversine
must be *injective* on the principal range `[0, π]` of arc-lengths -
otherwise two different `c` values could produce the same haversine,
and the inverse step would not be well-defined as a function.

Injectivity follows from strict monotonicity, which in turn follows
from `Real.strictAntiOn_cos` (strict antitonicity of `cos` on `[0, π]`)
combined with the half-angle identity `haversine = (1 - cos)/2`.

The downstream corollary `arcLength_eq_of_haversine_eq` lifts the
injectivity from real arc-lengths to the parent gallery's arc-lengths
between unit vectors, and `sideC_eq_of_haversine_sideC_eq` records the
two-spherical-triangles statement: equal haversines for `sideC` imply
equal `sideC`s. -/

/-- **Strict monotonicity** of `haversine` on the principal range `[0, π]`.

Follows from `Real.strictAntiOn_cos` (strict antitonicity of `cos` on `[0, π]`)
plus the half-angle identity `haversine = (1 - cos)/2`. -/
theorem haversine_strictMonoOn_Icc_zero_pi :
    StrictMonoOn haversine (Set.Icc 0 π) := by
  intro x hx y hy hxy
  rw [haversine_eq_one_sub_cos_div_two x, haversine_eq_one_sub_cos_div_two y]
  have h_cos_lt : Real.cos y < Real.cos x := Real.strictAntiOn_cos hx hy hxy
  linarith

/-- **Injectivity** of `haversine` on `[0, π]`. The recovery of the
great-circle distance from its haversine is well-defined. -/
theorem haversine_injOn_Icc_zero_pi :
    Set.InjOn haversine (Set.Icc 0 π) :=
  haversine_strictMonoOn_Icc_zero_pi.injOn

/-- **Order characterisation**: on the principal range `[0, π]`,
`hav x < hav y ↔ x < y`. -/
theorem haversine_lt_haversine_iff_lt {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) π) (hy : y ∈ Set.Icc (0 : ℝ) π) :
    haversine x < haversine y ↔ x < y :=
  haversine_strictMonoOn_Icc_zero_pi.lt_iff_lt hx hy

/-- **Equality characterisation**: on the principal range `[0, π]`,
`hav x = hav y ↔ x = y`. -/
theorem haversine_eq_haversine_iff_eq {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) π) (hy : y ∈ Set.Icc (0 : ℝ) π) :
    haversine x = haversine y ↔ x = y :=
  ⟨fun h => haversine_injOn_Icc_zero_pi hx hy h, fun h => by rw [h]⟩

/-- **Generic arc-length injectivity via haversine.** For any four unit
vectors, equal haversines of the arc-lengths imply equal arc-lengths.

This lifts `haversine_injOn_Icc_zero_pi` from real numbers to the
parent gallery's arc-lengths, using `arcLength_nonneg` and
`arcLength_le_pi` to confirm membership in `[0, π]`. -/
theorem arcLength_eq_of_haversine_eq
    {u v u' v' : Vec3} (hu : IsUnitVec u) (hv : IsUnitVec v)
    (hu' : IsUnitVec u') (hv' : IsUnitVec v')
    (h : haversine (arcLength u v) = haversine (arcLength u' v')) :
    arcLength u v = arcLength u' v' :=
  haversine_injOn_Icc_zero_pi
    ⟨arcLength_nonneg u v hu hv, arcLength_le_pi u v hu hv⟩
    ⟨arcLength_nonneg u' v' hu' hv', arcLength_le_pi u' v' hu' hv'⟩
    h

/-- **Two-triangle navigation uniqueness.** If two spherical triangles
have equal haversines for `sideC`, their `sideC`s are equal.

Formalises the well-definedness of great-circle distance recovery: a
given haversine value uniquely determines its arc-length on the sphere,
so the inverse step in the navigation pipeline produces no ambiguity. -/
theorem sideC_eq_of_haversine_sideC_eq (t₁ t₂ : SphericalTriangle)
    (h : haversine t₁.sideC = haversine t₂.sideC) :
    t₁.sideC = t₂.sideC :=
  arcLength_eq_of_haversine_eq t₁.hA t₁.hB t₂.hA t₂.hB h

/-- **Two-triangle uniqueness for sideA.** -/
theorem sideA_eq_of_haversine_sideA_eq (t₁ t₂ : SphericalTriangle)
    (h : haversine t₁.sideA = haversine t₂.sideA) :
    t₁.sideA = t₂.sideA :=
  arcLength_eq_of_haversine_eq t₁.hB t₁.hC t₂.hB t₂.hC h

/-- **Two-triangle uniqueness for sideB.** -/
theorem sideB_eq_of_haversine_sideB_eq (t₁ t₂ : SphericalTriangle)
    (h : haversine t₁.sideB = haversine t₂.sideB) :
    t₁.sideB = t₂.sideB :=
  arcLength_eq_of_haversine_eq t₁.hA t₁.hC t₂.hA t₂.hC h

/-- **Vanishing-haversine characterisation** on the principal range.
On `[0, π]`, `hav θ = 0 ↔ θ = 0`. -/
theorem haversine_eq_zero_iff_of_mem_Icc {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) π) :
    haversine θ = 0 ↔ θ = 0 := by
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) π :=
    ⟨le_refl 0, Real.pi_pos.le⟩
  have h := haversine_eq_haversine_iff_eq hθ h0_mem
  rw [haversine_zero] at h
  exact h

/- ## Part X: The haversine bijection `[0, π] ≃ [0, 1]` (S5)

S4 established that `haversine` is *strictly monotone* (hence injective) on the
principal range `[0, π]`. This part completes the picture by proving it is also
*surjective* onto `[0, 1]`, so the forward map and the inverse
`2 · arcsin(√·)` (S3) are mutually inverse bijections between `[0, π]` and
`[0, 1]`.

Surjectivity is *constructive* and needs no intermediate-value argument: for any
target `y ∈ [0, 1]`, the explicit preimage `2 · arcsin(√y)` lies in `[0, π]` and
maps to `y`, because `sin(arcsin(√y)) = √y` and `(√y)² = y`. This is the exact
range statement underlying the navigation recovery — every admissible haversine
value `y ∈ [0, 1]` is realised by a unique great-circle distance `c ∈ [0, π]`. -/

/-- **Right inverse / realisability**: every `y ∈ [0, 1]` is the haversine of its
explicit preimage `2 · arcsin(√y)`. Purely algebraic: `sin(arcsin √y) = √y`
(since `0 ≤ √y ≤ 1`) and `(√y)² = y` (since `0 ≤ y`). -/
theorem haversine_two_arcsin_sqrt {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    haversine (2 * Real.arcsin (Real.sqrt y)) = y := by
  have hsqrt_le : Real.sqrt y ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt h1
  have hhalf : (2 * Real.arcsin (Real.sqrt y)) / 2 = Real.arcsin (Real.sqrt y) := by
    ring
  unfold haversine
  rw [hhalf, Real.sin_arcsin (by linarith [Real.sqrt_nonneg y]) hsqrt_le,
      Real.sq_sqrt h0]

/-- The explicit preimage `2 · arcsin(√y)` always lies in the principal range
`[0, π]` (its half lies in `[0, π/2]` since `arcsin ≥ 0` on nonnegative inputs and
`arcsin ≤ π/2` always). -/
theorem two_arcsin_sqrt_mem_Icc (y : ℝ) :
    2 * Real.arcsin (Real.sqrt y) ∈ Set.Icc (0 : ℝ) π := by
  refine ⟨?_, ?_⟩
  · have h := Real.arcsin_nonneg.mpr (Real.sqrt_nonneg y)
    linarith
  · have h := Real.arcsin_le_pi_div_two (Real.sqrt y)
    linarith

/-- **`haversine` maps `[0, π]` into `[0, 1]`** (the codomain statement). -/
theorem haversine_mapsTo :
    Set.MapsTo haversine (Set.Icc (0 : ℝ) π) (Set.Icc (0 : ℝ) 1) :=
  fun θ _ => ⟨haversine_nonneg θ, haversine_le_one θ⟩

/-- **`haversine` is surjective from `[0, π]` onto `[0, 1]`.** Constructive: the
preimage of `y` is `2 · arcsin(√y)`. -/
theorem haversine_surjOn :
    Set.SurjOn haversine (Set.Icc (0 : ℝ) π) (Set.Icc (0 : ℝ) 1) := by
  intro y hy
  obtain ⟨h0, h1⟩ := hy
  exact ⟨2 * Real.arcsin (Real.sqrt y), two_arcsin_sqrt_mem_Icc y,
    haversine_two_arcsin_sqrt h0 h1⟩

/-- **The haversine bijection.** `haversine` is a bijection from the principal
arc-length range `[0, π]` onto the haversine range `[0, 1]`. Combined with the
inverse `eq_two_arcsin_sqrt_haversine` (S3), this makes great-circle distance
recovery a genuine two-sided inverse, not merely a one-sided formula. -/
theorem haversine_bijOn :
    Set.BijOn haversine (Set.Icc (0 : ℝ) π) (Set.Icc (0 : ℝ) 1) :=
  ⟨haversine_mapsTo, haversine_injOn_Icc_zero_pi, haversine_surjOn⟩

/-- **Image characterisation**: `haversine '' [0, π] = [0, 1]`. -/
theorem haversine_image_Icc :
    haversine '' (Set.Icc (0 : ℝ) π) = Set.Icc (0 : ℝ) 1 :=
  haversine_bijOn.image_eq

/- ## Part XI: Summary

| Result                                | Status   |
|---------------------------------------|----------|
| `haversine` (def)                     | DEFINED  |
| `haversine_eq_one_sub_cos_div_two`    | PROVED   |
| `two_haversine_eq`                    | PROVED   |
| `cos_eq_one_sub_two_haversine`        | PROVED   |
| `haversine_nonneg`                    | PROVED   |
| `haversine_le_one`                    | PROVED   |
| `haversine_zero`                      | PROVED   |
| `haversine_pi`                        | PROVED   |
| `haversine_neg`                       | PROVED   |
| `haversine_formula_algebraic`         | PROVED   |
| `cos_form_of_haversine_formula`       | PROVED   |
| `haversine_formula_holds_when_sin_sideA_zero` | PROVED |
| `haversine_sub_comm`                  | PROVED   |
| `inner_projectPerp_eq_sin_sin_cos_angleC` | PROVED (S2 bridge) |
| `cos_sideC_trig_form`                 | PROVED (S2) |
| `haversine_formula` (`SphericalTriangle`) | PROVED (S2) |
| `sin_half_nonneg`                     | PROVED (S3) |
| `sqrt_haversine_eq_sin_half`          | PROVED (S3) |
| `eq_two_arcsin_sqrt_haversine`        | PROVED (S3) |
| `sideC_eq_two_arcsin_sqrt_haversine`  | PROVED (S3) |
| `sideA_eq_two_arcsin_sqrt_haversine`  | PROVED (S3) |
| `sideB_eq_two_arcsin_sqrt_haversine`  | PROVED (S3) |
| `sideC_eq_great_circle_haversine`     | PROVED (S3) |
| `haversine_strictMonoOn_Icc_zero_pi`  | PROVED (S4) |
| `haversine_injOn_Icc_zero_pi`         | PROVED (S4) |
| `haversine_lt_haversine_iff_lt`       | PROVED (S4) |
| `haversine_eq_haversine_iff_eq`       | PROVED (S4) |
| `arcLength_eq_of_haversine_eq`        | PROVED (S4) |
| `sideC_eq_of_haversine_sideC_eq`      | PROVED (S4) |
| `sideA_eq_of_haversine_sideA_eq`      | PROVED (S4) |
| `sideB_eq_of_haversine_sideB_eq`      | PROVED (S4) |
| `haversine_eq_zero_iff_of_mem_Icc`    | PROVED (S4) |
| `haversine_two_arcsin_sqrt`           | PROVED (S5) |
| `two_arcsin_sqrt_mem_Icc`             | PROVED (S5) |
| `haversine_mapsTo`                    | PROVED (S5) |
| `haversine_surjOn`                    | PROVED (S5) |
| `haversine_bijOn`                     | PROVED (S5) |
| `haversine_image_Icc`                 | PROVED (S5) |

Axioms: 0
Sorries: 0
Proved theorems: 37
Definitions: 1
-/

end SphericalLawOfCosinesOQ05
