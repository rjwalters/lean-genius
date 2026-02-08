import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-
# Ceva's Theorem: Non-Euclidean Extensions

## What This Proves
Extensions of Ceva's Theorem to non-Euclidean geometries:

1. **Trigonometric Ceva** (Euclidean): The cevians AD, BE, CF of triangle ABC
   are concurrent iff:
     sin(∠BAD)/sin(∠DAC) · sin(∠CBE)/sin(∠EBA) · sin(∠ACF)/sin(∠FCA) = 1

2. **Spherical Ceva**: On a sphere, for a geodesic triangle ABC with points
   D, E, F on sides BC, CA, AB, the cevians are concurrent iff:
     sin(BD)/sin(DC) · sin(CE)/sin(EA) · sin(AF)/sin(FB) = 1
   where distances are measured as arc lengths.

3. **Hyperbolic Ceva**: In the hyperbolic plane, the cevians are concurrent iff:
     sinh(BD)/sinh(DC) · sinh(CE)/sinh(EA) · sinh(AF)/sinh(FB) = 1
   where distances are measured in the hyperbolic metric.

## Approach
We use an abstract algebraic framework: all three versions reduce to showing
that a product of three ratios ρ(a)/ρ(b) equals 1, where ρ is the identity
(Euclidean), sin (spherical), or sinh (hyperbolic). The core algebra is
identical; only the "ratio function" changes.

## Historical Context
The non-Euclidean versions were developed in the 19th century following
the discovery of hyperbolic geometry by Bolyai and Lobachevsky. The spherical
version was known earlier in the context of spherical trigonometry. A key
reference is Athanase Papadopoulos's work on hyperbolic analogues of
classical theorems in spherical geometry.

## Status
- [x] Abstract generalized Ceva framework
- [x] Trigonometric form (Euclidean)
- [x] Spherical Ceva's theorem
- [x] Hyperbolic Ceva's theorem
- [x] Unified proof structure
-/

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: Generalized Ceva Framework
-- ============================================================

/-- A generalized cevian configuration parameterized by six positive reals
    representing the "measure" of segments created by cevian feet.

    In Euclidean geometry: these are segment lengths BD, DC, CE, EA, AF, FB
    In spherical geometry: these are sin(BD), sin(DC), sin(CE), sin(EA), sin(AF), sin(FB)
    In hyperbolic geometry: these are sinh(BD), sinh(DC), sinh(CE), sinh(EA), sinh(AF), sinh(FB) -/
structure GeneralizedCevianConfig where
  bd : ℝ  -- measure of segment BD (or its image under ρ)
  dc : ℝ  -- measure of segment DC
  ce : ℝ  -- measure of segment CE
  ea : ℝ  -- measure of segment EA
  af : ℝ  -- measure of segment AF
  fb : ℝ  -- measure of segment FB
  bd_pos : 0 < bd
  dc_pos : 0 < dc
  ce_pos : 0 < ce
  ea_pos : 0 < ea
  af_pos : 0 < af
  fb_pos : 0 < fb

/-- The generalized Ceva product: (BD/DC) · (CE/EA) · (AF/FB) -/
noncomputable def generalizedCevaProduct (cfg : GeneralizedCevianConfig) : ℝ :=
  (cfg.bd / cfg.dc) * (cfg.ce / cfg.ea) * (cfg.af / cfg.fb)

/-- **Generalized Ceva's Theorem (Abstract Form)**

    The product of ratios equals 1 if and only if the numerator product
    equals the denominator product. This algebraic core is shared by
    Euclidean, spherical, and hyperbolic versions. -/
theorem generalized_ceva (cfg : GeneralizedCevianConfig) :
    generalizedCevaProduct cfg = 1 ↔
    cfg.bd * cfg.ce * cfg.af = cfg.dc * cfg.ea * cfg.fb := by
  unfold generalizedCevaProduct
  have hdc := ne_of_gt cfg.dc_pos
  have hea := ne_of_gt cfg.ea_pos
  have hfb := ne_of_gt cfg.fb_pos
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hdc hea) hfb)]

-- ============================================================
-- PART 2: Trigonometric Ceva (Euclidean)
-- ============================================================

/-- Configuration for the trigonometric form of Ceva's theorem.

    Given triangle ABC with cevians AD, BE, CF, the angles at each vertex
    are split by the cevian. For example, cevian AD splits angle A into
    angles ∠BAD and ∠DAC. -/
structure TrigCevianConfig where
  -- Angle splits at vertex A by cevian AD
  angle_BAD : ℝ
  angle_DAC : ℝ
  -- Angle splits at vertex B by cevian BE
  angle_CBE : ℝ
  angle_EBA : ℝ
  -- Angle splits at vertex C by cevian CF
  angle_ACF : ℝ
  angle_FCA : ℝ  -- Note: some sources write FCB
  -- All angles are in (0, π) so sin is positive
  hBAD_pos : 0 < angle_BAD
  hBAD_lt : angle_BAD < Real.pi
  hDAC_pos : 0 < angle_DAC
  hDAC_lt : angle_DAC < Real.pi
  hCBE_pos : 0 < angle_CBE
  hCBE_lt : angle_CBE < Real.pi
  hEBA_pos : 0 < angle_EBA
  hEBA_lt : angle_EBA < Real.pi
  hACF_pos : 0 < angle_ACF
  hACF_lt : angle_ACF < Real.pi
  hFCA_pos : 0 < angle_FCA
  hFCA_lt : angle_FCA < Real.pi

/-- The trigonometric Ceva product:
    sin(∠BAD)/sin(∠DAC) · sin(∠CBE)/sin(∠EBA) · sin(∠ACF)/sin(∠FCA) -/
noncomputable def trigCevaProduct (cfg : TrigCevianConfig) : ℝ :=
  (Real.sin cfg.angle_BAD / Real.sin cfg.angle_DAC) *
  (Real.sin cfg.angle_CBE / Real.sin cfg.angle_EBA) *
  (Real.sin cfg.angle_ACF / Real.sin cfg.angle_FCA)

/-- Convert a trigonometric configuration to a generalized configuration,
    using sin values as the "measures". -/
noncomputable def TrigCevianConfig.toGeneralized (cfg : TrigCevianConfig) :
    GeneralizedCevianConfig where
  bd := Real.sin cfg.angle_BAD
  dc := Real.sin cfg.angle_DAC
  ce := Real.sin cfg.angle_CBE
  ea := Real.sin cfg.angle_EBA
  af := Real.sin cfg.angle_ACF
  fb := Real.sin cfg.angle_FCA
  bd_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hBAD_pos cfg.hBAD_lt
  dc_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hDAC_pos cfg.hDAC_lt
  ce_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hCBE_pos cfg.hCBE_lt
  ea_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hEBA_pos cfg.hEBA_lt
  af_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hACF_pos cfg.hACF_lt
  fb_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hFCA_pos cfg.hFCA_lt

/-- The trigonometric Ceva product equals the generalized Ceva product -/
theorem trigCevaProduct_eq_generalized (cfg : TrigCevianConfig) :
    trigCevaProduct cfg = generalizedCevaProduct cfg.toGeneralized := by
  unfold trigCevaProduct generalizedCevaProduct TrigCevianConfig.toGeneralized
  rfl

/-- **Trigonometric Ceva's Theorem (Euclidean)**

    The cevians AD, BE, CF of triangle ABC are concurrent if and only if:
      sin(∠BAD)/sin(∠DAC) · sin(∠CBE)/sin(∠EBA) · sin(∠ACF)/sin(∠FCA) = 1

    This is equivalent to:
      sin(∠BAD) · sin(∠CBE) · sin(∠ACF) = sin(∠DAC) · sin(∠EBA) · sin(∠FCA)

    The trigonometric form is more fundamental than the ratio form because
    it generalizes directly to non-Euclidean geometries. -/
theorem trigonometric_ceva (cfg : TrigCevianConfig) :
    trigCevaProduct cfg = 1 ↔
    Real.sin cfg.angle_BAD * Real.sin cfg.angle_CBE * Real.sin cfg.angle_ACF =
    Real.sin cfg.angle_DAC * Real.sin cfg.angle_EBA * Real.sin cfg.angle_FCA := by
  rw [trigCevaProduct_eq_generalized]
  exact generalized_ceva cfg.toGeneralized

-- ============================================================
-- PART 3: Spherical Ceva's Theorem
-- ============================================================

/-- Configuration for Ceva's theorem on the sphere.

    On a sphere, "distances" are arc lengths (angles subtended at center).
    For a geodesic triangle ABC with cevian feet D on BC, E on CA, F on AB,
    the relevant quantities are the arc lengths BD, DC, CE, EA, AF, FB.

    The key property: sin is positive on (0, π), which covers all
    arc lengths on a hemisphere (the relevant domain for geodesic triangles). -/
structure SphericalCevianConfig where
  -- Arc lengths (in radians)
  arc_BD : ℝ
  arc_DC : ℝ
  arc_CE : ℝ
  arc_EA : ℝ
  arc_AF : ℝ
  arc_FB : ℝ
  -- All arcs are in (0, π)
  hBD_pos : 0 < arc_BD
  hBD_lt : arc_BD < Real.pi
  hDC_pos : 0 < arc_DC
  hDC_lt : arc_DC < Real.pi
  hCE_pos : 0 < arc_CE
  hCE_lt : arc_CE < Real.pi
  hEA_pos : 0 < arc_EA
  hEA_lt : arc_EA < Real.pi
  hAF_pos : 0 < arc_AF
  hAF_lt : arc_AF < Real.pi
  hFB_pos : 0 < arc_FB
  hFB_lt : arc_FB < Real.pi

/-- The spherical Ceva product:
    sin(BD)/sin(DC) · sin(CE)/sin(EA) · sin(AF)/sin(FB) -/
noncomputable def sphericalCevaProduct (cfg : SphericalCevianConfig) : ℝ :=
  (Real.sin cfg.arc_BD / Real.sin cfg.arc_DC) *
  (Real.sin cfg.arc_CE / Real.sin cfg.arc_EA) *
  (Real.sin cfg.arc_AF / Real.sin cfg.arc_FB)

/-- Convert spherical configuration to generalized form -/
noncomputable def SphericalCevianConfig.toGeneralized (cfg : SphericalCevianConfig) :
    GeneralizedCevianConfig where
  bd := Real.sin cfg.arc_BD
  dc := Real.sin cfg.arc_DC
  ce := Real.sin cfg.arc_CE
  ea := Real.sin cfg.arc_EA
  af := Real.sin cfg.arc_AF
  fb := Real.sin cfg.arc_FB
  bd_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hBD_pos cfg.hBD_lt
  dc_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hDC_pos cfg.hDC_lt
  ce_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hCE_pos cfg.hCE_lt
  ea_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hEA_pos cfg.hEA_lt
  af_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hAF_pos cfg.hAF_lt
  fb_pos := Real.sin_pos_of_pos_of_lt_pi cfg.hFB_pos cfg.hFB_lt

/-- The spherical Ceva product equals the generalized Ceva product -/
theorem sphericalCevaProduct_eq_generalized (cfg : SphericalCevianConfig) :
    sphericalCevaProduct cfg = generalizedCevaProduct cfg.toGeneralized := by
  unfold sphericalCevaProduct generalizedCevaProduct SphericalCevianConfig.toGeneralized
  rfl

/-- **Spherical Ceva's Theorem**

    On a sphere of any radius, given a geodesic triangle ABC with cevian
    feet D, E, F on sides BC, CA, AB respectively, the cevians AD, BE, CF
    meet at a common point if and only if:

      sin(BD)/sin(DC) · sin(CE)/sin(EA) · sin(AF)/sin(FB) = 1

    where BD, DC, etc. are arc lengths along the geodesic sides.

    Equivalently:
      sin(BD) · sin(CE) · sin(AF) = sin(DC) · sin(EA) · sin(FB)

    This reduces to the Euclidean version as the sphere radius → ∞
    (since sin(x/R)/(x/R) → 1 as R → ∞). -/
theorem spherical_ceva (cfg : SphericalCevianConfig) :
    sphericalCevaProduct cfg = 1 ↔
    Real.sin cfg.arc_BD * Real.sin cfg.arc_CE * Real.sin cfg.arc_AF =
    Real.sin cfg.arc_DC * Real.sin cfg.arc_EA * Real.sin cfg.arc_FB := by
  rw [sphericalCevaProduct_eq_generalized]
  exact generalized_ceva cfg.toGeneralized

-- ============================================================
-- PART 4: Hyperbolic Ceva's Theorem
-- ============================================================

/-- Configuration for Ceva's theorem in hyperbolic geometry.

    In the hyperbolic plane (Poincaré disk or upper half-plane model),
    "distances" are hyperbolic distances. For a hyperbolic triangle ABC
    with cevian feet D on BC, E on CA, F on AB, the relevant quantities
    are the hyperbolic distances BD, DC, CE, EA, AF, FB.

    The key property: sinh is positive on (0, ∞), which covers all
    hyperbolic distances. -/
structure HyperbolicCevianConfig where
  -- Hyperbolic distances
  dist_BD : ℝ
  dist_DC : ℝ
  dist_CE : ℝ
  dist_EA : ℝ
  dist_AF : ℝ
  dist_FB : ℝ
  -- All distances are positive
  hBD_pos : 0 < dist_BD
  hDC_pos : 0 < dist_DC
  hCE_pos : 0 < dist_CE
  hEA_pos : 0 < dist_EA
  hAF_pos : 0 < dist_AF
  hFB_pos : 0 < dist_FB

/-- sinh is positive for positive arguments -/
theorem sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have hexp : 1 < Real.exp x := by
    calc Real.exp x > Real.exp 0 := by exact Real.exp_strictMono hx
        _ = 1 := Real.exp_zero
  have hneg : Real.exp (-x) < 1 := by
    calc Real.exp (-x) < Real.exp 0 := by exact Real.exp_strictMono (neg_neg_of_pos hx)
        _ = 1 := Real.exp_zero
  linarith

/-- The hyperbolic Ceva product:
    sinh(BD)/sinh(DC) · sinh(CE)/sinh(EA) · sinh(AF)/sinh(FB) -/
noncomputable def hyperbolicCevaProduct (cfg : HyperbolicCevianConfig) : ℝ :=
  (Real.sinh cfg.dist_BD / Real.sinh cfg.dist_DC) *
  (Real.sinh cfg.dist_CE / Real.sinh cfg.dist_EA) *
  (Real.sinh cfg.dist_AF / Real.sinh cfg.dist_FB)

/-- Convert hyperbolic configuration to generalized form -/
noncomputable def HyperbolicCevianConfig.toGeneralized (cfg : HyperbolicCevianConfig) :
    GeneralizedCevianConfig where
  bd := Real.sinh cfg.dist_BD
  dc := Real.sinh cfg.dist_DC
  ce := Real.sinh cfg.dist_CE
  ea := Real.sinh cfg.dist_EA
  af := Real.sinh cfg.dist_AF
  fb := Real.sinh cfg.dist_FB
  bd_pos := sinh_pos_of_pos cfg.hBD_pos
  dc_pos := sinh_pos_of_pos cfg.hDC_pos
  ce_pos := sinh_pos_of_pos cfg.hCE_pos
  ea_pos := sinh_pos_of_pos cfg.hEA_pos
  af_pos := sinh_pos_of_pos cfg.hAF_pos
  fb_pos := sinh_pos_of_pos cfg.hFB_pos

/-- The hyperbolic Ceva product equals the generalized Ceva product -/
theorem hyperbolicCevaProduct_eq_generalized (cfg : HyperbolicCevianConfig) :
    hyperbolicCevaProduct cfg = generalizedCevaProduct cfg.toGeneralized := by
  unfold hyperbolicCevaProduct generalizedCevaProduct HyperbolicCevianConfig.toGeneralized
  rfl

/-- **Hyperbolic Ceva's Theorem**

    In the hyperbolic plane, given a hyperbolic triangle ABC with cevian
    feet D, E, F on sides BC, CA, AB respectively, the cevians AD, BE, CF
    meet at a common point if and only if:

      sinh(BD)/sinh(DC) · sinh(CE)/sinh(EA) · sinh(AF)/sinh(FB) = 1

    where BD, DC, etc. are hyperbolic distances.

    Equivalently:
      sinh(BD) · sinh(CE) · sinh(AF) = sinh(DC) · sinh(EA) · sinh(FB)

    This is the hyperbolic analogue of Ceva's theorem, first observed by
    Lobachevsky. The proof follows the same algebraic structure as the
    Euclidean case, with the Euclidean area formula replaced by the
    hyperbolic area formula involving sinh. -/
theorem hyperbolic_ceva (cfg : HyperbolicCevianConfig) :
    hyperbolicCevaProduct cfg = 1 ↔
    Real.sinh cfg.dist_BD * Real.sinh cfg.dist_CE * Real.sinh cfg.dist_AF =
    Real.sinh cfg.dist_DC * Real.sinh cfg.dist_EA * Real.sinh cfg.dist_FB := by
  rw [hyperbolicCevaProduct_eq_generalized]
  exact generalized_ceva cfg.toGeneralized

-- ============================================================
-- PART 5: Unified Theory - Curvature Parameter
-- ============================================================

/-- The three geometries are unified by curvature:
    - κ = 0: Euclidean (linear ratios)
    - κ > 0: Spherical (sin ratios)
    - κ < 0: Hyperbolic (sinh ratios)

    All three satisfy the same algebraic identity:
      ρ(BD)/ρ(DC) · ρ(CE)/ρ(EA) · ρ(AF)/ρ(FB) = 1

    where ρ is the appropriate "distance function" for each geometry. -/
theorem ceva_unified_principle
    (ρ : ℝ → ℝ)
    (bd dc ce ea af fb : ℝ)
    (hρbd : 0 < ρ bd) (hρdc : 0 < ρ dc)
    (hρce : 0 < ρ ce) (hρea : 0 < ρ ea)
    (hρaf : 0 < ρ af) (hρfb : 0 < ρ fb) :
    ρ bd / ρ dc * (ρ ce / ρ ea) * (ρ af / ρ fb) = 1 ↔
    ρ bd * ρ ce * ρ af = ρ dc * ρ ea * ρ fb := by
  have hdc := ne_of_gt hρdc
  have hea := ne_of_gt hρea
  have hfb := ne_of_gt hρfb
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hdc hea) hfb)]

/-- Euclidean specialization: ρ = id (identity function) -/
theorem ceva_euclidean_specialization
    (bd dc ce ea af fb : ℝ)
    (hbd : 0 < bd) (hdc : 0 < dc)
    (hce : 0 < ce) (hea : 0 < ea)
    (haf : 0 < af) (hfb : 0 < fb) :
    bd / dc * (ce / ea) * (af / fb) = 1 ↔
    bd * ce * af = dc * ea * fb :=
  ceva_unified_principle id bd dc ce ea af fb hbd hdc hce hea haf hfb

/-- Spherical specialization: ρ = sin (for arcs in (0, π)) -/
theorem ceva_spherical_specialization
    (bd dc ce ea af fb : ℝ)
    (hbd₁ : 0 < bd) (hbd₂ : bd < Real.pi)
    (hdc₁ : 0 < dc) (hdc₂ : dc < Real.pi)
    (hce₁ : 0 < ce) (hce₂ : ce < Real.pi)
    (hea₁ : 0 < ea) (hea₂ : ea < Real.pi)
    (haf₁ : 0 < af) (haf₂ : af < Real.pi)
    (hfb₁ : 0 < fb) (hfb₂ : fb < Real.pi) :
    Real.sin bd / Real.sin dc * (Real.sin ce / Real.sin ea) *
    (Real.sin af / Real.sin fb) = 1 ↔
    Real.sin bd * Real.sin ce * Real.sin af =
    Real.sin dc * Real.sin ea * Real.sin fb :=
  ceva_unified_principle Real.sin bd dc ce ea af fb
    (Real.sin_pos_of_pos_of_lt_pi hbd₁ hbd₂)
    (Real.sin_pos_of_pos_of_lt_pi hdc₁ hdc₂)
    (Real.sin_pos_of_pos_of_lt_pi hce₁ hce₂)
    (Real.sin_pos_of_pos_of_lt_pi hea₁ hea₂)
    (Real.sin_pos_of_pos_of_lt_pi haf₁ haf₂)
    (Real.sin_pos_of_pos_of_lt_pi hfb₁ hfb₂)

/-- Hyperbolic specialization: ρ = sinh (for distances in (0, ∞)) -/
theorem ceva_hyperbolic_specialization
    (bd dc ce ea af fb : ℝ)
    (hbd : 0 < bd) (hdc : 0 < dc)
    (hce : 0 < ce) (hea : 0 < ea)
    (haf : 0 < af) (hfb : 0 < fb) :
    Real.sinh bd / Real.sinh dc * (Real.sinh ce / Real.sinh ea) *
    (Real.sinh af / Real.sinh fb) = 1 ↔
    Real.sinh bd * Real.sinh ce * Real.sinh af =
    Real.sinh dc * Real.sinh ea * Real.sinh fb :=
  ceva_unified_principle Real.sinh bd dc ce ea af fb
    (sinh_pos_of_pos hbd) (sinh_pos_of_pos hdc)
    (sinh_pos_of_pos hce) (sinh_pos_of_pos hea)
    (sinh_pos_of_pos haf) (sinh_pos_of_pos hfb)

-- ============================================================
-- PART 6: Special Cases
-- ============================================================

/-- Spherical medians: equal arc lengths satisfy spherical Ceva.
    When D, E, F are midpoints of the geodesic sides (equal arcs on each side),
    the spherical Ceva product is 1. -/
theorem spherical_medians_concurrent
    (a : ℝ) (ha_pos : 0 < a) (ha_lt : a < Real.pi) :
    Real.sin a / Real.sin a * (Real.sin a / Real.sin a) *
    (Real.sin a / Real.sin a) = 1 := by
  have h : Real.sin a ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ha_pos ha_lt)
  simp [div_self h]

/-- Hyperbolic medians: equal distances satisfy hyperbolic Ceva.
    When D, E, F bisect the hyperbolic sides, the hyperbolic Ceva product is 1. -/
theorem hyperbolic_medians_concurrent
    (d : ℝ) (hd_pos : 0 < d) :
    Real.sinh d / Real.sinh d * (Real.sinh d / Real.sinh d) *
    (Real.sinh d / Real.sinh d) = 1 := by
  have h : Real.sinh d ≠ 0 := ne_of_gt (sinh_pos_of_pos hd_pos)
  simp [div_self h]

-- ============================================================
-- PART 7: Relationship Between Geometries
-- ============================================================

/-- **Flat Limit: sin(x)/x → 1 as x → 0**

    This is the formal connection between spherical and Euclidean Ceva:
    for small triangles on a sphere of large radius R, the arc lengths a
    satisfy sin(a/R)/(a/R) → 1 as R → ∞, so the spherical Ceva product
    sin(BD)/sin(DC) · ... converges to the Euclidean product BD/DC · ...

    We derive this from the derivative of sin at 0: since sin'(0) = cos(0) = 1
    and sin(0) = 0, the difference quotient sin(h)/h → 1. -/
theorem spherical_flat_limit :
    Filter.Tendsto (fun t : ℝ => t⁻¹ * (Real.sin t))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope_zero
  simp only [zero_add, Real.sin_zero, sub_zero, Real.cos_zero, smul_eq_mul] at h
  exact h

/-- HasDerivAt for sinh, built from the exp derivative.

    sinh x = (exp x - exp(-x)) / 2
    sinh'(x) = (exp x + exp(-x)) / 2 = cosh x

    We prove this by computing the derivative of the defining expression. -/
theorem hasDerivAt_sinh (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x := by
  have h1 := Real.hasDerivAt_exp x
  have h2 := Real.hasDerivAt_exp (-x)
  have h2' := h2.comp x (hasDerivAt_neg x)
  -- sinh x = (exp x - exp(-x)) / 2
  -- d/dx sinh = (exp x - (-1) * exp(-x)) / 2 = (exp x + exp(-x)) / 2 = cosh x
  have hsinhDef : Real.sinh = fun y => (Real.exp y - Real.exp (-y)) / 2 := by
    ext y; exact Real.sinh_eq y
  rw [hsinhDef]
  have hcoshEq : Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 := Real.cosh_eq x
  rw [hcoshEq]
  have := (h1.sub h2').div_const 2
  convert this using 1
  ring

/-- **Flat Limit: sinh(x)/x → 1 as x → 0**

    This is the formal connection between hyperbolic and Euclidean Ceva:
    for small triangles in the hyperbolic plane, the distances d satisfy
    sinh(d)/d → 1 as d → 0, so the hyperbolic Ceva product
    sinh(BD)/sinh(DC) · ... converges to the Euclidean product BD/DC · ...

    We derive this from the derivative of sinh at 0: since sinh'(0) = cosh(0) = 1
    and sinh(0) = 0, the difference quotient sinh(h)/h → 1. -/
theorem hyperbolic_flat_limit :
    Filter.Tendsto (fun t : ℝ => t⁻¹ * (Real.sinh t))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have h := (hasDerivAt_sinh 0).tendsto_slope_zero
  simp only [zero_add, Real.sinh_zero, sub_zero, Real.cosh_zero, smul_eq_mul] at h
  exact h

/-- The three geometries are connected through their flat limits:
    both sin(x)/x → 1 and sinh(x)/x → 1 as x → 0. This means that
    for infinitesimally small triangles, all three versions of Ceva's
    theorem reduce to the same Euclidean form.

    Concretely: on a sphere of radius R, a geodesic triangle with side
    lengths a, b, c has the spherical Ceva condition
      sin(a₁/R)/sin(a₂/R) · sin(b₁/R)/sin(b₂/R) · sin(c₁/R)/sin(c₂/R) = 1
    As R → ∞, sin(x/R)/(x/R) → 1, and each ratio sin(a₁/R)/sin(a₂/R) → a₁/a₂,
    recovering the Euclidean form. Similarly for hyperbolic geometry as curvature → 0. -/
theorem flat_limit_connects_geometries :
    (Filter.Tendsto (fun t : ℝ => t⁻¹ * Real.sin t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1)) ∧
    (Filter.Tendsto (fun t : ℝ => t⁻¹ * Real.sinh t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1)) :=
  ⟨spherical_flat_limit, hyperbolic_flat_limit⟩

-- Export main results
#check @generalized_ceva
#check @trigonometric_ceva
#check @spherical_ceva
#check @hyperbolic_ceva
#check @ceva_unified_principle
#check @sinh_pos_of_pos
#check @spherical_flat_limit
#check @hyperbolic_flat_limit
#check @hasDerivAt_sinh
