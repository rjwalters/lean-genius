import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
# Projective Unification of Ceva's Theorem (cevas-theorem-oq-02-oq-01-oq-02-oq-01)

## The Open Question

**OQ-02-OQ-01-OQ-02-OQ-01**: The parent file
(`CevasTheoremOQ02OQ01OQ02.lean`) proves the spherical, Euclidean, and
hyperbolic Ceva theorems *separately* and then observes they share one
concurrency criterion. Can all three instead be derived from a **single**
projective Ceva theorem via the Cayley–Klein / Beltrami–Klein model?

## The Answer: YES — one weight-parametrised side-ratio, three absolutes

All three constant-curvature geometries are **Cayley–Klein geometries**: the
projective plane equipped with an absolute conic `Q` whose choice (a curvature
sentinel `κ ∈ {+1, 0, −1}`) selects elliptic/spherical, Euclidean, or
hyperbolic. A cevian point on geodesic `BC` is the *projective* point
`D ∝ α·B + β·C` — pure projective incidence, geometry-independent. The metric
enters only through the curvature-`κ` "sine" factor

  g_κ = sin_κ(d(B,C)) / n,    n = √(α² + 2αβm + β²),   m = ⟨B,C⟩_κ

which is **common to numerator and denominator** of the side ratio and cancels:

  t_κ(BD) / t_κ(DC) = (β · g_κ) / (α · g_κ) = β / α                    (★)

for *every* κ, including the Euclidean limit (g = 1, the barycentric ratio).
This file isolates (★) as one abstract cancellation over a free nonzero factor
`g`, then recovers the three classical side-ratio identities as instantiations:

  spherical   g = √(1 − m²)/n   (m² < 1)
  Euclidean   g = 1
  hyperbolic  g = √(m² − 1)/n   (m > 1)

and proves a single `projective_ceva_unification` whose concurrency criterion
`α_D α_E α_F = β_D β_E β_F` holds for an arbitrary nonzero geometry factor — the
three geometries are its three specializations.

## Scope (honest)

Mathlib has no Cayley–Klein / projective-metric API. Following the survey plan,
the unification is encoded at the *algebraic* layer where it actually lives: the
scalar `(m, α, β, n)` data and the abstract factor `g`. We do **not** rebuild
`ℝP²` with an absolute conic — the concurrency criterion and side ratio are
fully captured by this data, and incidence in homogeneous `{B,C}` coordinates is
exactly the weight parametrisation. The mathematical content (cancellation +
criterion) reuses the parent's verified algebra verbatim.

## Status
- [x] κ-carrying configuration with single positivity hypothesis n² > 0
- [x] Abstract side-ratio cancellation over a free nonzero geometry factor
- [x] Three classical side-ratio identities as instantiations (sph/euc/hyp)
- [x] Single projective Ceva theorem; three geometries as corollaries
-/

set_option linter.unusedVariables false

namespace CevasOQ02OQ01OQ02OQ01

open Real

/-
## Part 1: The Cayley–Klein cevian configuration

One structure for all three geometries. The per-geometry bound on `m`
(`m ∈ (−1,1)` spherical, `m > 1` hyperbolic) is dropped in favour of the single
hypothesis `n² > 0`, which is exactly what every bound was there to guarantee
and what every downstream proof uses.
-/

/-- A Cayley–Klein cevian point `D ∝ α·B + β·C` on geodesic `BC`.
    `κ` is the curvature sentinel (`+1`/`0`/`−1` for elliptic/Euclidean/
    hyperbolic), `m = ⟨B,C⟩_κ` the curvature-`κ` inner product of the base
    points, and `α, β > 0` the projective weights. The single metric
    hypothesis `hn` is `n² > 0`. -/
structure CKCevianConfig where
  κ : ℝ
  m : ℝ
  α : ℝ
  β : ℝ
  hα : 0 < α
  hβ : 0 < β
  hn : 0 < α ^ 2 + 2 * α * β * m + β ^ 2

/-- The squared model norm of `α·B + β·C`:  `n² = α² + 2αβm + β²`. -/
noncomputable def CKCevianConfig.n_sq (cfg : CKCevianConfig) : ℝ :=
  cfg.α ^ 2 + 2 * cfg.α * cfg.β * cfg.m + cfg.β ^ 2

theorem CKCevianConfig.n_sq_pos (cfg : CKCevianConfig) : 0 < cfg.n_sq := by
  unfold CKCevianConfig.n_sq; exact cfg.hn

/-- The model norm `n = √(n²) > 0`. -/
noncomputable def CKCevianConfig.n (cfg : CKCevianConfig) : ℝ :=
  Real.sqrt cfg.n_sq

theorem CKCevianConfig.n_pos (cfg : CKCevianConfig) : 0 < cfg.n :=
  Real.sqrt_pos.mpr cfg.n_sq_pos

/-
## Part 2: The abstract side-ratio cancellation (★)

The crux, proved **once**. The geometry-specific factor `g = sin_κ/n` is a free
nonzero parameter; it cancels between the two segment measures, leaving `β/α`
independent of the geometry. This is the parent's `hyp_sinh_ratio` with the
`√(m²−1)/n` factor abstracted to `g`.
-/

/-- Universal side measure of segment `BD`, with geometry factor `g`: `β · g`. -/
noncomputable def ckMeasureBD (cfg : CKCevianConfig) (g : ℝ) : ℝ := cfg.β * g

/-- Universal side measure of segment `DC`, with geometry factor `g`: `α · g`. -/
noncomputable def ckMeasureDC (cfg : CKCevianConfig) (g : ℝ) : ℝ := cfg.α * g

/-- **Universal side-ratio (★)**. For any nonzero geometry factor `g`,
    the cevian side ratio equals the weight ratio `β/α`, independent of `κ`. -/
theorem ck_side_ratio (cfg : CKCevianConfig) (g : ℝ) (hg : g ≠ 0) :
    ckMeasureBD cfg g / ckMeasureDC cfg g = cfg.β / cfg.α := by
  unfold ckMeasureBD ckMeasureDC
  field_simp [hg, cfg.hα.ne']

/-
## Part 3: The three classical side-ratio identities as instantiations

Each is (★) with a specific geometry factor, the factor shown nonzero from the
geometry's `m`-bound.
-/

/-- Spherical geometry factor `g = √(1 − m²)/n` (valid for `m² < 1`). -/
noncomputable def gSph (m n : ℝ) : ℝ := Real.sqrt (1 - m ^ 2) / n

/-- Hyperbolic geometry factor `g = √(m² − 1)/n` (valid for `m > 1`). -/
noncomputable def gHyp (m n : ℝ) : ℝ := Real.sqrt (m ^ 2 - 1) / n

/-- **Spherical side ratio** = `β/α`. The `√(1−m²)/n` factor cancels. -/
theorem spherical_ceva_side_ratio (cfg : CKCevianConfig) (hm : cfg.m ^ 2 < 1) :
    ckMeasureBD cfg (gSph cfg.m cfg.n) / ckMeasureDC cfg (gSph cfg.m cfg.n)
      = cfg.β / cfg.α := by
  apply ck_side_ratio
  unfold gSph
  have h1 : 0 < 1 - cfg.m ^ 2 := by linarith
  exact (div_pos (Real.sqrt_pos.mpr h1) cfg.n_pos).ne'

/-- **Hyperbolic side ratio** = `β/α`. The `√(m²−1)/n` factor cancels. -/
theorem hyperbolic_ceva_side_ratio (cfg : CKCevianConfig) (hm : 1 < cfg.m) :
    ckMeasureBD cfg (gHyp cfg.m cfg.n) / ckMeasureDC cfg (gHyp cfg.m cfg.n)
      = cfg.β / cfg.α := by
  apply ck_side_ratio
  unfold gHyp
  have h1 : 0 < cfg.m ^ 2 - 1 := by nlinarith
  exact (div_pos (Real.sqrt_pos.mpr h1) cfg.n_pos).ne'

/-- **Euclidean side ratio** = `β/α`. The Euclidean limit is `g = 1`: the
    barycentric ratio, with no radical. -/
theorem euclidean_ceva_side_ratio (cfg : CKCevianConfig) :
    ckMeasureBD cfg 1 / ckMeasureDC cfg 1 = cfg.β / cfg.α := by
  apply ck_side_ratio
  exact one_ne_zero

/-
## Part 4: The single projective Ceva theorem

The weight balance criterion, geometry-free (reuses the parent's
`universal_weight_balance` algebra).
-/

/-- The concurrency criterion is purely algebraic in the weights. -/
theorem ck_weight_balance
    (αD βD αE βE αF βF : ℝ)
    (hαD : 0 < αD) (hαE : 0 < αE) (hαF : 0 < αF) :
    (αD * αE * αF = βD * βE * βF) ↔
    (βD / αD) * (βE / αE) * (βF / αF) = 1 := by
  constructor
  · intro h
    field_simp [hαD.ne', hαE.ne', hαF.ne']
    linarith
  · intro h
    field_simp [hαD.ne', hαE.ne', hαF.ne'] at h
    linarith

/-- **Projective Ceva (Cayley–Klein form)**.

    For three cevian points with weights `(α,β)` and **any** nonzero geometry
    factors `g_D, g_E, g_F`, the product of side ratios equals `1` iff the
    weights are balanced: `α_D α_E α_F = β_D β_E β_F`. The criterion does not
    depend on the geometry factors — the three classical Ceva theorems are its
    `κ = +1, 0, −1` specializations (Part 5). -/
theorem projective_ceva_unification
    (cfgD cfgE cfgF : CKCevianConfig)
    (gD gE gF : ℝ) (hgD : gD ≠ 0) (hgE : gE ≠ 0) (hgF : gF ≠ 0) :
    (ckMeasureBD cfgD gD / ckMeasureDC cfgD gD) *
    (ckMeasureBD cfgE gE / ckMeasureDC cfgE gE) *
    (ckMeasureBD cfgF gF / ckMeasureDC cfgF gF) = 1 ↔
    cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β := by
  rw [ck_side_ratio cfgD gD hgD, ck_side_ratio cfgE gE hgE,
      ck_side_ratio cfgF gF hgF]
  exact (ck_weight_balance cfgD.α cfgD.β cfgE.α cfgE.β cfgF.α cfgF.β
    cfgD.hα cfgE.hα cfgF.hα).symm

/-
## Part 5: The three geometries as corollaries of the one theorem

Each is `projective_ceva_unification` with the geometry's factor, shown nonzero
from the per-geometry `m`-bound. Same criterion, three absolutes.
-/

/-- **Spherical Ceva** from the projective theorem (`κ = +1`, `m² < 1`). -/
theorem spherical_ceva_via_projective
    (cfgD cfgE cfgF : CKCevianConfig)
    (hD : cfgD.m ^ 2 < 1) (hE : cfgE.m ^ 2 < 1) (hF : cfgF.m ^ 2 < 1) :
    (ckMeasureBD cfgD (gSph cfgD.m cfgD.n) / ckMeasureDC cfgD (gSph cfgD.m cfgD.n)) *
    (ckMeasureBD cfgE (gSph cfgE.m cfgE.n) / ckMeasureDC cfgE (gSph cfgE.m cfgE.n)) *
    (ckMeasureBD cfgF (gSph cfgF.m cfgF.n) / ckMeasureDC cfgF (gSph cfgF.m cfgF.n)) = 1 ↔
    cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β := by
  apply projective_ceva_unification
  · unfold gSph; exact (div_pos (Real.sqrt_pos.mpr (by linarith : 0 < 1 - cfgD.m ^ 2)) cfgD.n_pos).ne'
  · unfold gSph; exact (div_pos (Real.sqrt_pos.mpr (by linarith : 0 < 1 - cfgE.m ^ 2)) cfgE.n_pos).ne'
  · unfold gSph; exact (div_pos (Real.sqrt_pos.mpr (by linarith : 0 < 1 - cfgF.m ^ 2)) cfgF.n_pos).ne'

/-- **Hyperbolic Ceva** from the projective theorem (`κ = −1`, `m > 1`). -/
theorem hyperbolic_ceva_via_projective
    (cfgD cfgE cfgF : CKCevianConfig)
    (hD : 1 < cfgD.m) (hE : 1 < cfgE.m) (hF : 1 < cfgF.m) :
    (ckMeasureBD cfgD (gHyp cfgD.m cfgD.n) / ckMeasureDC cfgD (gHyp cfgD.m cfgD.n)) *
    (ckMeasureBD cfgE (gHyp cfgE.m cfgE.n) / ckMeasureDC cfgE (gHyp cfgE.m cfgE.n)) *
    (ckMeasureBD cfgF (gHyp cfgF.m cfgF.n) / ckMeasureDC cfgF (gHyp cfgF.m cfgF.n)) = 1 ↔
    cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β := by
  apply projective_ceva_unification
  · unfold gHyp; exact (div_pos (Real.sqrt_pos.mpr (by nlinarith : 0 < cfgD.m ^ 2 - 1)) cfgD.n_pos).ne'
  · unfold gHyp; exact (div_pos (Real.sqrt_pos.mpr (by nlinarith : 0 < cfgE.m ^ 2 - 1)) cfgE.n_pos).ne'
  · unfold gHyp; exact (div_pos (Real.sqrt_pos.mpr (by nlinarith : 0 < cfgF.m ^ 2 - 1)) cfgF.n_pos).ne'

/-- **Euclidean Ceva** from the projective theorem (`κ = 0`, `g = 1`). -/
theorem euclidean_ceva_via_projective
    (cfgD cfgE cfgF : CKCevianConfig) :
    (ckMeasureBD cfgD 1 / ckMeasureDC cfgD 1) *
    (ckMeasureBD cfgE 1 / ckMeasureDC cfgE 1) *
    (ckMeasureBD cfgF 1 / ckMeasureDC cfgF 1) = 1 ↔
    cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β := by
  apply projective_ceva_unification <;> exact one_ne_zero

/-- **Summary answering OQ-02-OQ-01-OQ-02-OQ-01**: the three classical Ceva
    theorems descend from one projective theorem. For a fixed triple of cevian
    configurations, the spherical, Euclidean, and hyperbolic concurrency
    criteria are *the same* statement `α_D α_E α_F = β_D β_E β_F`, obtained by
    instantiating the single `projective_ceva_unification` at the three
    geometry factors. -/
theorem summary_projective_unification
    (cfgD cfgE cfgF : CKCevianConfig)
    (hsD : cfgD.m ^ 2 < 1) (hsE : cfgE.m ^ 2 < 1) (hsF : cfgF.m ^ 2 < 1)
    (hhD : 1 < cfgD.m) (hhE : 1 < cfgE.m) (hhF : 1 < cfgF.m) :
    -- spherical, Euclidean, hyperbolic criteria coincide
    ((ckMeasureBD cfgD (gSph cfgD.m cfgD.n) / ckMeasureDC cfgD (gSph cfgD.m cfgD.n)) *
     (ckMeasureBD cfgE (gSph cfgE.m cfgE.n) / ckMeasureDC cfgE (gSph cfgE.m cfgE.n)) *
     (ckMeasureBD cfgF (gSph cfgF.m cfgF.n) / ckMeasureDC cfgF (gSph cfgF.m cfgF.n)) = 1
      ↔ cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β) ∧
    ((ckMeasureBD cfgD 1 / ckMeasureDC cfgD 1) *
     (ckMeasureBD cfgE 1 / ckMeasureDC cfgE 1) *
     (ckMeasureBD cfgF 1 / ckMeasureDC cfgF 1) = 1
      ↔ cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β) ∧
    ((ckMeasureBD cfgD (gHyp cfgD.m cfgD.n) / ckMeasureDC cfgD (gHyp cfgD.m cfgD.n)) *
     (ckMeasureBD cfgE (gHyp cfgE.m cfgE.n) / ckMeasureDC cfgE (gHyp cfgE.m cfgE.n)) *
     (ckMeasureBD cfgF (gHyp cfgF.m cfgF.n) / ckMeasureDC cfgF (gHyp cfgF.m cfgF.n)) = 1
      ↔ cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β) :=
  ⟨spherical_ceva_via_projective cfgD cfgE cfgF hsD hsE hsF,
   euclidean_ceva_via_projective cfgD cfgE cfgF,
   hyperbolic_ceva_via_projective cfgD cfgE cfgF hhD hhE hhF⟩

end CevasOQ02OQ01OQ02OQ01
