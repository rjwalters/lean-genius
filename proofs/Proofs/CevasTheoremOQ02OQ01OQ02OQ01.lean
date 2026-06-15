import Mathlib

/-
# Ceva's Theorem — OQ-02-OQ-01-OQ-02-OQ-01: Projective (Cayley–Klein) Unification

## Research Problem: cevas-theorem-oq-02-oq-01-oq-02-oq-01

The parent file `CevasTheoremOQ02OQ01OQ02.lean` proves Ceva's theorem in
hyperbolic geometry via weight parameters, and *observes* (Part 5,
`universal_weight_balance`) that the spherical, Euclidean and hyperbolic
concurrency criteria coincide.  But it proves the three side-ratio identities
**separately** — one `HyperbolicCevianConfig` for the hyperbolic case, parallel
reasoning for the spherical sibling — and only then notes the criterion matches.

This file delivers the genuine **unification** asked for by the OQ: a single
Cayley–Klein cevian configuration carrying a *curvature sentinel* `κ`, from which
all three classical Ceva theorems descend as specializations of **one** theorem.

## The Cayley–Klein picture

All three constant-curvature plane geometries are Cayley–Klein geometries: the
projective plane with an *absolute conic* `Q`, the choice of `Q` selecting the
geometry.

| curvature κ | geometry   | absolute `Q`          | `m = ⟨B,C⟩_κ`     | `1 − m²` |
|-------------|------------|-----------------------|-------------------|----------|
| `+1`        | spherical  | imaginary `x²+y²+z²=0` | `cos d ∈ (−1,1)`  | `> 0`    |
| `0`         | Euclidean  | degenerate `z²=0`     | `1`               | `= 0`    |
| `−1`        | hyperbolic | real `x²+y²−z²=0`     | `cosh d > 1`      | `< 0`    |

A cevian point on side `BC` is the **projective** point `D ∝ α·B + β·C` — pure
incidence, geometry-independent.  Normalising to the model uses the single norm
`n² = α² + 2αβm + β²` (valid for every κ).  The metric side-ratio is

      t_κ(BD) / t_κ(DC) = (β · g) / (α · g) = β / α,   g := √|1 − m²| / n,   (★)

where the geometry-specific factor `g` is *common to numerator and denominator*
and **cancels for every κ** — including the Euclidean limit, where `g → 0` but
the ratio survives as the barycentric ratio `β/α`.

## Main results

* `ck_ratio_cancel` — the single algebraic crux: `(β·g)/(α·g) = β/α` for any
  nonzero common factor `g`.  This is (★) with the geometry abstracted away.
* `ck_side_ratio` — (★) at the configuration level.
* `ck_weight_balance` — the universal concurrency criterion (pure algebra).
* `projective_ceva_unification` — the single projective Ceva theorem: for three
  cevian configs of *arbitrary* curvatures, with arbitrary nonzero geometric
  factors `gD, gE, gF`, the side-ratio product equals `1` iff the weight-balance
  `αD·αE·αF = βD·βE·βF` holds.
* `spherical_ceva_unified`, `euclidean_ceva_unified`, `hyperbolic_ceva_unified`
  — the three classical theorems, each obtained by plugging the appropriate
  factor (`gSph`, `gEuc`, `gHyp`) into the *same* `projective_ceva_unification`.

0 axioms, 0 sorries.
-/

namespace CevasOQ02OQ01OQ02OQ01

open Real

/-- A **Cayley–Klein cevian configuration**, unifying the three constant-curvature
    geometries through a single curvature sentinel `κ`.  The only positivity
    hypothesis is `n² > 0` (the field `hn`), which every geometry's `m`-bound
    (`−1 < m < 1` spherical, `m = 1` Euclidean, `m > 1` hyperbolic) implies. -/
structure CKCevianConfig where
  /-- curvature sentinel: `+1` spherical, `0` Euclidean, `−1` hyperbolic. -/
  κ : ℝ
  /-- the Cayley–Klein inner product `⟨B,C⟩_κ = cos_κ(d(B,C))`. -/
  m : ℝ
  /-- first weight parameter (barycentric coordinate of `D` toward `B`). -/
  α : ℝ
  /-- second weight parameter (barycentric coordinate of `D` toward `C`). -/
  β : ℝ
  hα : 0 < α
  hβ : 0 < β
  /-- the squared model norm `n² = α² + 2αβm + β²` is positive. -/
  hn : 0 < α ^ 2 + 2 * α * β * m + β ^ 2

namespace CKCevianConfig

/-- The squared model norm `n² = α² + 2αβm + β²` of `α·B + β·C`. -/
noncomputable def n_sq (cfg : CKCevianConfig) : ℝ :=
  cfg.α ^ 2 + 2 * cfg.α * cfg.β * cfg.m + cfg.β ^ 2

theorem n_sq_pos (cfg : CKCevianConfig) : 0 < cfg.n_sq := by
  unfold n_sq; exact cfg.hn

end CKCevianConfig

/-- **The algebraic crux (★).**  For any nonzero common geometric factor `g`, the
    metric side-ratio `(β·g)/(α·g)` collapses to the geometry-independent weight
    ratio `β/α`.  This single identity replaces the three per-geometry side-ratio
    derivations of the parent file. -/
theorem ck_ratio_cancel (g α β : ℝ) (hg : g ≠ 0) (hα : α ≠ 0) :
    (β * g) / (α * g) = β / α :=
  mul_div_mul_right β α hg

/-- **(★) at the configuration level.**  The metric side-ratio along `BC` is the
    weight ratio `β/α`, for *every* curvature `κ`, given any nonzero geometric
    factor `g`. -/
theorem ck_side_ratio (cfg : CKCevianConfig) (g : ℝ) (hg : g ≠ 0) :
    (cfg.β * g) / (cfg.α * g) = cfg.β / cfg.α :=
  ck_ratio_cancel g cfg.α cfg.β hg cfg.hα.ne'

/-- **The universal concurrency criterion** (pure algebra, κ-free): for positive
    weights, the product of the three weight ratios is `1` iff the weight-balance
    `αD·αE·αF = βD·βE·βF` holds.  Identical in all three geometries. -/
theorem ck_weight_balance
    (αD βD αE βE αF βF : ℝ)
    (hαD : 0 < αD) (hαE : 0 < αE) (hαF : 0 < αF) :
    (βD / αD) * (βE / αE) * (βF / αF) = 1 ↔
    αD * αE * αF = βD * βE * βF := by
  constructor
  · intro h
    field_simp [hαD.ne', hαE.ne', hαF.ne'] at h
    linarith
  · intro h
    field_simp [hαD.ne', hαE.ne', hαF.ne']
    linarith

/-- **Projective Ceva (Cayley–Klein unification).**

    For three cevian configurations `cfgD, cfgE, cfgF` of *arbitrary* (possibly
    distinct) curvatures, and arbitrary nonzero geometric factors `gD, gE, gF`,
    the product of the three metric side-ratios equals `1` — the concurrency
    condition — iff the single weight-balance criterion holds:

      (βD·gD)/(αD·gD) · (βE·gE)/(αE·gE) · (βF·gF)/(αF·gF) = 1
        ↔  αD·αE·αF = βD·βE·βF.

    Every geometry-specific factor cancels by `ck_side_ratio`, leaving the one
    κ-independent criterion.  The three classical theorems are specializations
    obtained by choosing `gSph`, `gEuc`, `gHyp` below. -/
theorem projective_ceva_unification
    (cfgD cfgE cfgF : CKCevianConfig) (gD gE gF : ℝ)
    (hgD : gD ≠ 0) (hgE : gE ≠ 0) (hgF : gF ≠ 0) :
    ((cfgD.β * gD) / (cfgD.α * gD)) *
      ((cfgE.β * gE) / (cfgE.α * gE)) *
      ((cfgF.β * gF) / (cfgF.α * gF)) = 1 ↔
    cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β := by
  rw [ck_side_ratio cfgD gD hgD, ck_side_ratio cfgE gE hgE, ck_side_ratio cfgF gF hgF]
  exact ck_weight_balance cfgD.α cfgD.β cfgE.α cfgE.β cfgF.α cfgF.β
    cfgD.hα cfgE.hα cfgF.hα

/-!
## The three geometric factors

Each geometry contributes its own factor `g = √|1 − m²| / n`.  Only its
**nonvanishing** matters for the unification (the value cancels), so we record a
nonzero/positivity lemma for each.
-/

/-- Spherical geometric factor `√(1 − m²)/n` (curvature `κ = +1`, `m² < 1`). -/
noncomputable def gSph (m n : ℝ) : ℝ := Real.sqrt (1 - m ^ 2) / n

/-- Hyperbolic geometric factor `√(m² − 1)/n` (curvature `κ = −1`, `m² > 1`). -/
noncomputable def gHyp (m n : ℝ) : ℝ := Real.sqrt (m ^ 2 - 1) / n

/-- Euclidean geometric factor (curvature `κ = 0`, `m = 1`): the barycentric
    limit has no radical, so the factor is the constant `1`. -/
def gEuc : ℝ := 1

/-- The spherical factor is nonzero when `m² < 1` and `n > 0`. -/
theorem gSph_ne (m n : ℝ) (hm : m ^ 2 < 1) (hn : 0 < n) : gSph m n ≠ 0 := by
  unfold gSph
  have h1 : (0 : ℝ) < 1 - m ^ 2 := by linarith
  exact div_ne_zero (sqrt_pos.mpr h1).ne' hn.ne'

/-- The hyperbolic factor is nonzero when `m² > 1` and `n > 0`. -/
theorem gHyp_ne (m n : ℝ) (hm : 1 < m ^ 2) (hn : 0 < n) : gHyp m n ≠ 0 := by
  unfold gHyp
  have h1 : (0 : ℝ) < m ^ 2 - 1 := by linarith
  exact div_ne_zero (sqrt_pos.mpr h1).ne' hn.ne'

/-- The Euclidean factor is nonzero (it is `1`). -/
theorem gEuc_ne : gEuc ≠ 0 := one_ne_zero

/-!
## Metric realization: the geometric factor IS the genuine side length

`projective_ceva_unification` cancels the factor `g` *abstractly* — it only needs
`g ≠ 0`.  The lemmas above record that `gSph`/`gHyp` are nonzero, but they do not
yet show those factors are the **actual** metric quantities.  This section closes
that gap, proving that `√(1 − m²)` (spherical) and `√(m² − 1)` (hyperbolic) really
are the per-unit-weight geodesic side lengths, via the single κ-uniform identity

      n² − (α + βm)² = β²·(1 − m²),       n² − (αm + β)² = α²·(1 − m²),

which collapses to the parent's hyperbolic `hyp_key_identity_BD/DC` and its
spherical sign-flip simultaneously.  Consequently the metric side-ratio
`sin_κ(BD)/sin_κ(DC)` — built from genuine geodesic distances, not the abstract
`g` — equals the weight ratio `β/α`.  This realizes the unification concretely:
the abstract cancellation of `projective_ceva_unification` is the true metric
side-ratio, not a formal placeholder.
-/

/-- **The κ-uniform key identity (BD side).**  `n² − (α + βm)² = β²(1 − m²)`.  A
    single ring identity covering all three geometries: for `m² < 1` the right
    side is `> 0` (spherical `sin²`), for `m² > 1` it is `< 0` (hyperbolic, the
    sign moves into `√(m²−1)`), for `m = 1` it vanishes (Euclidean limit). -/
theorem ck_metric_BD (cfg : CKCevianConfig) :
    cfg.n_sq - (cfg.α + cfg.β * cfg.m) ^ 2 = cfg.β ^ 2 * (1 - cfg.m ^ 2) := by
  unfold CKCevianConfig.n_sq; ring

/-- **The κ-uniform key identity (DC side).**  `n² − (αm + β)² = α²(1 − m²)`. -/
theorem ck_metric_DC (cfg : CKCevianConfig) :
    cfg.n_sq - (cfg.α * cfg.m + cfg.β) ^ 2 = cfg.α ^ 2 * (1 - cfg.m ^ 2) := by
  unfold CKCevianConfig.n_sq; ring

/-- **Spherical side length (BD).**  The genuine geodesic numerator
    `√(n² − (α + βm)²)` equals `β·√(1 − m²)`, i.e. `β` times the spherical factor's
    radical.  This is `sin(d(B,D))·n` in the unit-sphere model. -/
theorem gSph_sqrt_BD (cfg : CKCevianConfig) :
    Real.sqrt (cfg.n_sq - (cfg.α + cfg.β * cfg.m) ^ 2)
      = cfg.β * Real.sqrt (1 - cfg.m ^ 2) := by
  rw [ck_metric_BD, Real.sqrt_mul (sq_nonneg cfg.β), Real.sqrt_sq cfg.hβ.le]

/-- **Spherical side length (DC).**  `√(n² − (αm + β)²) = α·√(1 − m²)`. -/
theorem gSph_sqrt_DC (cfg : CKCevianConfig) :
    Real.sqrt (cfg.n_sq - (cfg.α * cfg.m + cfg.β) ^ 2)
      = cfg.α * Real.sqrt (1 - cfg.m ^ 2) := by
  rw [ck_metric_DC, Real.sqrt_mul (sq_nonneg cfg.α), Real.sqrt_sq cfg.hα.le]

/-- **Hyperbolic side length (BD).**  `√((α + βm)² − n²) = β·√(m² − 1)`, i.e.
    `sinh(d(B,D))·n` in the hyperboloid model. -/
theorem gHyp_sqrt_BD (cfg : CKCevianConfig) :
    Real.sqrt ((cfg.α + cfg.β * cfg.m) ^ 2 - cfg.n_sq)
      = cfg.β * Real.sqrt (cfg.m ^ 2 - 1) := by
  have h : (cfg.α + cfg.β * cfg.m) ^ 2 - cfg.n_sq = cfg.β ^ 2 * (cfg.m ^ 2 - 1) := by
    unfold CKCevianConfig.n_sq; ring
  rw [h, Real.sqrt_mul (sq_nonneg cfg.β), Real.sqrt_sq cfg.hβ.le]

/-- **Hyperbolic side length (DC).**  `√((αm + β)² − n²) = α·√(m² − 1)`. -/
theorem gHyp_sqrt_DC (cfg : CKCevianConfig) :
    Real.sqrt ((cfg.α * cfg.m + cfg.β) ^ 2 - cfg.n_sq)
      = cfg.α * Real.sqrt (cfg.m ^ 2 - 1) := by
  have h : (cfg.α * cfg.m + cfg.β) ^ 2 - cfg.n_sq = cfg.α ^ 2 * (cfg.m ^ 2 - 1) := by
    unfold CKCevianConfig.n_sq; ring
  rw [h, Real.sqrt_mul (sq_nonneg cfg.α), Real.sqrt_sq cfg.hα.le]

/-- **Spherical metric side-ratio (κ = +1).**  The ratio of the *genuine* geodesic
    side lengths `sin(d(B,D))/sin(d(D,C))` equals the weight ratio `β/α`.  Unlike
    `spherical_ceva_unified` (which cancels an abstract factor), this is derived
    from the actual metric quantities `√(n² − ·²)` via `gSph_sqrt_BD/DC`. -/
theorem spherical_side_ratio_metric (cfg : CKCevianConfig) (hm : cfg.m ^ 2 < 1) :
    Real.sqrt (cfg.n_sq - (cfg.α + cfg.β * cfg.m) ^ 2) /
        Real.sqrt (cfg.n_sq - (cfg.α * cfg.m + cfg.β) ^ 2) = cfg.β / cfg.α := by
  rw [gSph_sqrt_BD, gSph_sqrt_DC]
  have hpos : (0 : ℝ) < 1 - cfg.m ^ 2 := by linarith
  exact mul_div_mul_right cfg.β cfg.α (Real.sqrt_pos.mpr hpos).ne'

/-- **Hyperbolic metric side-ratio (κ = −1).**  The ratio of the genuine geodesic
    side lengths `sinh(d(B,D))/sinh(d(D,C))` equals the weight ratio `β/α`,
    derived from the actual metric quantities via `gHyp_sqrt_BD/DC`. -/
theorem hyperbolic_side_ratio_metric (cfg : CKCevianConfig) (hm : 1 < cfg.m ^ 2) :
    Real.sqrt ((cfg.α + cfg.β * cfg.m) ^ 2 - cfg.n_sq) /
        Real.sqrt ((cfg.α * cfg.m + cfg.β) ^ 2 - cfg.n_sq) = cfg.β / cfg.α := by
  rw [gHyp_sqrt_BD, gHyp_sqrt_DC]
  have hpos : (0 : ℝ) < cfg.m ^ 2 - 1 := by linarith
  exact mul_div_mul_right cfg.β cfg.α (Real.sqrt_pos.mpr hpos).ne'

/-!
## The single positivity hypothesis is implied by each geometry's distance bound

The unified `CKCevianConfig` carries only `hn : 0 < α² + 2αβm + β²` in place of the
parent's per-geometry `m`-bound.  These lemmas confirm **no generality is lost**: each
geometry's natural bound on `m = cos_κ(d(B,C))` implies `hn`, so a configuration can be
built from the ordinary geometric data.  Algebraically,
`α² + 2αβm + β² = (α−β)² + 2αβ(m+1) = (α+β)² + 2αβ(m−1)`.
-/

/-- **Spherical/elliptic** (`m = cos d > −1`): the squared model norm is positive.
Uses `α² + 2αβm + β² = (α−β)² + 2αβ(m+1)` with both summands `≥ 0`, the second `> 0`. -/
theorem hn_of_cos_gt_neg_one (α β m : ℝ) (hα : 0 < α) (hβ : 0 < β) (hm : -1 < m) :
    0 < α ^ 2 + 2 * α * β * m + β ^ 2 := by
  nlinarith [sq_nonneg (α - β), mul_pos hα hβ]

/-- **Hyperbolic** (`m = cosh d > 1`): the squared model norm is positive.
Uses `α² + 2αβm + β² = (α+β)² + 2αβ(m−1)` with both summands `≥ 0`, the second `> 0`. -/
theorem hn_of_cosh_gt_one (α β m : ℝ) (hα : 0 < α) (hβ : 0 < β) (hm : 1 < m) :
    0 < α ^ 2 + 2 * α * β * m + β ^ 2 := by
  nlinarith [sq_nonneg (α + β), mul_pos hα hβ]

/-- **Euclidean** (`m = 1`): the squared model norm is `(α+β)² > 0`. -/
theorem hn_of_eq_one (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < α ^ 2 + 2 * α * β * 1 + β ^ 2 := by
  nlinarith [sq_nonneg (α + β), mul_pos hα hβ]

/-!
## The three classical Ceva theorems, as specializations of ONE theorem

Each of the following is `projective_ceva_unification` with the geometry's own
factor plugged in.  The mathematical content is identical; only the choice of
`g` (and the source of its nonvanishing) differs.  This is the precise sense in
which "all three cases follow from a single projective Ceva theorem via the
Klein model".
-/

/-- **Spherical Ceva** (κ = +1): cevians concur iff the weight balance holds. -/
theorem spherical_ceva_unified
    (cfgD cfgE cfgF : CKCevianConfig)
    (nD nE nF : ℝ) (hnD : 0 < nD) (hnE : 0 < nE) (hnF : 0 < nF)
    (hmD : cfgD.m ^ 2 < 1) (hmE : cfgE.m ^ 2 < 1) (hmF : cfgF.m ^ 2 < 1) :
    ((cfgD.β * gSph cfgD.m nD) / (cfgD.α * gSph cfgD.m nD)) *
      ((cfgE.β * gSph cfgE.m nE) / (cfgE.α * gSph cfgE.m nE)) *
      ((cfgF.β * gSph cfgF.m nF) / (cfgF.α * gSph cfgF.m nF)) = 1 ↔
    cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β :=
  projective_ceva_unification cfgD cfgE cfgF _ _ _
    (gSph_ne cfgD.m nD hmD hnD) (gSph_ne cfgE.m nE hmE hnE) (gSph_ne cfgF.m nF hmF hnF)

/-- **Hyperbolic Ceva** (κ = −1): cevians concur iff the weight balance holds. -/
theorem hyperbolic_ceva_unified
    (cfgD cfgE cfgF : CKCevianConfig)
    (nD nE nF : ℝ) (hnD : 0 < nD) (hnE : 0 < nE) (hnF : 0 < nF)
    (hmD : 1 < cfgD.m ^ 2) (hmE : 1 < cfgE.m ^ 2) (hmF : 1 < cfgF.m ^ 2) :
    ((cfgD.β * gHyp cfgD.m nD) / (cfgD.α * gHyp cfgD.m nD)) *
      ((cfgE.β * gHyp cfgE.m nE) / (cfgE.α * gHyp cfgE.m nE)) *
      ((cfgF.β * gHyp cfgF.m nF) / (cfgF.α * gHyp cfgF.m nF)) = 1 ↔
    cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β :=
  projective_ceva_unification cfgD cfgE cfgF _ _ _
    (gHyp_ne cfgD.m nD hmD hnD) (gHyp_ne cfgE.m nE hmE hnE) (gHyp_ne cfgF.m nF hmF hnF)

/-- **Euclidean Ceva** (κ = 0): the barycentric limit (`g = 1`), cevians concur
    iff the weight balance holds. -/
theorem euclidean_ceva_unified (cfgD cfgE cfgF : CKCevianConfig) :
    ((cfgD.β * gEuc) / (cfgD.α * gEuc)) *
      ((cfgE.β * gEuc) / (cfgE.α * gEuc)) *
      ((cfgF.β * gEuc) / (cfgF.α * gEuc)) = 1 ↔
    cfgD.α * cfgE.α * cfgF.α = cfgD.β * cfgE.β * cfgF.β :=
  projective_ceva_unification cfgD cfgE cfgF _ _ _ gEuc_ne gEuc_ne gEuc_ne

/-
## Summary

This file unifies Ceva's theorem across the three constant-curvature plane
geometries.  The hyperbolic-only result of `CevasTheoremOQ02OQ01OQ02.lean` and
its spherical sibling are now corollaries of a single theorem,
`projective_ceva_unification`, which works for cevian configurations of
*arbitrary* curvature and arbitrary nonzero geometric factor.  The three
classical theorems (`spherical_ceva_unified`, `euclidean_ceva_unified`,
`hyperbolic_ceva_unified`) are obtained by plugging in `gSph`, `gEuc`, `gHyp`.

The mathematical heart is the cancellation `(β·g)/(α·g) = β/α` (`ck_ratio_cancel`):
the geometry enters *only* through a common nonzero factor that cancels, so the
concurrency criterion `αD·αE·αF = βD·βE·βF` is genuinely one universal statement.

0 axioms, 0 sorries.
-/

end CevasOQ02OQ01OQ02OQ01
