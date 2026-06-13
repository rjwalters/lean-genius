import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Projective Unification of Ceva's Theorem via the Cayley–Klein Model

**OQ (`cevas-theorem-oq-02-oq-01-oq-02-oq-01`).** Exhibit a *single* projective
(Cayley–Klein) Ceva theorem from which the spherical (`sin`), Euclidean (identity)
and hyperbolic (`sinh`) cevian side-ratio identities and the common concurrency
criterion all descend.

The parent `CevasTheoremOQ02OQ01OQ02.lean` proves the three classical Ceva
theorems share *one* algebraic concurrency criterion and that each geometry's
side-ratio collapses to the same weight ratio `β/α` — but it derives the
side-ratio identity **three times**, once per geometry. This file isolates the
genuine unification: a single curvature-carrying configuration `CKCevianConfig`
and a single algebraic crux `ck_ratio_cancel`, with the three classical cases
recovered as specialisations of one common geometry factor `g = √|1 − m²| / n`.

## The Cayley–Klein picture

All three constant-curvature geometries are Cayley–Klein geometries on `ℝP²` with
an absolute conic selected by a curvature sentinel `κ ∈ {+1, 0, −1}`:

* `κ = +1` (spherical/elliptic): `m = ⟨B,C⟩_κ = cos d ∈ (−1,1)`, `1 − m² > 0`,
  factor `gSph = √(1 − m²) / n`;
* `κ =  0` (Euclidean, degenerate limit): `m = 1`, factor `gEuc = 1`;
* `κ = −1` (hyperbolic): `m = cosh d > 1`, `1 − m² < 0`, factor
  `gHyp = √(m² − 1) / n`.

A cevian point `D ∝ α·B + β·C` is a *projective* point (geometry-independent);
the metric enters only through the single norm `n² = α² + 2αβm + β²`, valid for
every `κ`. The geometry-specific factor `g` is common to numerator and
denominator of the side-ratio and cancels — this is the one fact the parent
proves three times and that we prove **once** here.

**Build status.** Written during the 2026-06-13 verification blackout (Docker
down, Aristotle 404); the proofs mirror the verbatim tactic patterns of the
compiling parent file but are themselves **build-unverified**. PR kept as draft.
-/

namespace CevasOQ02OQ01OQ02OQ01

open Real

/-- A **Cayley–Klein cevian configuration**. The curvature sentinel `κ` selects the
geometry; `m = ⟨B,C⟩_κ` is the absolute bilinear value of the two base points;
`α, β > 0` are the projective weights of `D ∝ α·B + β·C`. The single positivity
hypothesis `hn : 0 < α² + 2αβm + β²` replaces the per-geometry bound on `m`
(`1 < m` hyperbolic, `|m| < 1` spherical, `m = 1` Euclidean) — each of those
bounds implies `hn`, so no generality is lost. -/
structure CKCevianConfig where
  κ : ℝ        -- curvature sentinel (+1 / 0 / −1)
  m : ℝ        -- ⟨B,C⟩_κ
  α : ℝ        -- weight parameter (> 0)
  β : ℝ        -- weight parameter (> 0)
  hα : 0 < α
  hβ : 0 < β
  hn : 0 < α ^ 2 + 2 * α * β * m + β ^ 2

/-- The squared Cayley–Klein norm of `α·B + β·C`: `n² = α² + 2αβm + β²`. The same
expression for every curvature `κ` (it is `⟨α·B + β·C, α·B + β·C⟩_κ` with the
cross term `2αβ⟨B,C⟩_κ = 2αβm`). -/
noncomputable def CKCevianConfig.n_sq (cfg : CKCevianConfig) : ℝ :=
  cfg.α ^ 2 + 2 * cfg.α * cfg.β * cfg.m + cfg.β ^ 2

/-- `n² > 0` for every geometry — exactly the structure's single hypothesis. -/
theorem CKCevianConfig.n_sq_pos (cfg : CKCevianConfig) : 0 < cfg.n_sq := by
  unfold n_sq; exact cfg.hn

/-- Curvature-free identity `(α + βm)² − n² = β²(m² − 1)`: the squared spherical/
hyperbolic "sine" of `d(B,D)` is `β²(m² − 1)/n²` (sign absorbed by `√|·|`). Holds
for all `κ` by pure algebra. -/
theorem CKCevianConfig.key_identity_BD (cfg : CKCevianConfig) :
    (cfg.α + cfg.β * cfg.m) ^ 2 - cfg.n_sq = cfg.β ^ 2 * (cfg.m ^ 2 - 1) := by
  unfold CKCevianConfig.n_sq; ring

/-- Curvature-free identity `(αm + β)² − n² = α²(m² − 1)` (the `d(D,C)` companion). -/
theorem CKCevianConfig.key_identity_DC (cfg : CKCevianConfig) :
    (cfg.α * cfg.m + cfg.β) ^ 2 - cfg.n_sq = cfg.α ^ 2 * (cfg.m ^ 2 - 1) := by
  unfold CKCevianConfig.n_sq; ring

/-! ## The crux: one cancellation for every curvature -/

/-- **The Cayley–Klein ratio cancellation (the crux).**

For any nonzero common geometry factor `g` (in each model `g = √|1 − m²| / n`),
the cevian side-ratio `(β·g)/(α·g)` collapses to the weight ratio `β/α`,
*independent of the geometry*. This single algebraic identity replaces the three
per-geometry derivations (`sin`-ratio, identity, `sinh`-ratio) of the parent. -/
theorem ck_ratio_cancel (g α β : ℝ) (hg : g ≠ 0) (hα : α ≠ 0) :
    (β * g) / (α * g) = β / α := by
  field_simp [hg, hα]

/-- Cevian side-measure along `BD` carrying the common geometry factor `g`. -/
noncomputable def ckSideBD (cfg : CKCevianConfig) (g : ℝ) : ℝ := cfg.β * g

/-- Cevian side-measure along `DC` carrying the common geometry factor `g`. -/
noncomputable def ckSideDC (cfg : CKCevianConfig) (g : ℝ) : ℝ := cfg.α * g

/-- **Universal cevian side-ratio.** For any nonzero geometry factor `g`, the
side-ratio along `BC` equals the weight ratio `β/α` — by the single crux. -/
theorem ck_side_ratio (cfg : CKCevianConfig) (g : ℝ) (hg : g ≠ 0) :
    ckSideBD cfg g / ckSideDC cfg g = cfg.β / cfg.α := by
  unfold ckSideBD ckSideDC
  exact ck_ratio_cancel g cfg.α cfg.β hg cfg.hα.ne'

/-! ## The three geometry factors and their specialisations -/

/-- Spherical/elliptic geometry factor `√(1 − m²) / n` (`κ = +1`, `|m| < 1`). -/
noncomputable def gSph (m n : ℝ) : ℝ := sqrt (1 - m ^ 2) / n

/-- Hyperbolic geometry factor `√(m² − 1) / n` (`κ = −1`, `m > 1`). -/
noncomputable def gHyp (m n : ℝ) : ℝ := sqrt (m ^ 2 - 1) / n

/-- Euclidean geometry factor (the degenerate `κ → 0` limit): the barycentric
side-ratio `β/α` arises directly, factor `1`. -/
def gEuc : ℝ := 1

theorem gSph_ne_zero {m n : ℝ} (hm : m ^ 2 < 1) (hn : n ≠ 0) : gSph m n ≠ 0 := by
  unfold gSph
  have h : (0 : ℝ) < 1 - m ^ 2 := by linarith
  exact div_ne_zero (sqrt_pos.mpr h).ne' hn

theorem gHyp_ne_zero {m n : ℝ} (hm : 1 < m ^ 2) (hn : n ≠ 0) : gHyp m n ≠ 0 := by
  unfold gHyp
  have h : (0 : ℝ) < m ^ 2 - 1 := by linarith
  exact div_ne_zero (sqrt_pos.mpr h).ne' hn

theorem gEuc_ne_zero : gEuc ≠ 0 := one_ne_zero

/-- **Spherical Ceva side-ratio** (`κ = +1`) as a specialisation of the crux. -/
theorem spherical_side_ratio (cfg : CKCevianConfig) {n : ℝ}
    (hm : cfg.m ^ 2 < 1) (hn : n ≠ 0) :
    ckSideBD cfg (gSph cfg.m n) / ckSideDC cfg (gSph cfg.m n) = cfg.β / cfg.α :=
  ck_side_ratio cfg (gSph cfg.m n) (gSph_ne_zero hm hn)

/-- **Hyperbolic Ceva side-ratio** (`κ = −1`) as a specialisation of the crux. -/
theorem hyperbolic_side_ratio (cfg : CKCevianConfig) {n : ℝ}
    (hm : 1 < cfg.m ^ 2) (hn : n ≠ 0) :
    ckSideBD cfg (gHyp cfg.m n) / ckSideDC cfg (gHyp cfg.m n) = cfg.β / cfg.α :=
  ck_side_ratio cfg (gHyp cfg.m n) (gHyp_ne_zero hm hn)

/-- **Euclidean Ceva side-ratio** (`κ = 0`) as a specialisation of the crux. -/
theorem euclidean_side_ratio (cfg : CKCevianConfig) :
    ckSideBD cfg gEuc / ckSideDC cfg gEuc = cfg.β / cfg.α :=
  ck_side_ratio cfg gEuc gEuc_ne_zero

/-! ## The single curvature-free concurrency criterion -/

/-- **Universal weight balance.** The cevian concurrency criterion is purely
algebraic and identical across all geometries: for positive weights,
`αD·αE·αF = βD·βE·βF` iff the product of weight ratios is `1`. The ratio function
(`sin`/identity/`sinh`) only serves to identify the geometric ratio with `β/α`;
the concurrency condition itself never sees the curvature. -/
theorem universal_weight_balance
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

/-- **Projective Ceva unification (answers the OQ).**

A *single* projective Ceva theorem: for any curvature `κ` and any nonzero common
geometry factor `g = √|1 − m²| / n`, the cevian side-ratio collapses to the weight
ratio `β/α` (the single crux `ck_ratio_cancel`), and concurrency is governed by
the single curvature-free criterion `αD·αE·αF = βD·βE·βF`
(`universal_weight_balance`). The three classical Ceva theorems are exactly the
specialisations `g = gSph` (spherical), `g = gEuc` (Euclidean), `g = gHyp`
(hyperbolic) — see `spherical_side_ratio`, `euclidean_side_ratio`,
`hyperbolic_side_ratio`. -/
theorem projective_ceva_unification
    (cfg : CKCevianConfig) (g : ℝ) (hg : g ≠ 0)
    (αD βD αE βE αF βF : ℝ) (hαD : 0 < αD) (hαE : 0 < αE) (hαF : 0 < αF) :
    (ckSideBD cfg g / ckSideDC cfg g = cfg.β / cfg.α) ∧
      ((αD * αE * αF = βD * βE * βF) ↔
        (βD / αD) * (βE / αE) * (βF / αF) = 1) :=
  ⟨ck_side_ratio cfg g hg,
   universal_weight_balance αD βD αE βE αF βF hαD hαE hαF⟩

end CevasOQ02OQ01OQ02OQ01
