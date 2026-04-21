import Mathlib

/-
# Steiner's Formula: d/dr Vol(B_r^n) = Area(∂B_r^n)
# (area-of-circle-oq-01-oq-02-oq-03-oq-03)

## The Open Question

**OQ-01-OQ-02-OQ-03-OQ-03**: Can the infinitesimal Archimedes principle be
formalized as Steiner's formula for n-dimensional balls?

The Archimedes perspective: a thin shell of thickness dr at radius r
contributes Surface_Area(r) × dr to the ball's volume. Taking dr → 0:

    d/dr Vol(B_r^n) = Area(∂B_r^n)

## The Answer

Yes. Since Vol(B_r^n) = ω_n · r^n is polynomial in r, differentiation by
the power rule yields:

    d/dr [ω_n r^n] = n · ω_n · r^(n-1) = Area(∂B_r^n)

This is **Steiner's formula** for n-balls — the n-dimensional generalization
of the classical circumference–area duality d(πr²)/dr = 2πr.

## Special Cases

| n | Vol(B_r^n)    | Area(∂B_r^n) | Steiner's formula         |
|---|---------------|--------------|---------------------------|
| 1 | 2r            | 2            | d/dr[2r] = 2 ✓            |
| 2 | πr²           | 2πr          | d/dr[πr²] = 2πr ✓         |
| 3 | (4π/3)r³      | 4πr²         | d/dr[(4π/3)r³] = 4πr² ✓  |
| n | ω_n · r^n     | n·ω_n·r^(n-1)| d/dr[ω_n r^n] = n ω_n r^(n-1) ✓ |

## What This File Proves (9 theorems, 0 sorries, 0 axioms)

- **Part I**: Steiner's formula via direct differentiation (HasDerivAt and deriv forms)
- **Part II**: The Archimedes shell limit interpretation
- **Part III**: Volume from surface area via FTC (∫₀ʳ S_n = V_n)
- **Part IV**: Shell/annulus formula (∫_{r₁}^{r₂} S_n = V_n(r₂) − V_n(r₁))
- **Part V**: Special cases n = 2, 3 with explicit formulas

## Connection to Parent

The parent proof (OQ-03, Archimedes Exhaustion meets FTC) established that
the polygon approximation and FTC integral agree in 2D. This OQ shows that
the FTC half generalizes cleanly to all dimensions via Steiner's formula.

## References

- Steiner (1840): *Einige Gesetze über die Theilung der Ebene und des Raumes*
- AreaOfCircleOQ01OQ02OQ01.lean: n-ball volume from surface area integral
- AreaOfCircleOQ01OQ02OQ03.lean: Archimedes exhaustion meets FTC (parent)
-/

set_option linter.unusedVariables false

namespace SteinerFormulaNBall

open Real MeasureTheory intervalIntegral

noncomputable section

-- ============================================================
-- DEFINITIONS: Unit ball volume and surface area functions
-- ============================================================

/-- The unit n-ball volume: ω_n = π^(n/2) / Γ(n/2 + 1).
    Matches NDimVolumeIntegral.unitBallVolume; redefined for self-containedness. -/
def unitBallVolume (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/-- The n-ball volume function: V_n(r) = ω_n · r^n. -/
def nBallVol (n : ℕ) (r : ℝ) : ℝ :=
  unitBallVolume n * r ^ n

/-- The (n-1)-sphere surface area: S_n(r) = n · ω_n · r^(n-1).
    - n = 1: S₁(r) = 2    (two endpoints of interval [-r,r])
    - n = 2: S₂(r) = 2πr  (circumference of circle)
    - n = 3: S₃(r) = 4πr² (surface area of sphere) -/
def nSphereArea (n : ℕ) (r : ℝ) : ℝ :=
  n * unitBallVolume n * r ^ (n - 1)

-- ============================================================
-- SUPPORTING LEMMAS
-- ============================================================

/-- ω_n ≥ 0 for all n. -/
lemma unitBallVolume_nonneg (n : ℕ) : 0 ≤ unitBallVolume n := by
  unfold unitBallVolume
  apply div_nonneg
  · exact rpow_nonneg (le_of_lt pi_pos) _
  · exact le_of_lt (Gamma_pos_of_pos (by positivity))

/-- ω_2 = π. -/
lemma unitBallVolume_two : unitBallVolume 2 = π := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) / 2 + 1 = 2 from by ring, show (2 : ℝ) / 2 = 1 from by ring,
      rpow_one, Gamma_two]
  simp

/-- ω_3 = 4π/3. -/
lemma unitBallVolume_three : unitBallVolume 3 = 4 * π / 3 := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  have h32 : Gamma (3 / 2 : ℝ) = √π / 2 := by
    have h := Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring] at h
    rw [h, Gamma_one_half_eq]; ring
  have h52 : Gamma (5 / 2 : ℝ) = 3 * √π / 4 := by
    have h := Gamma_add_one (show (3 / 2 : ℝ) ≠ 0 from by norm_num)
    rw [show (3 : ℝ) / 2 + 1 = 5 / 2 from by ring] at h
    rw [h, h32]; ring
  rw [show (3 : ℝ) / 2 + 1 = 5 / 2 from by ring, h52,
      show (3 : ℝ) / 2 = 1 + 1 / 2 from by ring,
      rpow_add pi_pos, rpow_one, ← Real.sqrt_eq_rpow]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp [hpi.ne']; ring

/-- S_n is continuous. -/
lemma continuous_nSphereArea (n : ℕ) : Continuous (nSphereArea n) := by
  unfold nSphereArea; exact continuous_const.mul (continuous_pow (n - 1))

/-- V_n(0) = 0 for n ≥ 1. -/
lemma nBallVol_zero (n : ℕ) (hn : 1 ≤ n) : nBallVol n 0 = 0 := by
  unfold nBallVol; simp [zero_pow (by omega : n ≠ 0)]

-- ============================================================
-- PART I: STEINER'S FORMULA
-- ============================================================

/-- **Steiner's Formula** — HasDerivAt form.

    The derivative of the n-ball volume function with respect to radius equals
    the surface area of the (n-1)-sphere:

        d/dr [ω_n · r^n] = n · ω_n · r^(n-1)

    This is the n-dimensional Archimedes principle: an infinitesimally thin
    shell of thickness dr at radius r contributes S_n(r) · dr to the volume. -/
theorem steiners_formula (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (nBallVol n) (nSphereArea n r) r := by
  unfold nBallVol nSphereArea
  have h := (hasDerivAt_pow n r).const_mul (unitBallVolume n)
  convert h using 1
  ring

/-- **Steiner's Formula** — pointwise deriv form.

    Differentiating the volume function yields the surface area at each radius. -/
theorem steiners_formula_deriv (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    deriv (nBallVol n) r = nSphereArea n r :=
  (steiners_formula n hn r).deriv

-- ============================================================
-- PART II: THE ARCHIMEDES SHELL LIMIT
-- ============================================================

/-- **Shell Limit** — the ratio of shell volume to thickness converges to surface area.

    As h → 0 (with h ≠ 0):
        [V_n(r + h) - V_n(r)] / h  →  S_n(r)

    Interpretation: the volume added by expanding the ball from radius r to r+h
    is approximately S_n(r) · h — a shell of surface area S_n(r) and thickness h.
    Steiner's formula is exactly this limit.

    Proof: The ratio equals the slope of V_n at r evaluated at r+h. As h → 0,
    the map h ↦ r+h sends the punctured neighborhood of 0 to the punctured
    neighborhood of r, and the slope limit is exactly the derivative. -/
theorem shell_limit (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    Filter.Tendsto
      (fun h : ℝ => (nBallVol n (r + h) - nBallVol n r) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (nSphereArea n r)) := by
  have hd := hasDerivAt_iff_tendsto_slope.mp (steiners_formula n hn r)
  -- hd : Tendsto (slope (nBallVol n) r) (𝓝[{r}ᶜ] r) (𝓝 (nSphereArea n r))
  -- The map h ↦ r + h sends 𝓝[{0}ᶜ] 0 to 𝓝[{r}ᶜ] r
  have hmap : Filter.Tendsto (fun h : ℝ => r + h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin r {r}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (by have : Filter.Tendsto (fun h : ℝ => r + h) (𝓝 0) (𝓝 r) := by
            have := (continuous_const.add continuous_id).continuousAt (x := (0 : ℝ))
            simpa using this
          exact this.mono_left nhdsWithin_le_nhds)
      (Filter.eventually_nhdsWithin_of_forall fun h hh =>
        show r + h ≠ r from fun h' => hh (show h = 0 from by linarith))
  -- Rewrite the ratio as a slope evaluation
  have heq : ∀ h : ℝ, (nBallVol n (r + h) - nBallVol n r) / h =
      slope (nBallVol n) r (r + h) := fun h => by
    rw [slope_def_field]; congr 1; ring
  simp_rw [heq]
  -- Compose: slope f r (r + h) → slope f r y as h → 0 (i.e., y → r)
  exact hd.comp hmap

-- ============================================================
-- PART III: VOLUME FROM SURFACE AREA (FTC)
-- ============================================================

/-- **FTC Form of Steiner's Formula**: V_n(r) = ∫₀ʳ S_n(ρ) dρ.

    By FTC Part 2, since d/dρ[V_n(ρ)] = S_n(ρ) and S_n is continuous:
        ∫₀ʳ S_n(ρ) dρ = V_n(r) - V_n(0) = V_n(r). -/
theorem volume_from_steiner (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, nSphereArea n ρ = nBallVol n r := by
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt (nBallVol n) (nSphereArea n x) x :=
    fun x _ => steiners_formula n hn x
  have h_int : IntervalIntegrable (nSphereArea n) volume 0 r :=
    (continuous_nSphereArea n).intervalIntegrable 0 r
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int, nBallVol_zero n hn, sub_zero]

-- ============================================================
-- PART IV: SHELL / ANNULUS FORMULA
-- ============================================================

/-- **Shell Formula**: ∫_{r₁}^{r₂} S_n(ρ) dρ = V_n(r₂) − V_n(r₁).

    The volume of the n-dimensional shell between radii r₁ and r₂ equals
    the integral of surface area over the radius range. -/
theorem shell_volume (n : ℕ) (hn : 1 ≤ n) (r₁ r₂ : ℝ) :
    ∫ ρ in r₁..r₂, nSphereArea n ρ = nBallVol n r₂ - nBallVol n r₁ := by
  have h_deriv : ∀ x ∈ Set.uIcc r₁ r₂,
      HasDerivAt (nBallVol n) (nSphereArea n x) x :=
    fun x _ => steiners_formula n hn x
  exact integral_eq_sub_of_hasDerivAt h_deriv
    ((continuous_nSphereArea n).intervalIntegrable r₁ r₂)

-- ============================================================
-- PART V: SPECIAL CASES
-- ============================================================

/-- n = 2: d/dr[πr²] = 2πr (classical circumference = dA/dr). -/
theorem steiner_2d (r : ℝ) :
    HasDerivAt (nBallVol 2) (nSphereArea 2 r) r :=
  steiners_formula 2 (by norm_num) r

/-- n = 2 with explicit formulas: d/dr[πr²] = 2πr. -/
theorem steiner_2d_explicit (r : ℝ) :
    HasDerivAt (fun x => π * x ^ 2) (2 * π * r) r := by
  have h := steiner_2d r
  convert h using 1
  · ext x; simp [nBallVol, unitBallVolume_two]
  · simp [nSphereArea, unitBallVolume_two]

/-- n = 3: d/dr[(4π/3)r³] = 4πr² (sphere surface area = dV/dr). -/
theorem steiner_3d (r : ℝ) :
    HasDerivAt (nBallVol 3) (nSphereArea 3 r) r :=
  steiners_formula 3 (by norm_num) r

/-- n = 3 with explicit formulas: d/dr[(4π/3)r³] = 4πr². -/
theorem steiner_3d_explicit (r : ℝ) :
    HasDerivAt (fun x => 4 * π / 3 * x ^ 3) (4 * π * r ^ 2) r := by
  have h := steiner_3d r
  convert h using 1
  · ext x; simp [nBallVol, unitBallVolume_three]
  · simp [nSphereArea, unitBallVolume_three]
    push_cast; ring

/-- The surface-to-volume ratio S_n(r) / V_n(r) = n/r for r ≠ 0, n ≥ 1. -/
theorem surface_to_volume_ratio (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : r ≠ 0) :
    nSphereArea n r / nBallVol n r = n / r := by
  unfold nSphereArea nBallVol
  have hω : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact div_ne_zero (rpow_pos_of_pos pi_pos _).ne' (Gamma_pos_of_pos (by positivity)).ne'
  have hrn : r ^ n ≠ 0 := pow_ne_zero n hr
  field_simp [hω, hrn, hr]
  rw [show r ^ (n - 1) * (unitBallVolume n * r ^ n)⁻¹ =
      (unitBallVolume n)⁻¹ * (r ^ (n - 1) * (r ^ n)⁻¹) from by ring,
      ← pow_sub₀ hr (by omega : n - 1 ≤ n)]
  simp [show n - (n - 1) = 1 from by omega]; ring

/- ## Summary

### Proved (9 theorems, 0 sorries, 0 axioms):

1. `steiners_formula` — d/dr[V_n(r)] = S_n(r) for all n ≥ 1 (HasDerivAt form)
2. `steiners_formula_deriv` — deriv(V_n) r = S_n(r) (pointwise deriv form)
3. `shell_limit` — lim_{h→0} [V_n(r+h) - V_n(r)] / h = S_n(r) (Archimedes limit)
4. `volume_from_steiner` — V_n(r) = ∫₀ʳ S_n(ρ) dρ (FTC)
5. `shell_volume` — ∫_{r₁}^{r₂} S_n(ρ) dρ = V_n(r₂) - V_n(r₁) (shell/annulus)
6. `steiner_2d` / `steiner_2d_explicit` — d/dr[πr²] = 2πr
7. `steiner_3d` / `steiner_3d_explicit` — d/dr[(4π/3)r³] = 4πr²
8. `surface_to_volume_ratio` — S_n(r) / V_n(r) = n/r

### Key Insight:

The polynomial structure V_n(r) = ω_n · r^n makes Steiner's formula for n-balls
a routine application of the power rule. The depth is in the geometric interpretation:
the infinitesimal shell principle (thin shell ≈ S_n(r) × dr) is exactly the
derivative, connecting Archimedes' intuition to modern calculus.

The parent proof (OQ-03) shows the FTC–Archimedes connection in 2D.
This file shows the same structure holds in all dimensions via Steiner's formula.
-/

end  -- close noncomputable section

end SteinerFormulaNBall
