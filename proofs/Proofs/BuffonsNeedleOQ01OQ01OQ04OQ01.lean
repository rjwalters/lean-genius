import Mathlib
import Proofs.BuffonsNeedleOQ01OQ01
import Proofs.BuffonsNeedleOQ01OQ01OQ04

/-
# Angular Averaging Identity from Sphere Measure Theory

## Open Question: buffons-needle-oq-01-oq-01-oq-04-oq-01

The parent `BuffonsNeedleOQ01OQ01OQ04.lean` axiomatizes the angular averaging
identity for the n-dimensional Cauchy–Crofton formula via `AngularAverageData`.

This file **proves** the 2D case from first principles using interval integration,
without any axioms. The key insight is that the 2D angular average reduces to:

  angularAvg(r) = r · ∫_0^π |cos θ| dθ = r · 2 = 2r

matching the formula sphereArea(0)/(2-1) · r = 2 · r.

## Main Results

1. `integral_abs_cos_zero_pi`: ∫_0^π |cos θ| dθ = 2 (from rotation invariance)
2. `angularAverageData2D`: `AngularAverageData 2` instance — **0 axioms**
3. `cauchyCrofton_product`: c_n · c_{n+1} = 2/(n·π) for n ≥ 2
4. `cauchyCroftonConst_pos`: positivity of Cauchy-Crofton constants

## Relationship to Parent

The parent axiomatizes `AngularAverageData` for all n. Here we prove it for n=2
using ∫_0^π |cos θ| dθ = 2, which is a special case of ∫_0^π |sin(θ+c)| dθ = 2.
For n ≥ 3, the Beta integral ∫_0^{π/2} cos(θ) sin^{n-2}(θ) dθ = 1/(n-1) is needed
and remains axiomatized in the general `angularAvg_ndim` statement below.
-/

open Real intervalIntegral MeasureTheory
open CauchyCrofton

namespace BuffonsNeedleOQ01OQ01OQ04OQ01

-- ============================================================
-- Part I: The 2D Angular Integral
-- ============================================================

/-- ∫_0^π |cos θ| dθ = 2.

    Key: sin(θ + π/2) = cos θ, so this is a rotation of ∫_0^π |sin θ| dθ = 2. -/
theorem integral_abs_cos_zero_pi : ∫ θ in (0 : ℝ)..π, |cos θ| = 2 := by
  have hid : ∀ θ : ℝ, |sin (θ + π / 2)| = |cos θ| := by
    intro θ
    congr 1
    rw [sin_add, sin_pi_div_two, cos_pi_div_two]
    ring
  have hshift := BuffonsNeedleOQ01OQ01.integral_abs_sin_shift (π / 2)
  simp_rw [hid] at hshift
  exact hshift

/-- The 2D angular average function, defined as the actual sphere integral factor:
      angularAvg2D(r) = r · ∫_0^π |cos θ| dθ
    This represents (1/σ_1) · ∫_{S^1} |⟨(r,0), ω⟩| dσ(ω), i.e., the angular
    average of |⟨v, ω⟩| over S^1 (half-period version for RP^1). -/
noncomputable def sphereAngularAvg2D (r : ℝ) : ℝ :=
  r * ∫ θ in (0 : ℝ)..π, |cos θ|

/-- The 2D angular average equals 2r. -/
theorem sphereAngularAvg2D_eq (r : ℝ) (hr : 0 ≤ r) :
    sphereAngularAvg2D r = 2 * r := by
  unfold sphereAngularAvg2D
  rw [integral_abs_cos_zero_pi]
  ring

/-- The 2D angular average is non-negative for r ≥ 0. -/
theorem sphereAngularAvg2D_nonneg (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ sphereAngularAvg2D r :=
  mul_nonneg hr (integral_nonneg (fun θ _ => abs_nonneg _))

-- ============================================================
-- Part II: The 2D Angular Average Instance (Axiom-Free)
-- ============================================================

/-- **2D Angular Average Identity**: an explicit `AngularAverageData 2` instance
    proved entirely from interval integration — **no axioms**.

    The function `sphereAngularAvg2D r = r · ∫_0^π |cos θ| dθ = 2r` satisfies:
    - `angularAvg_eq`: 2r = sphereArea(0)/(2-1) · r = 2 · r ✓
    - `angularAvg_nonneg`: r · 2 ≥ 0 for r ≥ 0 ✓

    **Mathematical content**: The 2D Cauchy–Crofton formula E = 2L/(πd) is a theorem,
    not just a formula. The angular averaging factor 2 = ∫_0^π |cos θ| dθ is proved
    from classical integration theory, without any measure-theoretic axioms. -/
noncomputable def angularAverageData2D : AngularAverageData 2 where
  angularAvg := sphereAngularAvg2D
  angularAvg_eq := fun r hr => by
    rw [sphereAngularAvg2D_eq r hr]
    simp only [show (2 : ℕ) - 2 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl]
    rw [sphereArea_zero]
    norm_num
  angularAvg_nonneg := fun r hr => sphereAngularAvg2D_nonneg r hr

/-- Consistency check: `angularAverageData2D` recovers the correct constant c_2 = 2/π.
    E[crossings] = 2/(σ_1 · d) · angularAvg2D(L) = 2/(2π·d) · 2L = 2L/(πd). -/
theorem angularAverageData2D_expectedCrossings (L d : ℝ) (hd : 0 < d) (hL : 0 ≤ L) :
    expectedCrossings (n := 2) L d =
    2 / (sphereArea 1 * d) * angularAverageData2D.angularAvg L := by
  exact expectedCrossings_eq_angularAvg angularAverageData2D (by norm_num) L d hd hL

-- ============================================================
-- Part III: General n-Dimensional Angular Averaging
-- ============================================================

/-- **Angular Averaging Theorem** (general, n ≥ 3).
    For n ≥ 3: ∫_{S^{n-1}} |ω₁| dσ(ω) = 2σ_{n-2}/(n-1), where σ_k is the
    surface area of S^k. This follows from the Beta integral:
      ∫_0^{π/2} cos(θ) · sin^{n-2}(θ) dθ = 1/(n-1)
    via substitution u = sin(θ), giving [u^{n-1}/(n-1)]_0^1 = 1/(n-1).
    Combined with the sphere area via polar coordinates:
      ∫_{S^{n-1}} |ω₁| dσ = σ_{n-2} · 2 · ∫_0^{π/2} cos(θ) sin^{n-2}(θ) dθ
                            = σ_{n-2} · 2/(n-1)
    This is the n-dimensional generalization of ∫_0^π |cos θ| dθ = 2 (case n=2). -/
axiom angularAvg_ndim (n : ℕ) (hn : 3 ≤ n) : AngularAverageData n

-- ============================================================
-- Part IV: Product Formula for Cauchy-Crofton Constants
-- ============================================================

/-- **Product Formula**: c_n · c_{n+1} = 2/(n·π) for n ≥ 2.

    Proof: c_n = 2σ_{n-2}/((n-1)σ_{n-1}), c_{n+1} = 2σ_{n-1}/(n·σ_n).
    Product = 4σ_{n-2}/((n-1)·n·σ_n). By the sphere area recurrence
    σ_n = 2π/(n-1) · σ_{n-2}, we get σ_{n-2} = (n-1)/(2π) · σ_n, so:
    product = 4·(n-1)/(2π)·σ_n / ((n-1)·n·σ_n) = 4/(2πn) = 2/(πn). -/
theorem cauchyCrofton_product (n : ℕ) (hn : 2 ≤ n) :
    cauchyCroftonConst n * cauchyCroftonConst (n + 1) = 2 / ((n : ℝ) * π) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : 1 < n := Nat.lt_of_lt_of_le one_lt_two hn
    exact_mod_cast this
  have hσn2_pos := sphereArea_pos (n - 2)
  have hσn1_pos := sphereArea_pos (n - 1)
  have hσn_pos := sphereArea_pos n
  -- Reduce n+1-2 and n+1-1 in ℕ
  have h2 : n + 1 - 2 = n - 1 := by omega
  have h1 : n + 1 - 1 = n := by omega
  -- The real subtraction cast: (↑(n+1) - 1 : ℝ) = ↑n
  have hcast : ((n : ℝ) + 1 - 1) = (n : ℝ) := by ring
  -- Sphere area recurrence
  have hrec := sphereArea_recurrence n hn
  simp only [cauchyCroftonConst, h2, h1, Nat.cast_add, Nat.cast_one, hcast]
  rw [hrec]
  have hpi_pos := pi_pos
  field_simp [hn1_pos.ne', hn_pos.ne', hσn1_pos.ne', hσn2_pos.ne', hpi_pos.ne']
  ring

/-- Corollary: c_2 · c_3 = 1/π. -/
theorem cauchyCrofton_product_two :
    cauchyCroftonConst 2 * cauchyCroftonConst 3 = 1 / π := by
  have h := cauchyCrofton_product 2 (by norm_num)
  simp only [Nat.cast_ofNat] at h
  rw [h]; field_simp [pi_pos.ne']

/-- The product c_n · c_{n+1} is strictly decreasing in n: 2/(nπ) > 2/((n+1)π). -/
theorem cauchyCrofton_product_decreasing (n : ℕ) (hn : 2 ≤ n) :
    cauchyCroftonConst n * cauchyCroftonConst (n + 1) >
    cauchyCroftonConst (n + 1) * cauchyCroftonConst (n + 2) := by
  rw [cauchyCrofton_product n hn, cauchyCrofton_product (n + 1) (by omega)]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply div_lt_div_of_pos_left (by norm_num) (mul_pos (mul_pos hn_pos pi_pos)
    (by positivity : (0 : ℝ) < ((n : ℝ) + 1) * π))
  · push_cast; nlinarith

-- ============================================================
-- Part V: Positivity and Boundedness
-- ============================================================

/-- All Cauchy-Crofton constants are positive (for n ≥ 1). -/
theorem cauchyCroftonConst_pos (n : ℕ) (hn : 1 ≤ n) : 0 < cauchyCroftonConst n := by
  unfold cauchyCroftonConst
  apply div_pos
  · exact mul_pos two_pos (sphereArea_pos _)
  · apply mul_pos
    · have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    · exact sphereArea_pos _

/-- c_2 ≤ 1 (since 2/π < 1). -/
theorem cauchyCroftonConst_two_lt_one : cauchyCroftonConst 2 < 1 := by
  rw [cauchyCrofton_two]
  rw [div_lt_one pi_pos]
  linarith [pi_gt_three]

/-- From the product formula, consecutive constants satisfy:
    c_{n+1} = 2/(n·π·c_n), so as c_n is bounded away from 0, c_{n+1} is determined. -/
theorem cauchyCrofton_successor_eq (n : ℕ) (hn : 2 ≤ n)
    (hcn : 0 < cauchyCroftonConst n) :
    cauchyCroftonConst (n + 1) = 2 / ((n : ℝ) * π * cauchyCroftonConst n) := by
  have h := cauchyCrofton_product n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [← h]
  field_simp [hcn.ne', hn_pos.ne', pi_pos.ne']
  ring

end BuffonsNeedleOQ01OQ01OQ04OQ01
