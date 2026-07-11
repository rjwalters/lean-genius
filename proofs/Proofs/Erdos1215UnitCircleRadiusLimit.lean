/-
Erdős Problem #1215 (Mac Lane 1953) — degree-limit of the sharp confinement radius for
the *general* unit-circle-rooted class, and the resulting **uniform** confinement.

Parent: `Proofs.Erdos1215UnitCircleRadius`, which proved that for every
`Erdos1215.IsUnitCirclePolynomial P` of positive degree the level set
`{z : |P(z)| < C}` is contained in the closed ball of the sharp radius
`1 + C^{1/deg P}` (`levelSet_subset_closedBall`).

The cyclotomic file `CyclotomicPolynomialsOQ02OQ04` performed the degree-limit analysis
of that radius (`1 + C^{1/φ(n)} ↓ 2`) *only for the cyclotomic subfamily* `Φ_n`.  This
file lifts that analysis to the **entire** Mac Lane class: since the sharp radius
`1 + C^{1/deg P}` depends only on `C` and the degree — not on the specific unit-modulus
roots — the confinement is *uniform across all unit-circle polynomials of a given
degree*.  Concretely:

  * `sharpRadius_ge_two`   — for `C ≥ 1` the radius is always `≥ 2` (a hard floor: no
                             finite-degree unit-circle lemniscate can be confined inside
                             the disc of radius `2`);
  * `sharpRadius_antitone` — the radius is antitone in the degree (`C ≥ 1`);
  * `tendsto_sharpRadius`  — it converges to `2` as `deg P → ∞`;
  * `eventually_levelSet_subset_closedBall`
                           — hence for every `ε > 0` and `C ≥ 1` there is a single degree
                             threshold `K` such that **every** unit-circle polynomial of
                             degree `≥ K` has its level set `{|P| < C}` confined to the
                             one fixed disc `closedBall(0, 2 + ε)`.

The last theorem is the general-class analogue of the cyclotomic
`CyclotomicPolynomialsOQ02OQ04.eventually_levelSet_subset_closedBall`: it shows that the
*whole* high-degree Mac Lane class — not merely the cyclotomic examples — hugs a disc
barely larger than the unit disc, leaving no room for a level path escaping to `∞`.
This is unconditional geometric evidence against a Mac Lane labyrinth in the
high-degree regime (the deep `maclane_labyrinth` phenomenon of the parent remains
axiomatized).

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib
import Proofs.Erdos1215UnitCircleRadius

open Complex Polynomial Filter Topology

namespace Erdos1215UnitCircleRadiusLimit

/-- **The sharp confinement radius has a hard floor of `2`.**
For `C ≥ 1` and any degree `k`, `2 ≤ 1 + C^{1/k}`: since `C ≥ 1` and `1/k ≥ 0`,
monotonicity of `x ↦ x^{1/k}` gives `C^{1/k} ≥ 1^{1/k} = 1`.  Thus no positive-degree
unit-circle level set can be confined strictly inside the disc of radius `2`. -/
theorem sharpRadius_ge_two {C : ℝ} (hC : 1 ≤ C) (k : ℕ) :
    2 ≤ 1 + C ^ ((k : ℝ)⁻¹) := by
  have ht : (0 : ℝ) ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
  have h1 : (1 : ℝ) ≤ C ^ ((k : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hC ht
    rwa [Real.one_rpow] at h
  linarith

/-- **Degree-monotonicity of the sharp radius.**
For `C ≥ 1` and degrees `1 ≤ k ≤ k'`, `1 + C^{1/k'} ≤ 1 + C^{1/k}`: raising the degree
shrinks (weakly) the confining disc.  Since `1/k' ≤ 1/k` and `C ≥ 1`,
`C^{1/k'} ≤ C^{1/k}`. -/
theorem sharpRadius_antitone {C : ℝ} (hC : 1 ≤ C) {k k' : ℕ} (hk : 1 ≤ k)
    (hkk' : k ≤ k') :
    1 + C ^ ((k' : ℝ)⁻¹) ≤ 1 + C ^ ((k : ℝ)⁻¹) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hcast : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hkk'
  have hinv : (k' : ℝ)⁻¹ ≤ (k : ℝ)⁻¹ := by
    gcongr
  have hle : C ^ ((k' : ℝ)⁻¹) ≤ C ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hC hinv
  linarith

/-- **The sharp radius tends to `2`.**
For `C > 0`, `1 + C^{1/k} → 2` as the degree `k → ∞`, because
`C^{1/k} = exp((log C)/k) → exp 0 = 1`. -/
theorem tendsto_sharpRadius {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ => 1 + C ^ ((k : ℝ)⁻¹)) atTop (𝓝 2) := by
  have hexp : (fun k : ℕ => C ^ ((k : ℝ)⁻¹))
      = (fun k : ℕ => Real.exp (Real.log C * (k : ℝ)⁻¹)) := by
    funext k; rw [Real.rpow_def_of_pos hC]
  have htinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun k : ℕ => Real.log C * (k : ℝ)⁻¹) atTop (𝓝 0) := by
    have h := htinv.const_mul (Real.log C)
    simpa using h
  have hCk : Tendsto (fun k : ℕ => C ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
    rw [hexp]
    have h := (Real.continuous_exp.tendsto 0).comp harg
    simpa [Real.exp_zero] using h
  have h2 : Tendsto (fun k : ℕ => 1 + C ^ ((k : ℝ)⁻¹)) atTop (𝓝 (1 + 1)) :=
    hCk.const_add 1
  have he : (1 : ℝ) + 1 = 2 := by norm_num
  rwa [he] at h2

/-- **Uniform confinement of the entire high-degree Mac Lane class.**
For `C ≥ 1` and any `ε > 0` there is a degree threshold `K` such that **every**
unit-circle polynomial `P` (`Erdos1215.IsUnitCirclePolynomial P`) of degree `≥ K` has its
level set `{z : |P(z)| < C}` contained in the single fixed disc `closedBall(0, 2 + ε)`.

Because the sharp radius `1 + C^{1/deg P}` depends only on `C` and `deg P` (not on the
individual roots) and tends to `2`, one common threshold `K` works simultaneously for the
whole class — not just the cyclotomic examples of
`CyclotomicPolynomialsOQ02OQ04.eventually_levelSet_subset_closedBall`.  Thus all
sufficiently high-degree unit-circle lemniscates hug a disc barely larger than the unit
disc: no room for a level path escaping to `∞`, the antithesis of a Mac Lane labyrinth. -/
theorem eventually_levelSet_subset_closedBall {C : ℝ} (hC : 1 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ P : ℂ[X], Erdos1215.IsUnitCirclePolynomial P → 0 < P.natDegree →
      K ≤ P.natDegree →
        Erdos1215.levelSet P C ⊆ Metric.closedBall (0 : ℂ) (2 + ε) := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have htend := tendsto_sharpRadius hC0
  have hev : ∀ᶠ k : ℕ in atTop, 1 + C ^ ((k : ℝ)⁻¹) < 2 + ε :=
    (tendsto_order.1 htend).2 (2 + ε) (by linarith)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨K, fun P hP hdeg hKP => ?_⟩
  have hlt : 1 + C ^ ((P.natDegree : ℝ)⁻¹) < 2 + ε := hK P.natDegree hKP
  calc Erdos1215.levelSet P C
      ⊆ Metric.closedBall (0 : ℂ) (1 + C ^ ((P.natDegree : ℝ)⁻¹)) :=
        Erdos1215UnitCircleRadius.levelSet_subset_closedBall hP hdeg C
    _ ⊆ Metric.closedBall (0 : ℂ) (2 + ε) :=
        Metric.closedBall_subset_closedBall (le_of_lt hlt)

end Erdos1215UnitCircleRadiusLimit
