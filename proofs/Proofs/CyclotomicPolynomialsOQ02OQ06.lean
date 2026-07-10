/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): the sharp outer *area* of the
cyclotomic level set decreases monotonically to `4π` with the degree.

Parent chain:
  OQ02OQ01  the cyclotomic level set `{z : |Φ_n(z)| < C}` is bounded
            (crude radius `max 2 (C + 1)`).
  OQ02OQ02  sharp two-sided radii; the outer radius is `1 + C^{1/φ(n)}`.
  OQ02OQ03  planar area of the level set squeezed between two discs;
            the outer disc has area `π · (1 + C^{1/φ(n)})²`.
  OQ02OQ04  the outer *radius* `1 + C^{1/φ(n)}` is antitone in the degree `φ(n)`
            and tends to `2` as `φ(n) → ∞`.

`OQ02OQ04` controlled the sharp outer *radius*; this file is the exact *area*
analogue, tracking the area `π · (1 + C^{1/k})²` of that outer confining disc as the
degree exponent `k = φ(n)` grows:

  * `four_pi_le_sharpArea`  — the outer disc always has area `≥ 4π` (a floor: for
                             `C ≥ 1` the radius is `≥ 2`, so the area never dips below
                             that of the disc of radius `2`);
  * `sharpArea_antitone`    — the outer area `π · (1 + C^{1/k})²` is antitone in the
                             degree `k` (higher degree ⟹ smaller-or-equal area);
  * `tendsto_sharpArea`     — it converges to `4π = π · 2²` as `k → ∞`.

Together these say the outer confining disc of every high-degree cyclotomic
lemniscate decreases monotonically to its infimal area `4π`: the region hugs the
unit disc ever more tightly, the antithesis of a Mac Lane labyrinth spreading out to
`∞`.  This is the area-side of the "cyclotomic geometry is tame" picture, sitting on
top of the outer-area bound `volume_levelSet_le` of `OQ02OQ03`.

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ04

open Complex Polynomial Filter Topology

namespace CyclotomicPolynomialsOQ02OQ06

/-- **Floor for the sharp outer area.**
For `C ≥ 1` the sharp outer radius `1 + C^{1/k}` is at least `2` (since `C^{1/k} ≥ 1`),
so the outer disc area `π · (1 + C^{1/k})²` never drops below `4π = π · 2²`, the area
of the disc of radius `2` that the radii converge down to. -/
theorem four_pi_le_sharpArea {C : ℝ} (hC : 1 ≤ C) (k : ℕ) :
    4 * Real.pi ≤ Real.pi * (1 + C ^ ((k : ℝ)⁻¹)) ^ 2 := by
  have h1le : (1 : ℝ) ≤ C ^ ((k : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hC
      (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    simpa using h
  have hrad : (2 : ℝ) ≤ 1 + C ^ ((k : ℝ)⁻¹) := by linarith
  calc 4 * Real.pi = Real.pi * (2 : ℝ) ^ 2 := by ring
    _ ≤ Real.pi * (1 + C ^ ((k : ℝ)⁻¹)) ^ 2 := by gcongr

/-- **Degree-monotonicity of the sharp outer area.**
For `C ≥ 1` and totient exponents `1 ≤ k ≤ k'`, the outer disc area is antitone in the
degree: `π · (1 + C^{1/k'})² ≤ π · (1 + C^{1/k})²`.  This is the area image of the
radius-monotonicity `CyclotomicPolynomialsOQ02OQ04.sharpRadius_antitone` under the
(order-preserving on nonnegatives) map `ρ ↦ π · ρ²`. -/
theorem sharpArea_antitone {C : ℝ} (hC : 1 ≤ C) {k k' : ℕ} (hk : 1 ≤ k)
    (hkk' : k ≤ k') :
    Real.pi * (1 + C ^ ((k' : ℝ)⁻¹)) ^ 2 ≤ Real.pi * (1 + C ^ ((k : ℝ)⁻¹)) ^ 2 := by
  have hrad : 1 + C ^ ((k' : ℝ)⁻¹) ≤ 1 + C ^ ((k : ℝ)⁻¹) :=
    CyclotomicPolynomialsOQ02OQ04.sharpRadius_antitone hC hk hkk'
  have hnn : (0 : ℝ) ≤ 1 + C ^ ((k' : ℝ)⁻¹) := by positivity
  gcongr

/-- **The sharp outer area tends to `4π`.**
For `C > 0`, the outer disc area `π · (1 + C^{1/k})² → 4π = π · 2²` as the degree
`k → ∞`, because the radius `1 + C^{1/k} → 2`
(`CyclotomicPolynomialsOQ02OQ04.tendsto_sharpRadius`) and `ρ ↦ π · ρ²` is continuous.
The outer confining disc of the cyclotomic lemniscate shrinks to its infimal area. -/
theorem tendsto_sharpArea {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ => Real.pi * (1 + C ^ ((k : ℝ)⁻¹)) ^ 2) atTop (𝓝 (4 * Real.pi)) := by
  have hrad := CyclotomicPolynomialsOQ02OQ04.tendsto_sharpRadius hC
  have h2 : Tendsto (fun k : ℕ => Real.pi * (1 + C ^ ((k : ℝ)⁻¹)) ^ 2) atTop
      (𝓝 (Real.pi * (2 : ℝ) ^ 2)) := (hrad.pow 2).const_mul Real.pi
  have he : Real.pi * (2 : ℝ) ^ 2 = 4 * Real.pi := by ring
  rwa [he] at h2

end CyclotomicPolynomialsOQ02OQ06
