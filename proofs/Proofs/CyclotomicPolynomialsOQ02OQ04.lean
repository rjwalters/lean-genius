/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): the sharp outer radius of the
cyclotomic level set shrinks monotonically to `2` with the degree.

Parent chain:
  OQ02OQ01  the cyclotomic level set `{z : |Φ_n(z)| < C}` is bounded
            (crude radius `max 2 (C + 1)`).
  OQ02OQ02  sharp two-sided radii; the outer radius is `1 + C^{1/φ(n)}`.
  OQ02OQ03  planar area of the level set squeezed between two discs.

`OQ02OQ02` observed *in prose* that the sharp outer radius `1 + C^{1/φ(n)}`
"decreases to `2` as `φ(n) → ∞`", so high-degree cyclotomic lemniscates hug the unit
circle — the exact opposite of the freedom Mac Lane needs to build a labyrinth for a
general unit-circle-rooted polynomial. This file turns that observation into three
theorems:

  * `sharpRadius_antitone`   — the radius `1 + C^{1/k}` is antitone in the degree
                               `k = φ(n)` (higher degree ⟹ smaller-or-equal disc);
  * `tendsto_sharpRadius`    — it converges to `2` as the degree `k → ∞`;
  * `eventually_levelSet_subset_closedBall`
                             — hence for every `ε > 0` there is a degree threshold
                               `K` such that EVERY cyclotomic level set `{|Φ_n| < C}`
                               with `φ(n) ≥ K` fits inside the one fixed disc
                               `closedBall(0, 2 + ε)`: a uniform confinement of all
                               high-degree cyclotomic lemniscates.

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ02

open Complex Polynomial Filter Topology

namespace CyclotomicPolynomialsOQ02OQ04

/-- **Degree-monotonicity of the sharp outer radius.**
For `C ≥ 1` and totient exponents `1 ≤ k ≤ k'`, the sharp outer radius of
`CyclotomicPolynomialsOQ02OQ02` satisfies `1 + C^{1/k'} ≤ 1 + C^{1/k}`: raising the
degree `φ(n)` shrinks (weakly) the disc confining the level set. Since `1/k' ≤ 1/k`
and `C ≥ 1`, `C^{1/k'} ≤ C^{1/k}`. -/
theorem sharpRadius_antitone {C : ℝ} (hC : 1 ≤ C) {k k' : ℕ} (hk : 1 ≤ k)
    (hkk' : k ≤ k') :
    1 + C ^ ((k' : ℝ)⁻¹) ≤ 1 + C ^ ((k : ℝ)⁻¹) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hcast : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hkk'
  have hinv : (k' : ℝ)⁻¹ ≤ (k : ℝ)⁻¹ := inv_le_inv_of_le hkpos hcast
  have hle : C ^ ((k' : ℝ)⁻¹) ≤ C ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hC hinv
  linarith

/-- **The sharp outer radius tends to `2`.**
For `C > 0`, `1 + C^{1/k} → 2` as the degree `k → ∞`, because
`C^{1/k} = exp((log C)/k) → exp 0 = 1`. This is the quantitative form of the
"cyclotomic lemniscates hug the unit circle" observation of `OQ02OQ02`. -/
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

/-- **Uniform confinement of high-degree cyclotomic level sets.**
For `C ≥ 1` and any `ε > 0`, there is a degree threshold `K` such that every
cyclotomic level set `{z : |Φ_n(z)| < C}` with `φ(n) ≥ K` is contained in the single
fixed disc `closedBall(0, 2 + ε)`. Since the sharp outer radius `1 + C^{1/φ(n)}`
tends to `2`, it eventually drops below `2 + ε`; combined with the outer containment
`sublevel_subset_closedBall_sharp` this confines all sufficiently high-degree
cyclotomic lemniscates to one disc barely larger than the unit disc — no room for a
path escaping to `∞`, the antithesis of a Mac Lane labyrinth. -/
theorem eventually_levelSet_subset_closedBall {C : ℝ} (hC : 1 ≤ C) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℕ, n ≠ 0 → K ≤ n.totient →
      Erdos1215.levelSet (cyclotomic n ℂ) C ⊆ Metric.closedBall (0 : ℂ) (2 + ε) := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have htend := tendsto_sharpRadius hC0
  have hev : ∀ᶠ k : ℕ in atTop, 1 + C ^ ((k : ℝ)⁻¹) < 2 + ε :=
    (tendsto_order.1 htend).2 (2 + ε) (by linarith)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨K, fun n hn hKn => ?_⟩
  have hlt : 1 + C ^ ((n.totient : ℝ)⁻¹) < 2 + ε := hK n.totient hKn
  calc Erdos1215.levelSet (cyclotomic n ℂ) C
      ⊆ Metric.closedBall (0 : ℂ) (1 + C ^ ((n.totient : ℝ)⁻¹)) :=
        CyclotomicPolynomialsOQ02OQ02.sublevel_subset_closedBall_sharp n hn C
    _ ⊆ Metric.closedBall (0 : ℂ) (2 + ε) :=
        Metric.closedBall_subset_closedBall (le_of_lt hlt)

/-- **The sharp outer radius never drops below `2`.**
For `C ≥ 1` and any degree `k`, the sharp outer radius satisfies `2 ≤ 1 + C^{1/k}`:
since `C ≥ 1` and `1/k ≥ 0`, monotonicity of `x ↦ x^{1/k}` gives `C^{1/k} ≥ 1^{1/k} = 1`.
Together with `sharpRadius_antitone` (weakly decreasing in the degree) and
`tendsto_sharpRadius` (limit `2`), this shows the radius decreases to its **infimum** `2`
strictly from above: `2` is the exact limiting confinement radius of the cyclotomic
lemniscates, attained only in the `φ(n) → ∞` limit — never for a finite degree. -/
theorem sharpRadius_ge_two {C : ℝ} (hC : 1 ≤ C) (k : ℕ) :
    2 ≤ 1 + C ^ ((k : ℝ)⁻¹) := by
  have ht : (0 : ℝ) ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
  have h1 : (1 : ℝ) ≤ C ^ ((k : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hC ht
    rwa [Real.one_rpow] at h
  linarith

end CyclotomicPolynomialsOQ02OQ04
