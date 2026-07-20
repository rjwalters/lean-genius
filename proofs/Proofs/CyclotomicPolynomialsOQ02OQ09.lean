/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): the far field of a cyclotomic
level set is a single connected escape region.

Prior OQ-02 layers (see OQ02OQ01…OQ02OQ07) pinned the *metric* geometry of the sublevel
set `{z : |Φ_n(z)| < C}`: it is open, bounded, and sandwiched between concentric balls,

      ball(0, C^{1/φ(n)} - 1)  ⊆  {|Φ_n| < C}  ⊆  closedBall(0, 1 + C^{1/φ(n)}).

Those bounds constrain *where* the "cyclotomic labyrinth" can live but say nothing about
its *topology* — the genuinely open Mac Lane driver is the number of connected components
of the level set, which Mathlib's analysis library cannot yet reach (no polynomial-
lemniscate topology / rectifiable arc length).

This file records the one topological fact that *is* reachable with the existing sharp
outer radius: however intricate the bounded sublevel labyrinth is, the complementary far
field is a **single connected unbounded escape region**.  Concretely, the exterior of the
sharp outer ball,

      { z : 1 + C^{1/φ(n)} < ‖z‖ },

(i)  lies entirely inside the closed superlevel set `{ z : C ≤ |Φ_n(z)| }` (contrapositive
     of the sharp outer-radius bound `OQ02OQ02.cyclotomic_sublevel_norm_lt_sharp`), and
(ii) is itself path-connected and unbounded.

So the superlevel set `{ |Φ_n| ≥ C }` always contains a path-connected unbounded piece:
there is exactly one way to "escape to infinity", regardless of `n` or `C`.  This is the
topological complement of the metric confinement proved in the earlier layers, and it is
orthogonal to the radius/area/monotonicity companions.

## Main results
* `isPathConnected_norm_gt`            : (general, reusable) the exterior `{z : ℂ | R < ‖z‖}`
                                         of a closed ball is path-connected — it is the
                                         continuous image of the punctured plane `{0}ᶜ`
                                         (path-connected since `dim_ℝ ℂ = 2 > 1`) under the
                                         radial rescaling `w ↦ (R + ‖w‖)‖w‖⁻¹ • w`.
* `not_isBounded_norm_gt`              : that exterior is unbounded.
* `exterior_subset_cyclotomic_superlevel` : `{1 + C^{1/φ(n)} < ‖z‖} ⊆ {C ≤ |Φ_n(z)|}`.
* `cyclotomic_superlevel_exterior_isPathConnected` : the escape region
                                         `{1 + C^{1/φ(n)} < ‖z‖}` is path-connected.
* `cyclotomic_superlevel_has_connected_unbounded_subset` : the cyclotomic superlevel set
                                         `{C ≤ |Φ_n(z)|}` contains a path-connected,
                                         unbounded subset — a single connected far field.
-/
import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ01
import Proofs.CyclotomicPolynomialsOQ02OQ02

open Metric Set Polynomial

namespace CyclotomicPolynomialsOQ02OQ09

/-- **The exterior of a closed ball in `ℂ` is path-connected.**
For any radius `R ≥ 0`, the set `{z : ℂ | R < ‖z‖}` is path-connected.  It is the
continuous image of the punctured plane `{0}ᶜ` — which is path-connected because `ℂ` has
real dimension `2 > 1` — under the radial rescaling `w ↦ (R + ‖w‖)‖w‖⁻¹ • w`, a
homeomorphism-onto-image that sends the direction of `w` to the same direction at radius
`R + ‖w‖ ∈ (R, ∞)`.  This is the reusable topological core behind the "single connected
escape region" of any polynomial superlevel set. -/
theorem isPathConnected_norm_gt (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {z : ℂ | R < ‖z‖} := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ :=
    Complex.rank_real_complex ▸ Nat.one_lt_ofNat
  have hcompl : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  set f : ℂ → ℂ := fun w => ((R + ‖w‖) * ‖w‖⁻¹) • w with hf_def
  have hcont : ContinuousOn f {0}ᶜ := by
    apply ContinuousOn.smul _ continuousOn_id
    apply ContinuousOn.mul (by fun_prop)
    intro w hw
    exact (continuousOn_id.norm.inv₀ (fun x hx => norm_ne_zero_iff.2 hx)) w hw
  have himg : f '' ({0}ᶜ : Set ℂ) = {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [mem_compl_iff, mem_singleton_iff] at hw
      have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
      simp only [hf_def, mem_setOf_eq, norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [mul_assoc, inv_mul_cancel₀ hwpos.ne', mul_one]
      linarith
    · intro hz
      simp only [mem_setOf_eq] at hz
      have hzpos : (0 : ℝ) < ‖z‖ := lt_of_le_of_lt hR hz
      have hzne : z ≠ 0 := norm_pos_iff.1 hzpos
      refine ⟨((‖z‖ - R) * ‖z‖⁻¹) • z, ?_, ?_⟩
      · simp only [mem_compl_iff, mem_singleton_iff]
        exact smul_ne_zero (mul_ne_zero (sub_ne_zero.2 hz.ne') (inv_ne_zero hzpos.ne')) hzne
      · have hwn : ‖((‖z‖ - R) * ‖z‖⁻¹) • z‖ = ‖z‖ - R := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          field_simp
        have h1 : ‖z‖ - R ≠ 0 := sub_ne_zero.2 hz.ne'
        have h2 : ‖z‖ ≠ 0 := hzpos.ne'
        simp only [hf_def]
        rw [hwn, smul_smul, show R + (‖z‖ - R) = ‖z‖ by ring]
        rw [show ‖z‖ * (‖z‖ - R)⁻¹ * ((‖z‖ - R) * ‖z‖⁻¹) = 1 by field_simp, one_smul]
  rw [← himg]
  exact hcompl.image' hcont

/-- **The exterior of a closed ball is unbounded.**
The set `{z : ℂ | R < ‖z‖}` contains points of arbitrarily large norm, so it is not
bounded. -/
theorem not_isBounded_norm_gt (R : ℝ) : ¬ Bornology.IsBounded {z : ℂ | R < ‖z‖} := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
  rintro ⟨r, hr⟩
  -- pick a real point with nonnegative value exceeding both `R` and `r`
  set M : ℝ := |R| + |r| + 1 with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hMR : R < M := by rw [hM]; have := le_abs_self R; have := abs_nonneg r; linarith
  have hMr : r < M := by rw [hM]; have := le_abs_self r; have := abs_nonneg R; linarith
  have hmem : (M : ℂ) ∈ {z : ℂ | R < ‖z‖} := by
    simp only [mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hM0]; exact hMR
  have := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hM0] at this
  linarith

/-- **The far field lies in the closed superlevel set.**
Beyond the sharp outer radius `1 + C^{1/φ(n)}` the cyclotomic modulus is at least `C`:
this is the contrapositive of the sharp outer-radius bound
`OQ02OQ02.cyclotomic_sublevel_norm_lt_sharp` (`|Φ_n(z)| < C ⟹ ‖z‖ < 1 + C^{1/φ(n)}`). -/
theorem exterior_subset_cyclotomic_superlevel (n : ℕ) (hn : n ≠ 0) (C : ℝ) :
    {z : ℂ | 1 + C ^ ((n.totient : ℝ)⁻¹) < ‖z‖} ⊆
      {z : ℂ | C ≤ ‖(cyclotomic n ℂ).eval z‖} := by
  intro z hz
  simp only [mem_setOf_eq] at hz ⊢
  rw [← not_lt]
  intro h
  exact absurd (CyclotomicPolynomialsOQ02OQ02.cyclotomic_sublevel_norm_lt_sharp n hn C z h)
    (not_lt.2 hz.le)

/-- **The escape region is path-connected.**
For `C > 0` the exterior of the sharp outer ball, `{ z : 1 + C^{1/φ(n)} < ‖z‖ }`, is
path-connected (the radius `1 + C^{1/φ(n)}` is positive, so `isPathConnected_norm_gt`
applies). -/
theorem cyclotomic_superlevel_exterior_isPathConnected (n : ℕ) {C : ℝ} (hC : 0 < C) :
    IsPathConnected {z : ℂ | 1 + C ^ ((n.totient : ℝ)⁻¹) < ‖z‖} := by
  apply isPathConnected_norm_gt
  have : (0 : ℝ) < C ^ ((n.totient : ℝ)⁻¹) := Real.rpow_pos_of_pos hC _
  linarith

/-- **The cyclotomic superlevel set has a single connected unbounded escape region.**
For `n ≥ 1` and `C > 0`, the closed superlevel set `{ z : C ≤ |Φ_n(z)| }` contains a
subset that is simultaneously path-connected and unbounded — namely the exterior
`{ z : 1 + C^{1/φ(n)} < ‖z‖ }` of the sharp outer ball.  However intricate the bounded
sublevel "cyclotomic labyrinth" `{|Φ_n| < C}` is, there is exactly one connected way to
escape to infinity. -/
theorem cyclotomic_superlevel_has_connected_unbounded_subset
    (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 0 < C) :
    ∃ S : Set ℂ, S ⊆ {z : ℂ | C ≤ ‖(cyclotomic n ℂ).eval z‖} ∧
      IsPathConnected S ∧ ¬ Bornology.IsBounded S := by
  refine ⟨{z : ℂ | 1 + C ^ ((n.totient : ℝ)⁻¹) < ‖z‖}, ?_, ?_, ?_⟩
  · exact exterior_subset_cyclotomic_superlevel n hn C
  · exact cyclotomic_superlevel_exterior_isPathConnected n hC
  · exact not_isBounded_norm_gt _

end CyclotomicPolynomialsOQ02OQ09

-- Axiom audit (verified 0-axiom: [propext, Classical.choice, Quot.sound]; uncomment to re-check)
-- #print axioms CyclotomicPolynomialsOQ02OQ09.cyclotomic_superlevel_has_connected_unbounded_subset
-- #print axioms CyclotomicPolynomialsOQ02OQ09.isPathConnected_norm_gt
