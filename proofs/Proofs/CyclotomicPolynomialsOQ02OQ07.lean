/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): the sharp *inner* radius of the
cyclotomic level set, and the origin as an interior point.

Parent chain:
  OQ02OQ01  the cyclotomic level set `{z : |Φ_n(z)| < C}` is bounded and open
            (crude outer radius `max 2 (C + 1)`).
  OQ02OQ02  sharp two-sided radii; the outer radius is `1 + C^{1/φ(n)}`, and a ball of
            *any* radius `r` with `(r + 1)^{φ(n)} < C` sits inside the level set.
  OQ02OQ03  planar area of the level set squeezed between two discs.
  OQ02OQ04  the outer *radius* `1 + C^{1/φ(n)}` is antitone in `φ(n)` and tends to `2`.

Everything downstream of `OQ02OQ02` pinned the sharp *outer* radius `1 + C^{1/φ(n)}`
exactly, but the *inner* containment was always stated with an unspecified `r`
subject to the inequality `(r + 1)^{φ(n)} < C`.  This file pins the **sharp inner
radius** to the extremal value `C^{1/φ(n)} - 1` — the largest radius for which the
open ball certainly lies inside `{|Φ_n| < C}` — closing the two-sided *sharp radius*
sandwich to mirror the two-sided *area* sandwich of `OQ02OQ03`:

      ball(0, C^{1/φ(n)} - 1)  ⊆  {|Φ_n| < C}  ⊆  closedBall(0, 1 + C^{1/φ(n)}).

The mechanism: `|Φ_n(0)| = ∏_{μ} ‖0 - μ‖ = ∏_{μ} ‖μ‖ = 1`, so for the Erdős regime
`C > 1` the origin lies (strictly) in the level set, and the elementary upper bound
`|Φ_n(z)| ≤ (‖z‖ + 1)^{φ(n)}` promotes `‖z‖ + 1 < C^{1/φ(n)}` to `|Φ_n(z)| < C`.

Main results:
* `norm_cyclotomic_eval_zero`     : `|Φ_n(0)| = 1`.
* `zero_mem_levelSet`             : for `C > 1`, `0 ∈ {|Φ_n| < C}`.
* `sharpInnerRadius_pos`          : for `C > 1`, the inner radius `C^{1/φ(n)} - 1 > 0`.
* `ball_sharpInner_subset_levelSet` : `ball(0, C^{1/φ(n)} - 1) ⊆ {|Φ_n| < C}`.
* `zero_mem_interior_levelSet`    : the origin is an *interior* point of the level set.
* `sharpRadius_sandwich`          : the two-sided sharp radius sandwich above.
* `sharpInner_area_le_volume`     : `π · (C^{1/φ(n)} - 1)² ≤ area {|Φ_n| < C}` — the
                                    sharp-inner-radius companion to the outer-area
                                    bound `OQ02OQ03.volume_levelSet_le`.

This is the sharp inner-radius / origin-interiority layer of the "cyclotomic geometry
is tame" picture: the level set is a genuine bounded open region with the origin in
its interior at an explicit, degree-controlled distance from its boundary.

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ01
import Proofs.CyclotomicPolynomialsOQ02OQ02

open Complex Polynomial MeasureTheory

namespace CyclotomicPolynomialsOQ02OQ07

/-- **The modulus of a cyclotomic polynomial at the origin is `1`.**
Since `Φ_n` factors as `∏_{μ}(X - μ)` over the primitive `n`-th roots of unity, all of
which have `‖μ‖ = 1`, we get `|Φ_n(0)| = ∏_{μ} ‖0 - μ‖ = ∏_{μ} ‖μ‖ = 1`.  (Equivalently
`Φ_n(0) = ±1`.)  This is the geometric reason the origin lies inside every level set
`{|Φ_n| < C}` with `C > 1`. -/
lemma norm_cyclotomic_eval_zero (n : ℕ) (hn : n ≠ 0) :
    ‖(cyclotomic n ℂ).eval 0‖ = 1 := by
  rw [CyclotomicPolynomialsOQ02OQ01.norm_cyclotomic_eval n hn 0]
  apply Finset.prod_eq_one
  intro μ hμ
  have hμ' : IsPrimitiveRoot μ n := (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).1 hμ
  have hnorm : ‖μ‖ = 1 := hμ'.norm'_eq_one hn
  rw [zero_sub, norm_neg, hnorm]

/-- **The origin lies in the level set for `C > 1`.**
Immediate from `|Φ_n(0)| = 1 < C`.  This is exactly the Erdős regime `C > 1` of
problem #1215; for `C ≤ 1` the origin is on or outside the boundary. -/
theorem zero_mem_levelSet (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    (0 : ℂ) ∈ Erdos1215.levelSet (cyclotomic n ℂ) C := by
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq, norm_cyclotomic_eval_zero n hn]
  exact hC

/-- **The sharp inner radius is positive.**
For `C > 1`, `C^{1/φ(n)} > 1` (raising `C > 1` to the positive power `1/φ(n)`), so the
inner radius `C^{1/φ(n)} - 1` is strictly positive: the origin sits a genuine positive
distance inside the level set. -/
theorem sharpInnerRadius_pos (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    0 < C ^ ((n.totient : ℝ)⁻¹) - 1 := by
  have hk0 : n.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have hkpos : (0 : ℝ) < (n.totient : ℝ)⁻¹ := by
    apply inv_pos.mpr; exact_mod_cast Nat.pos_of_ne_zero hk0
  have h1lt : (1 : ℝ) < C ^ ((n.totient : ℝ)⁻¹) := by
    have h2 : (1 : ℝ) ^ ((n.totient : ℝ)⁻¹) < C ^ ((n.totient : ℝ)⁻¹) :=
      Real.rpow_lt_rpow (by norm_num) hC hkpos
    rwa [Real.one_rpow] at h2
  linarith

/-- **Sharp inner-radius containment.**
For `C > 1`, the open ball of the *sharp* inner radius `C^{1/φ(n)} - 1` about the origin
lies inside the cyclotomic level set `{|Φ_n| < C}`.  If `‖z‖ < C^{1/φ(n)} - 1` then
`‖z‖ + 1 < C^{1/φ(n)}`, so `(‖z‖ + 1)^{φ(n)} < (C^{1/φ(n)})^{φ(n)} = C`, and the upper
bound `|Φ_n(z)| ≤ (‖z‖ + 1)^{φ(n)}` of `OQ02OQ02` gives `|Φ_n(z)| < C`.  This is the
extremal case of `OQ02OQ02.closedBall_subset_levelSet_cyclotomic`, pinning its free
radius `r` to the largest admissible value. -/
theorem ball_sharpInner_subset_levelSet (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    Metric.ball (0 : ℂ) (C ^ ((n.totient : ℝ)⁻¹) - 1) ⊆
      Erdos1215.levelSet (cyclotomic n ℂ) C := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hC0 : (0 : ℝ) < C := lt_trans one_pos hC
  have hk0 : n.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have hb : ‖z‖ + 1 < C ^ ((n.totient : ℝ)⁻¹) := by linarith
  have hbnn : (0 : ℝ) ≤ ‖z‖ + 1 := by positivity
  have hpow : (‖z‖ + 1) ^ n.totient < (C ^ ((n.totient : ℝ)⁻¹)) ^ n.totient :=
    pow_lt_pow_left₀ hb hbnn hk0
  have heq : (C ^ ((n.totient : ℝ)⁻¹)) ^ n.totient = C :=
    Real.rpow_inv_natCast_pow hC0.le hk0
  rw [heq] at hpow
  exact CyclotomicPolynomialsOQ02OQ02.mem_levelSet_of_norm_add_one_pow_lt n hn C z hpow

/-- **The origin is an interior point of the level set.**
For `C > 1`, the level set `{|Φ_n| < C}` is open (`OQ02OQ01`) and contains `0`, so `0`
lies in its interior.  Concretely, the sharp inner ball
`ball(0, C^{1/φ(n)} - 1)` of positive radius is an explicit open neighbourhood of the
origin inside the level set. -/
theorem zero_mem_interior_levelSet (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    (0 : ℂ) ∈ interior (Erdos1215.levelSet (cyclotomic n ℂ) C) := by
  rw [(CyclotomicPolynomialsOQ02OQ01.isOpen_levelSet_cyclotomic n C).interior_eq]
  exact zero_mem_levelSet n hn hC

/-- **The two-sided sharp radius sandwich.**
For `C > 1`, the cyclotomic level set is trapped between the open inner disc of the
sharp radius `C^{1/φ(n)} - 1` and the closed outer disc of the sharp radius
`1 + C^{1/φ(n)}`:

      ball(0, C^{1/φ(n)} - 1)  ⊆  {|Φ_n| < C}  ⊆  closedBall(0, 1 + C^{1/φ(n)}).

This is the radius-level analogue of the area sandwich `OQ02OQ03.volume_levelSet_sandwich`,
now with *both* radii pinned to their sharp cyclotomic values (the inner bound of
`OQ02OQ03` carried a free radius `r`). -/
theorem sharpRadius_sandwich (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    Metric.ball (0 : ℂ) (C ^ ((n.totient : ℝ)⁻¹) - 1) ⊆
        Erdos1215.levelSet (cyclotomic n ℂ) C ∧
      Erdos1215.levelSet (cyclotomic n ℂ) C ⊆
        Metric.closedBall (0 : ℂ) (1 + C ^ ((n.totient : ℝ)⁻¹)) :=
  ⟨ball_sharpInner_subset_levelSet n hn hC,
    CyclotomicPolynomialsOQ02OQ02.sublevel_subset_closedBall_sharp n hn C⟩

/-- **Sharp inner-radius area bound.**
For `C > 1`, the planar Lebesgue measure of the cyclotomic level set is at least the
area `π · (C^{1/φ(n)} - 1)²` of the sharp inner disc.  This is the sharp-inner-radius
companion to the outer-area bound `OQ02OQ03.volume_levelSet_le`, and — unlike the
free-radius lower bound `OQ02OQ03.le_volume_levelSet` — is stated at the extremal inner
radius, so together with the outer bound it squeezes the area between the two sharp
disc areas `π·(C^{1/φ(n)} - 1)²` and `π·(1 + C^{1/φ(n)})²`. -/
theorem sharpInner_area_le_volume (n : ℕ) (hn : n ≠ 0) {C : ℝ} (hC : 1 < C) :
    ENNReal.ofReal (C ^ ((n.totient : ℝ)⁻¹) - 1) ^ 2 * NNReal.pi ≤
      volume (Erdos1215.levelSet (cyclotomic n ℂ) C) := by
  calc ENNReal.ofReal (C ^ ((n.totient : ℝ)⁻¹) - 1) ^ 2 * NNReal.pi
      = volume (Metric.ball (0 : ℂ) (C ^ ((n.totient : ℝ)⁻¹) - 1)) :=
        (Complex.volume_ball _ _).symm
    _ ≤ volume (Erdos1215.levelSet (cyclotomic n ℂ) C) :=
        measure_mono (ball_sharpInner_subset_levelSet n hn hC)

end CyclotomicPolynomialsOQ02OQ07
