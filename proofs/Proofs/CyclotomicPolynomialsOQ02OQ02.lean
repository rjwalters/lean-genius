/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): sharp two-sided radii of the
cyclotomic level set.

Parent: `Proofs.Erdos1215Problem` asks whether, for polynomials `P` with all roots
on the unit circle, there is a bounded-level path from `0` to `∞` inside
`{z : |P(z)| < C}`.  OQ-02 restricts to the *cyclotomic* polynomials `Φ_n`.

The companion `CyclotomicPolynomialsOQ02OQ01` proved the qualitative fact that the
cyclotomic level set `{z : |Φ_n(z)| < C}` is bounded, contained in the ball of the
crude radius `max 2 (C + 1)`.  This entry **sharpens the outer radius to
`1 + C^{1/φ(n)}`** and supplies the complementary **inner containment**, pinning the
level set between two concentric balls about the origin:

      { z : ‖z‖ + 1 < C^{1/φ(n)} }  ⊆  {|Φ_n(z)| < C}  ⊆  closedBall(0, 1 + C^{1/φ(n)}).

The mechanism is the elementary two-sided factor bound `‖z‖ - 1 ≤ ‖z - μ‖ ≤ ‖z‖ + 1`
on each primitive-root factor (`‖μ‖ = 1`), giving

      (‖z‖ - 1)^{φ(n)} ≤ |Φ_n(z)| ≤ (‖z‖ + 1)^{φ(n)}.

Quantitatively the sharp outer radius `1 + C^{1/φ(n)}` is a genuine improvement over
`max 2 (C + 1)`: for a fixed threshold `C > 1` it decreases to `2` as the degree
`φ(n) → ∞`, so high-degree cyclotomic lemniscates hug the unit circle — the exact
opposite of the freedom Mac Lane needs to build a labyrinth for arbitrary
unit-circle-rooted polynomials.

Main results:
* `norm_cyclotomic_eval_le`              : `|Φ_n(z)| ≤ (‖z‖ + 1)^{φ(n)}`.
* `mem_levelSet_of_norm_add_one_pow_lt`  : `(‖z‖+1)^{φ(n)} < C ⟹ z ∈ {|Φ_n| < C}`.
* `closedBall_subset_levelSet_cyclotomic`: inner ball contained in the level set.
* `cyclotomic_sublevel_norm_lt_sharp`    : `|Φ_n(z)| < C ⟹ ‖z‖ < 1 + C^{1/φ(n)}`.
* `sublevel_subset_closedBall_sharp`     : level set ⊆ `closedBall(0, 1 + C^{1/φ(n)})`.
* `sharp_radius_le_crude`                : `1 + C^{1/φ(n)} ≤ max 2 (C + 1)` (it really
                                           is a sharpening of the OQ-01 radius).

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ01

open Complex Polynomial

namespace CyclotomicPolynomialsOQ02OQ02

/-- **Upper bound on `|Φ_n(z)|`.**
For `n ≥ 1`, `|Φ_n(z)| ≤ (‖z‖ + 1)^{φ(n)}`, because each primitive root `μ` has
`‖μ‖ = 1`, so `‖z - μ‖ ≤ ‖z‖ + 1`.  This is the mirror image of the OQ-01 lower
bound `(‖z‖ - 1)^{φ(n)} ≤ |Φ_n(z)|`. -/
lemma norm_cyclotomic_eval_le (n : ℕ) (hn : n ≠ 0) (z : ℂ) :
    ‖(cyclotomic n ℂ).eval z‖ ≤ (‖z‖ + 1) ^ n.totient := by
  rw [CyclotomicPolynomialsOQ02OQ01.norm_cyclotomic_eval n hn z]
  have hcard : (primitiveRoots n ℂ).card = n.totient := card_primitiveRoots n
  calc ∏ μ ∈ primitiveRoots n ℂ, ‖z - μ‖
      ≤ ∏ _μ ∈ primitiveRoots n ℂ, (‖z‖ + 1) := by
        apply Finset.prod_le_prod
        · intro μ _; positivity
        · intro μ hμ
          have hμ' : IsPrimitiveRoot μ n :=
            (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).1 hμ
          have hnorm : ‖μ‖ = 1 := hμ'.norm'_eq_one hn
          calc ‖z - μ‖ ≤ ‖z‖ + ‖μ‖ := norm_sub_le z μ
            _ = ‖z‖ + 1 := by rw [hnorm]
    _ = (‖z‖ + 1) ^ (primitiveRoots n ℂ).card := by rw [Finset.prod_const]
    _ = (‖z‖ + 1) ^ n.totient := by rw [hcard]

/-! ### Inner containment: a ball inside the level set -/

/-- **Sufficient condition for level-set membership.**
If `(‖z‖ + 1)^{φ(n)} < C` then `z` lies in `{|Φ_n| < C}`.  Directly from the upper
bound. -/
theorem mem_levelSet_of_norm_add_one_pow_lt (n : ℕ) (hn : n ≠ 0) (C : ℝ) (z : ℂ)
    (hz : (‖z‖ + 1) ^ n.totient < C) :
    z ∈ Erdos1215.levelSet (cyclotomic n ℂ) C := by
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq]
  exact lt_of_le_of_lt (norm_cyclotomic_eval_le n hn z) hz

/-- **Inner ball containment.**
For a radius `r ≥ 0` with `(r + 1)^{φ(n)} < C`, the entire closed ball of radius `r`
about the origin lies inside the cyclotomic level set `{|Φ_n| < C}`.  Together with the
outer bound below, this sandwiches the level set between concentric balls. -/
theorem closedBall_subset_levelSet_cyclotomic (n : ℕ) (hn : n ≠ 0) (C r : ℝ)
    (hr0 : 0 ≤ r) (hr : (r + 1) ^ n.totient < C) :
    Metric.closedBall (0 : ℂ) r ⊆ Erdos1215.levelSet (cyclotomic n ℂ) C := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  apply mem_levelSet_of_norm_add_one_pow_lt n hn C z
  have hmono : (‖z‖ + 1) ^ n.totient ≤ (r + 1) ^ n.totient :=
    pow_le_pow_left₀ (by positivity) (by linarith) n.totient
  linarith

/-! ### Sharp outer radius `1 + C^{1/φ(n)}` -/

/-- **Sharp pointwise bound.**
For `n ≥ 1`, every point of the level set satisfies `‖z‖ < 1 + C^{1/φ(n)}`.
This sharpens `CyclotomicPolynomialsOQ02OQ01.cyclotomic_sublevel_norm_lt`
(radius `max 2 (C + 1)`): taking `φ(n)`-th roots of the lower bound
`(‖z‖ - 1)^{φ(n)} ≤ |Φ_n(z)| < C` gives `‖z‖ - 1 < C^{1/φ(n)}`. -/
theorem cyclotomic_sublevel_norm_lt_sharp (n : ℕ) (hn : n ≠ 0) (C : ℝ) (z : ℂ)
    (hz : ‖(cyclotomic n ℂ).eval z‖ < C) :
    ‖z‖ < 1 + C ^ ((n.totient : ℝ)⁻¹) := by
  have hC : 0 < C := lt_of_le_of_lt (norm_nonneg _) hz
  have hk0 : n.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have hkpos : (0 : ℝ) < (n.totient : ℝ)⁻¹ := by
    apply inv_pos.mpr; exact_mod_cast Nat.pos_of_ne_zero hk0
  have hCr : 0 < C ^ ((n.totient : ℝ)⁻¹) := Real.rpow_pos_of_pos hC _
  by_cases h1 : ‖z‖ < 1
  · linarith
  · push_neg at h1
    have ha : (0 : ℝ) ≤ ‖z‖ - 1 := by linarith
    have hlow :=
      CyclotomicPolynomialsOQ02OQ01.pow_sub_one_le_norm_cyclotomic_eval n hn z h1
    have hak : (‖z‖ - 1) ^ n.totient < C := lt_of_le_of_lt hlow hz
    have hmono : ((‖z‖ - 1) ^ n.totient) ^ ((n.totient : ℝ)⁻¹)
        < C ^ ((n.totient : ℝ)⁻¹) :=
      Real.rpow_lt_rpow (pow_nonneg ha _) hak hkpos
    rw [Real.pow_rpow_inv_natCast ha hk0] at hmono
    linarith

/-- **Sharp level-set containment.**
The cyclotomic level set `{|Φ_n| < C}` is contained in the closed ball of the sharp
radius `1 + C^{1/φ(n)}` about the origin. -/
theorem sublevel_subset_closedBall_sharp (n : ℕ) (hn : n ≠ 0) (C : ℝ) :
    Erdos1215.levelSet (cyclotomic n ℂ) C ⊆
      Metric.closedBall (0 : ℂ) (1 + C ^ ((n.totient : ℝ)⁻¹)) := by
  intro z hz
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (cyclotomic_sublevel_norm_lt_sharp n hn C z hz)

/-- **The sharp radius really is a sharpening.**
For `C ≥ 1` and `n ≥ 1`, the sharp radius `1 + C^{1/φ(n)}` never exceeds the crude
OQ-01 radius `max 2 (C + 1)`.  (Since `1/φ(n) ≤ 1`, we have `C^{1/φ(n)} ≤ C`, whence
`1 + C^{1/φ(n)} ≤ 1 + C = C + 1 ≤ max 2 (C + 1)`.) -/
theorem sharp_radius_le_crude (n : ℕ) (hn : n ≠ 0) (C : ℝ) (hC : 1 ≤ C) :
    1 + C ^ ((n.totient : ℝ)⁻¹) ≤ max 2 (C + 1) := by
  have hk0 : n.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have hone_le : (1 : ℝ) ≤ (n.totient : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hinv_le_one : (n.totient : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hone_le
  have hle : C ^ ((n.totient : ℝ)⁻¹) ≤ C ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hC hinv_le_one
  rw [Real.rpow_one] at hle
  calc 1 + C ^ ((n.totient : ℝ)⁻¹) ≤ 1 + C := by linarith
    _ = C + 1 := by ring
    _ ≤ max 2 (C + 1) := le_max_right _ _

end CyclotomicPolynomialsOQ02OQ02
