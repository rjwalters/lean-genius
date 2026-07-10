/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): geometry of cyclotomic level sets.

Parent: `Proofs.Erdos1215Problem` asks whether, for polynomials `P` with all roots
on the unit circle, there is a bounded-level path from `0` to `∞` inside
`{z : |P(z)| < C}`.  OQ-02 restricts attention to the *cyclotomic* polynomials
`Φ_n`, whose roots are exactly the primitive `n`-th roots of unity, and asks for a
polynomial path-length bound.

This file establishes the fundamental structural fact underlying any such bound:
**the cyclotomic lemniscate `{z : |Φ_n(z)| < C}` is bounded** (indeed compact),
with an explicit radius.  The mechanism is that every root of `Φ_n` lies on the
unit circle, so for `‖z‖` large the modulus `|Φ_n(z)| = ∏ ‖z - μ‖ ≥ (‖z‖ - 1)^{φ(n)}`
grows without bound.  As an immediate consequence, no continuous path escaping to
infinity can remain in the sublevel set: for cyclotomic polynomials the path
obstruction is *unconditional* (it holds for every threshold `C`, not just `C > 1`).

We also record the exact geometry of the smallest cases `n = 1, 2`, where the
level-`1` set is a genuine open disk.

Main results:
* `norm_cyclotomic_eval`      : `|Φ_n(z)| = ∏_{μ prim} ‖z - μ‖`.
* `pow_sub_one_le_norm_cyclotomic_eval` : `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)|` for `‖z‖ ≥ 1`.
* `cyclotomic_sublevel_norm_lt`         : `|Φ_n(z)| < C ⟹ ‖z‖ < max 2 (C+1)`.
* `isBounded_levelSet_cyclotomic`       : the level set is a bounded subset of `ℂ`.
* `not_hasBoundedLevelPath_cyclotomic`  : no escape-to-∞ path stays in the level set.
* `sublevel_one`, `sublevel_two`        : exact open-disk description for `n = 1, 2`.

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib
import Proofs.Erdos1215Problem

open Complex Polynomial

namespace CyclotomicPolynomialsOQ02OQ01

/-- **Product formula for the modulus of a cyclotomic polynomial.**
For `n ≥ 1`, `|Φ_n(z)|` is the product of the distances from `z` to the primitive
`n`-th roots of unity. -/
lemma norm_cyclotomic_eval (n : ℕ) (hn : n ≠ 0) (z : ℂ) :
    ‖(cyclotomic n ℂ).eval z‖ = ∏ μ ∈ primitiveRoots n ℂ, ‖z - μ‖ := by
  have hζ := isPrimitiveRoot_exp n hn
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ]
  simp only [eval_prod, eval_sub, eval_X, eval_C, norm_prod]

/-- **Lower bound on `|Φ_n(z)|` outside the closed unit disk.**
For `n ≥ 1` and `‖z‖ ≥ 1`, we have `(‖z‖ - 1)^{φ(n)} ≤ |Φ_n(z)|`, because each
primitive root `μ` has `‖μ‖ = 1`, so `‖z - μ‖ ≥ ‖z‖ - 1`. -/
lemma pow_sub_one_le_norm_cyclotomic_eval (n : ℕ) (hn : n ≠ 0) (z : ℂ)
    (hz : 1 ≤ ‖z‖) :
    (‖z‖ - 1) ^ n.totient ≤ ‖(cyclotomic n ℂ).eval z‖ := by
  rw [norm_cyclotomic_eval n hn z]
  have hcard : (primitiveRoots n ℂ).card = n.totient := card_primitiveRoots n
  calc (‖z‖ - 1) ^ n.totient
      = (‖z‖ - 1) ^ (primitiveRoots n ℂ).card := by rw [hcard]
    _ = ∏ _μ ∈ primitiveRoots n ℂ, (‖z‖ - 1) := by rw [Finset.prod_const]
    _ ≤ ∏ μ ∈ primitiveRoots n ℂ, ‖z - μ‖ := by
        apply Finset.prod_le_prod
        · intro μ _; linarith
        · intro μ hμ
          have hμ' : IsPrimitiveRoot μ n :=
            (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).1 hμ
          have hnorm : ‖μ‖ = 1 := hμ'.norm'_eq_one hn
          have hb : ‖z‖ - ‖μ‖ ≤ ‖z - μ‖ := norm_sub_norm_le z μ
          rw [hnorm] at hb
          linarith

/-- **The cyclotomic lemniscate is bounded (pointwise form).**
For `n ≥ 1` and any threshold `C`, every point of the sublevel set
`{z : |Φ_n(z)| < C}` satisfies `‖z‖ < max 2 (C + 1)`. -/
theorem cyclotomic_sublevel_norm_lt (n : ℕ) (hn : n ≠ 0) (C : ℝ) (z : ℂ)
    (hz : ‖(cyclotomic n ℂ).eval z‖ < C) : ‖z‖ < max 2 (C + 1) := by
  by_cases h2 : ‖z‖ < 2
  · exact lt_of_lt_of_le h2 (le_max_left _ _)
  · push_neg at h2
    have h1 : (1 : ℝ) ≤ ‖z‖ := by linarith
    have hb1 : (1 : ℝ) ≤ ‖z‖ - 1 := by linarith
    have hφ : n.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    have hlow := pow_sub_one_le_norm_cyclotomic_eval n hn z h1
    have hself : (‖z‖ - 1) ≤ (‖z‖ - 1) ^ n.totient := le_self_pow₀ hb1 hφ
    have hlt : ‖z‖ - 1 < C := lt_of_le_of_lt (hself.trans hlow) hz
    have : ‖z‖ < C + 1 := by linarith
    exact lt_of_lt_of_le this (le_max_right _ _)

/-- **The cyclotomic level set is a bounded subset of `ℂ`.**
It is contained in the closed ball of radius `max 2 (C + 1)` about the origin. -/
theorem isBounded_levelSet_cyclotomic (n : ℕ) (hn : n ≠ 0) (C : ℝ) :
    Bornology.IsBounded (Erdos1215.levelSet (cyclotomic n ℂ) C) := by
  have hsub : Erdos1215.levelSet (cyclotomic n ℂ) C ⊆
      Metric.closedBall (0 : ℂ) (max 2 (C + 1)) := by
    intro z hz
    simp only [Erdos1215.levelSet, Set.mem_setOf_eq] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (cyclotomic_sublevel_norm_lt n hn C z hz)
  exact Metric.isBounded_closedBall.subset hsub

/-- **No escape-to-infinity path for cyclotomic polynomials.**
Because the level set is bounded, no continuous path from `0` with `‖γ t‖ → ∞`
can stay inside `{z : |Φ_n(z)| < C}`.  This is the cyclotomic specialisation of the
Erdős #1215 path problem: for `Φ_n` the obstruction holds for *every* threshold `C`
(not merely `C > 1`), since the level sets are compact. -/
theorem not_hasBoundedLevelPath_cyclotomic (n : ℕ) (hn : n ≠ 0) (C : ℝ) :
    ¬ Erdos1215.HasBoundedLevelPath (cyclotomic n ℂ) C := by
  rintro ⟨γ, _hcont, _h0, htend, hmem⟩
  set R := max 2 (C + 1) with hR
  have hev : ∀ᶠ t in Filter.atTop, R < ‖γ t‖ := htend.eventually_gt_atTop R
  have hev0 : ∀ᶠ t in Filter.atTop, (0 : ℝ) ≤ t := Filter.eventually_ge_atTop 0
  obtain ⟨t, htR, ht0⟩ := (hev.and hev0).exists
  have hmem' : ‖(cyclotomic n ℂ).eval (γ t)‖ < C := by
    have := hmem t ht0
    simpa only [Erdos1215.levelSet, Set.mem_setOf_eq] using this
  have hlt : ‖γ t‖ < R := cyclotomic_sublevel_norm_lt n hn C (γ t) hmem'
  linarith

/-- **`n = 1`:** the level-`1` set `{|Φ₁(z)| < 1}` is exactly the open unit disk
centred at `1` (since `Φ₁ = X - 1`). -/
theorem sublevel_one :
    {z : ℂ | ‖(cyclotomic 1 ℂ).eval z‖ < 1} = Metric.ball (1 : ℂ) 1 := by
  ext z
  simp only [cyclotomic_one, eval_sub, eval_X, eval_one, Set.mem_setOf_eq,
    Metric.mem_ball, dist_eq_norm]

/-- **`n = 2`:** the level-`1` set `{|Φ₂(z)| < 1}` is exactly the open unit disk
centred at `-1` (since `Φ₂ = X + 1`). -/
theorem sublevel_two :
    {z : ℂ | ‖(cyclotomic 2 ℂ).eval z‖ < 1} = Metric.ball (-1 : ℂ) 1 := by
  ext z
  simp only [cyclotomic_two, eval_add, eval_X, eval_one, Set.mem_setOf_eq,
    Metric.mem_ball, dist_eq_norm, sub_neg_eq_add]

end CyclotomicPolynomialsOQ02OQ01
