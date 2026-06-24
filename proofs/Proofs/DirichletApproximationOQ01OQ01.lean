/-
# Dirichlet Approximation — OQ-01-OQ-01: Optimality of the Hurwitz Constant √5

**Open Question (sharpening the approximation constant).** The parent entry
`DirichletApproximationOQ01` upgrades Dirichlet's one-shot bound to the
*infinitude* statement: every irrational `α` has infinitely many rationals
`p/q` in lowest terms with `|α − p/q| < 1/q²`. Hurwitz's theorem sharpens the
constant from `1` to `1/√5`:

> every irrational `α` has infinitely many `p/q` with `|α − p/q| < 1/(√5·q²)`,
> and the constant `√5` is **best possible** — it cannot be replaced by any
> larger constant.

This file formalizes the **optimality half** (the sharpness direction), which
is the genuinely new content: it is *not* in Mathlib (Mathlib has Dirichlet's
theorem with constant `1`, plus Legendre's theorem and continued fractions,
but no Hurwitz bound and no optimality statement). The *existence* half of
Hurwitz (the `1/√5` bound itself, via three consecutive continued-fraction
convergents) is left as future work and is noted in the gallery entry.

## The result

For the golden ratio `φ = (1+√5)/2` and any constant `c > √5`, only **finitely
many** rationals `p/q` satisfy `|φ − p/q| < 1/(c·q²)`. Consequently no
Hurwitz-type theorem can hold with a constant exceeding `√5`: the golden ratio
is the extremal irrational that pins the constant down.

## Method (elementary, axiom-free)

Write `A = p − qφ`, `B = p − qψ` where `ψ = (1−√5)/2` is the conjugate. Since
`φ + ψ = 1` and `φ·ψ = −1` (both in Mathlib), the product
`A·B = p² − pq − q² =: N` is an **integer**, and it is nonzero because `φ` is
irrational (a zero factor would make `φ = p/q` rational). Hence `|A·B| ≥ 1`.
Because `B = A + q√5`, the triangle inequality gives `|B| ≤ |A| + q√5`, so

  `1 ≤ |A|·|B| ≤ |A|² + |A|·q√5`.

Feeding in `|A| = q·|φ − p/q| < 1/(c·q)` and clearing denominators yields
`(c² − c√5)·q² < 1`. As `c > √5` makes `c² − c√5 > 0`, the denominators `q`
are bounded, so — together with the value bound `|φ − p/q| < 1` — the
approximating fractions lie in a fixed bounded box of bounded height, a finite
set.

## References

* A. Hurwitz, *Über die angenäherte Darstellung der Irrationalzahlen durch
  rationale Brüche*, Math. Ann. 39 (1891).
* G.H. Hardy & E.M. Wright, *An Introduction to the Theory of Numbers*, §11.8.
* Mathlib: `Mathlib/NumberTheory/Real/GoldenRatio.lean`,
  `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`.
-/
import Mathlib

namespace DirichletApproximationOQ01OQ01

open Set Real
open scoped goldenRatio

/-- **Bounded-height finiteness** (self-contained re-derivation of the
infrastructure lemma from the parent entry). The rationals lying in a bounded
real interval `[a, b]` whose denominator is at most `N` form a finite set: the
map `q ↦ (q.num, q.den)` embeds them into the finite integer box
`[-M, M] × [1, N]`, where `M` bounds the numerators via
`|q.num| = |q|·q.den ≤ max |a| |b| · N`. -/
theorem finite_bounded_den (a b : ℝ) (N : ℕ) :
    {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) ≤ b ∧ q.den ≤ N}.Finite := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max |a| |b| * N)
  apply Set.Finite.of_finite_image (f := fun q : ℚ => (q.num, q.den))
  · apply Set.Finite.subset
      ((Finset.Icc (-(M : ℤ)) (M : ℤ) ×ˢ Finset.Icc 1 N).finite_toSet)
    rintro p ⟨q, ⟨ha, hb, hden⟩, rfl⟩
    have hdpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    have hnum : (q.num : ℝ) = (q : ℝ) * (q.den : ℝ) := by
      rw [Rat.cast_def]; field_simp
    have hqle : (q : ℝ) ≤ max |a| |b| :=
      le_trans hb (le_trans (le_abs_self b) (le_max_right _ _))
    have hqge : -max |a| |b| ≤ (q : ℝ) :=
      le_trans (le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le a)) ha
    have habsq : |(q : ℝ)| ≤ max |a| |b| := abs_le.mpr ⟨hqge, hqle⟩
    have hdenR : (q.den : ℝ) ≤ (N : ℝ) := by exact_mod_cast hden
    have habsnum : |(q.num : ℝ)| ≤ (M : ℝ) := by
      rw [hnum, abs_mul, abs_of_pos hdpos]
      calc |(q : ℝ)| * (q.den : ℝ)
          ≤ max |a| |b| * (N : ℝ) := by gcongr
        _ ≤ (M : ℝ) := hM
    have hb1 : -(M : ℤ) ≤ q.num := by exact_mod_cast (abs_le.mp habsnum).1
    have hb2 : q.num ≤ (M : ℤ) := by exact_mod_cast (abs_le.mp habsnum).2
    simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨hb1, hb2⟩, q.pos, hden⟩
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    rw [← Rat.num_div_den x, ← Rat.num_div_den y, hxy.1, hxy.2]

set_option maxHeartbeats 1000000 in
/-- **Optimality of the Hurwitz constant √5.** For any `c > √5`, only finitely
many rationals approximate the golden ratio `φ` to within `1/(c·q²)`. -/
theorem finite_approx_gt_sqrt5 {c : ℝ} (hc : Real.sqrt 5 < c) :
    {r : ℚ | |Real.goldenRatio - (r : ℝ)| < 1 / (c * (r.den : ℝ) ^ 2)}.Finite := by
  have hs_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs_gt1 : (1 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have hc0 : (0 : ℝ) < c := lt_trans hs_pos hc
  have hc1 : (1 : ℝ) < c := lt_trans hs_gt1 hc
  have he : (0 : ℝ) < c ^ 2 - c * Real.sqrt 5 := by
    nlinarith [mul_pos hc0 (sub_pos.mpr hc)]
  obtain ⟨M, hM⟩ := exists_nat_ge (1 / (c ^ 2 - c * Real.sqrt 5))
  apply Set.Finite.subset
    (finite_bounded_den (Real.goldenRatio - 1) (Real.goldenRatio + 1) M)
  intro r hr
  simp only [Set.mem_setOf_eq] at hr ⊢
  have hQpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hQ1 : (1 : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hQne : (r.den : ℝ) ≠ 0 := hQpos.ne'
  -- The integer norm  N = p² − pq − q²  factors as  (p − qφ)(p − qψ).
  set N : ℤ := r.num ^ 2 - r.num * (r.den : ℤ) - (r.den : ℤ) ^ 2 with hNdef
  have hid : ((r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio)
      * ((r.num : ℝ) - (r.den : ℝ) * Real.goldenConj) = (N : ℝ) := by
    have e1 : Real.goldenRatio + Real.goldenConj = 1 := Real.goldenRatio_add_goldenConj
    have e2 : Real.goldenRatio * Real.goldenConj = -1 := Real.goldenRatio_mul_goldenConj
    have expand : ((r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio)
          * ((r.num : ℝ) - (r.den : ℝ) * Real.goldenConj)
        = (r.num : ℝ) ^ 2
            - (r.num : ℝ) * (r.den : ℝ) * (Real.goldenRatio + Real.goldenConj)
            + (r.den : ℝ) ^ 2 * (Real.goldenRatio * Real.goldenConj) := by ring
    rw [expand, e1, e2, hNdef]; push_cast; ring
  -- N ≠ 0, otherwise φ (or ψ) would be rational.
  have hNne : (N : ℝ) ≠ 0 := by
    intro h0
    have hzero : ((r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio)
        * ((r.num : ℝ) - (r.den : ℝ) * Real.goldenConj) = 0 := by rw [hid, h0]
    rcases mul_eq_zero.mp hzero with hA | hB
    · refine Real.goldenRatio_irrational ⟨r, ?_⟩
      have hnum : (r.num : ℝ) = (r.den : ℝ) * Real.goldenRatio := by linear_combination hA
      rw [Rat.cast_def, div_eq_iff hQne, hnum]; ring
    · refine Real.goldenConj_irrational ⟨r, ?_⟩
      have hnum : (r.num : ℝ) = (r.den : ℝ) * Real.goldenConj := by linear_combination hB
      rw [Rat.cast_def, div_eq_iff hQne, hnum]; ring
  -- |A|, |B| and their basic estimates.
  set a : ℝ := |(r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio| with ha_def
  set b : ℝ := |(r.num : ℝ) - (r.den : ℝ) * Real.goldenConj| with hb_def
  have ha0 : 0 ≤ a := abs_nonneg _
  -- 1 ≤ a·b, since a·b = |N| ≥ 1.
  have hab : 1 ≤ a * b := by
    have hNne' : N ≠ 0 := fun h => hNne (by rw [h]; simp)
    have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by
      calc (1 : ℝ) ≤ ((|N| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hNne'
        _ = |(N : ℝ)| := by rw [Int.cast_abs]
    rw [ha_def, hb_def, ← abs_mul, hid]; exact hN1
  -- b ≤ a + q√5, from  B = A + q√5  and the triangle inequality.
  have hBeq : (r.num : ℝ) - (r.den : ℝ) * Real.goldenConj
      = ((r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio) + (r.den : ℝ) * Real.sqrt 5 := by
    linear_combination (r.den : ℝ) * Real.goldenRatio_sub_goldenConj
  have hb_le : b ≤ a + (r.den : ℝ) * Real.sqrt 5 := by
    have h3 : |(r.den : ℝ) * Real.sqrt 5| = (r.den : ℝ) * Real.sqrt 5 :=
      abs_of_nonneg (by positivity)
    rw [hb_def, hBeq, ha_def]
    calc |((r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio) + (r.den : ℝ) * Real.sqrt 5|
        ≤ |(r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio| + |(r.den : ℝ) * Real.sqrt 5| :=
          abs_add_le _ _
      _ = |(r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio| + (r.den : ℝ) * Real.sqrt 5 := by
          rw [h3]
  -- a < 1/(c·q).
  have ha : a < 1 / (c * (r.den : ℝ)) := by
    have haeq : a = (r.den : ℝ) * |Real.goldenRatio - (r : ℝ)| := by
      rw [ha_def,
        show (r.num : ℝ) - (r.den : ℝ) * Real.goldenRatio
            = -((r.den : ℝ) * (Real.goldenRatio - (r : ℝ))) from by
          rw [Rat.cast_def]; field_simp; ring,
        abs_neg, abs_mul, abs_of_pos hQpos]
    rw [haeq]
    calc (r.den : ℝ) * |Real.goldenRatio - (r : ℝ)|
        < (r.den : ℝ) * (1 / (c * (r.den : ℝ) ^ 2)) := by
          exact mul_lt_mul_of_pos_left hr hQpos
      _ = 1 / (c * (r.den : ℝ)) := by
          rw [mul_one_div,
            div_eq_div_iff (mul_pos hc0 (pow_pos hQpos 2)).ne' (mul_pos hc0 hQpos).ne']; ring
  have hucq : a * (c * (r.den : ℝ)) < 1 :=
    (lt_div_iff₀ (mul_pos hc0 hQpos)).mp ha
  -- 1 ≤ a² + a·q√5.
  have hstep : a * b ≤ a * (a + (r.den : ℝ) * Real.sqrt 5) :=
    mul_le_mul_of_nonneg_left hb_le ha0
  have hI : 1 ≤ a ^ 2 + a * (r.den : ℝ) * Real.sqrt 5 := by nlinarith [hab, hstep]
  -- The crucial denominator bound: (c² − c√5)·q² < 1.
  have hw0 : 0 ≤ a * (c * (r.den : ℝ)) := mul_nonneg ha0 (mul_nonneg hc0.le hQpos.le)
  have hK : 0 < c * Real.sqrt 5 * (r.den : ℝ) ^ 2 :=
    mul_pos (mul_pos hc0 hs_pos) (pow_pos hQpos 2)
  -- Multiply  1 ≤ a² + a·q√5  by (c·q)²  to obtain  (c·q)² ≤ (a·c·q)² + (a·c·q)·K.
  have E : (c * (r.den : ℝ)) ^ 2
      ≤ (a * (c * (r.den : ℝ))) ^ 2
        + (a * (c * (r.den : ℝ))) * (c * Real.sqrt 5 * (r.den : ℝ) ^ 2) := by
    calc (c * (r.den : ℝ)) ^ 2
        = (c * (r.den : ℝ)) ^ 2 * 1 := by ring
      _ ≤ (c * (r.den : ℝ)) ^ 2 * (a ^ 2 + a * (r.den : ℝ) * Real.sqrt 5) :=
          mul_le_mul_of_nonneg_left hI (sq_nonneg _)
      _ = (a * (c * (r.den : ℝ))) ^ 2
            + (a * (c * (r.den : ℝ))) * (c * Real.sqrt 5 * (r.den : ℝ) ^ 2) := by ring
  have hw2 : (a * (c * (r.den : ℝ))) ^ 2 < 1 := by nlinarith [hw0, hucq]
  have hw3 : (a * (c * (r.den : ℝ))) * (c * Real.sqrt 5 * (r.den : ℝ) ^ 2)
      < c * Real.sqrt 5 * (r.den : ℝ) ^ 2 := by
    have h := mul_lt_mul_of_pos_right hucq hK
    rwa [one_mul] at h
  have hbound : (c ^ 2 - c * Real.sqrt 5) * (r.den : ℝ) ^ 2 < 1 := by
    nlinarith [E, hw2, hw3]
  -- Hence q ≤ M, a bound depending only on c.
  have hden_le : r.den ≤ M := by
    have hq2 : (r.den : ℝ) ^ 2 < 1 / (c ^ 2 - c * Real.sqrt 5) := by
      rw [lt_div_iff₀ he]; nlinarith [hbound]
    have hqle : (r.den : ℝ) ≤ (r.den : ℝ) ^ 2 := by nlinarith [hQ1]
    have hlt : (r.den : ℝ) < (M : ℝ) :=
      lt_of_le_of_lt hqle (lt_of_lt_of_le hq2 hM)
    have : r.den < M := by exact_mod_cast hlt
    exact le_of_lt this
  -- Value bound: |φ − r| < 1, so r lies in [φ−1, φ+1].
  have hval : |Real.goldenRatio - (r : ℝ)| < 1 := by
    have hb1 : 1 / (c * (r.den : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hc1, hQ1]
    exact lt_of_lt_of_le hr hb1
  rw [abs_lt] at hval
  exact ⟨by linarith [hval.2], by linarith [hval.1], hden_le⟩

/-- **The √5 set is not infinite.** Restating optimality: for `c > √5` there are
*not* infinitely many `1/(c·q²)`-approximations to the golden ratio. -/
theorem not_infinite_approx_gt_sqrt5 {c : ℝ} (hc : Real.sqrt 5 < c) :
    ¬ {r : ℚ | |Real.goldenRatio - (r : ℝ)| < 1 / (c * (r.den : ℝ) ^ 2)}.Infinite :=
  fun h => h (finite_approx_gt_sqrt5 hc)

/-- **Optimality of the Hurwitz constant.** No Hurwitz-type theorem holds with a
constant exceeding `√5`: for any `c > √5` it is false that *every* irrational
has infinitely many approximations within `1/(c·q²)` — the golden ratio is a
counterexample. This is the sharpness statement that complements Hurwitz's
existence theorem. -/
theorem hurwitz_constant_optimal {c : ℝ} (hc : Real.sqrt 5 < c) :
    ¬ ∀ ξ : ℝ, Irrational ξ →
        {r : ℚ | |ξ - (r : ℝ)| < 1 / (c * (r.den : ℝ) ^ 2)}.Infinite := by
  intro H
  exact not_infinite_approx_gt_sqrt5 hc (H Real.goldenRatio Real.goldenRatio_irrational)

end DirichletApproximationOQ01OQ01
