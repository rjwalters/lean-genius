import Proofs.CollatzCyclesOQ02
import Mathlib

/-!
# Collatz Cycles OQ-02-OQ-01: Continued-Fraction Convergents of `log₂ 3` and a Sharp Rational Cycle Bound

The parent `CollatzCyclesOQ02` proves, for a hypothetical non-trivial Collatz cycle with
`J` odd (tripling) steps and `M` even (halving) steps, the logarithmic lower bound
`M > J · log₂ 3` (and `L = M + J > J · log₂ 6`), but it explicitly leaves the **sharp
numerical refinement** — Eliahou's use of the *continued-fraction expansion* of `log₂ 3`
to control the cycle length — unformalised.

This file supplies the continued-fraction ingredient in a fully elementary, axiom-free way.

## The continued fraction of `log₂ 3`

`log₂ 3 = 1.5849625007…` has continued fraction expansion

  `log₂ 3 = [1; 1, 1, 2, 2, 3, 1, 5, …]`,

with convergents

  `1/1,  2/1,  3/2,  8/5,  19/12,  65/41,  84/53,  485/306,  …`

The even-indexed convergents lie **below** `log₂ 3` and the odd-indexed ones lie **above**.
Every one of these bounds is equivalent to a *decidable integer comparison* between powers
of `2` and `3`, because

  `p/q < log₂ 3  ⟺  2^p < 3^q`      and      `p/q > log₂ 3  ⟺  2^p > 3^q`.

We verify the whole ladder up to `485/306` this way (`norm_num` on the power comparisons),
obtaining the rigorous sandwich

  `84/53  <  log₂ 3  <  485/306`,

i.e. `log₂ 3` is pinned to an interval of width `485/306 − 84/53 = 1/16218 ≈ 6.2·10⁻⁵`.

## A sharp rational lower bound on cycle length (no logarithms)

The lower convergent `84/53 < log₂ 3` yields, via the halving constraint `3^J < 2^M`, the
clean **integer** inequality

  `53 · M  ≥  84 · J + 1`,

proved *without any real analysis*: chaining `2^{84} < 3^{53}` and `3^J < 2^M` gives
`2^{84J} < 3^{53J} < 2^{53M}`, whence `84J < 53M` by strict monotonicity of `2^{(·)}`.
Adding `53 · J` to both sides sharpens the cycle-length bound to

  `53 · L = 53(M + J)  ≥  137 · J + 1`,   i.e.   `L ≥ (137 J + 1)/53 > 2.5849 · J`,

matching the slope `log₂ 6 ≈ 2.585` of the parent's real-analytic bound but with an
explicit rational constant coming directly from a convergent of `log₂ 3`.

## Honest scope

This formalises the continued-fraction *convergent bounds* of `log₂ 3` and the sharp
rational bounds they give for the cycle length: the lower convergent `84/53` yields
`53·M ≥ 84·J + 1` in the cycle regime `3^J < 2^M`, and the upper convergent `485/306`
yields the mirror bound `306·M + 1 ≤ 485·J` in the anti-cycle regime `2^M < 3^J`, so the
two sharpest convergents bracket the crossover ratio `M/J` from both sides with explicit
integer certificates. Eliahou's celebrated numerical constant (a non-trivial cycle has
length `≥ 17 087 915`) additionally needs the *two-sided* Diophantine gap on a *single*
`(M,J)` — an upper constraint `2^M < 3^J·(1 + small)` from the cycle's minimal element —
combined with the best-approximation denominators; that sharper second ingredient is beyond
this entry. What is proved here is exactly the CF-approximation input, axiom-free.

`#print axioms` on the headline results shows only `propext`, `Classical.choice`,
`Quot.sound` (no `Lean.ofReduceBool`, no `sorryAx`).
-/

open Real

-- The convergent certificates compare powers up to `2^485` / `3^306`; raise `norm_num`'s
-- exponentiation-evaluation threshold (default 256) so these integer comparisons evaluate.
set_option exponentiation.threshold 512

namespace CollatzCyclesOQ02OQ01

/-! ## Part I: from power comparisons to logarithm bounds -/

/-- **Lower convergent bound.** If `2^p < 3^q` then `p < q · log₂ 3`, i.e. `p/q < log₂ 3`.
The whole content is monotonicity of `log₂` applied to the integer inequality `2^p < 3^q`. -/
theorem pow_lt_to_logb {p q : ℕ} (h : 2 ^ p < 3 ^ q) :
    (p : ℝ) < (q : ℝ) * Real.logb 2 3 := by
  have hcast : (2 : ℝ) ^ p < (3 : ℝ) ^ q := by exact_mod_cast h
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hlt : Real.logb 2 ((2 : ℝ) ^ p) < Real.logb 2 ((3 : ℝ) ^ q) :=
    Real.logb_lt_logb (by norm_num) h2pos hcast
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlt
  rw [mul_one] at hlt
  exact hlt

/-- **Upper convergent bound.** If `3^q < 2^p` then `q · log₂ 3 < p`, i.e. `log₂ 3 < p/q`. -/
theorem pow_gt_to_logb {p q : ℕ} (h : 3 ^ q < 2 ^ p) :
    (q : ℝ) * Real.logb 2 3 < (p : ℝ) := by
  have hcast : (3 : ℝ) ^ q < (2 : ℝ) ^ p := by exact_mod_cast h
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
  have hlt : Real.logb 2 ((3 : ℝ) ^ q) < Real.logb 2 ((2 : ℝ) ^ p) :=
    Real.logb_lt_logb (by norm_num) h3pos hcast
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlt
  rw [mul_one] at hlt
  exact hlt

/-! ## Part II: the continued-fraction ladder for `log₂ 3`

Each bound is stated in cleared-denominator form `p < q · log₂ 3` (a convergent below)
or `q · log₂ 3 < p` (a convergent above); the power comparison is discharged by `norm_num`.
The convergents are `1/1, 2/1, 3/2, 8/5, 19/12, 65/41, 84/53, 485/306`. -/

/-- Convergent `1/1` (below): `1 < log₂ 3`. -/
theorem conv_1_1 : (1 : ℝ) < 1 * Real.logb 2 3 := by
  have h := pow_lt_to_logb (p := 1) (q := 1) (by norm_num); push_cast at h; linarith

/-- Convergent `2/1` (above): `log₂ 3 < 2`. -/
theorem conv_2_1 : 1 * Real.logb 2 3 < (2 : ℝ) := by
  have h := pow_gt_to_logb (p := 2) (q := 1) (by norm_num); push_cast at h; linarith

/-- Convergent `3/2` (below): `3 < 2 · log₂ 3`. -/
theorem conv_3_2 : (3 : ℝ) < 2 * Real.logb 2 3 := by
  have h := pow_lt_to_logb (p := 3) (q := 2) (by norm_num); push_cast at h; linarith

/-- Convergent `8/5` (above): `5 · log₂ 3 < 8`. -/
theorem conv_8_5 : 5 * Real.logb 2 3 < (8 : ℝ) := by
  have h := pow_gt_to_logb (p := 8) (q := 5) (by norm_num); push_cast at h; linarith

/-- Convergent `19/12` (below): `19 < 12 · log₂ 3`. -/
theorem conv_19_12 : (19 : ℝ) < 12 * Real.logb 2 3 := by
  have h := pow_lt_to_logb (p := 19) (q := 12) (by norm_num); push_cast at h; linarith

/-- Convergent `65/41` (above): `41 · log₂ 3 < 65`. -/
theorem conv_65_41 : 41 * Real.logb 2 3 < (65 : ℝ) := by
  have h := pow_gt_to_logb (p := 65) (q := 41) (by norm_num); push_cast at h; linarith

/-- Convergent `84/53` (below): `84 < 53 · log₂ 3`. This is the sharpest lower convergent
of the ladder; `84/53 = 1.5849056… < log₂ 3`. -/
theorem conv_84_53 : (84 : ℝ) < 53 * Real.logb 2 3 := by
  have h := pow_lt_to_logb (p := 84) (q := 53) (by norm_num); push_cast at h; linarith

/-- Convergent `485/306` (above): `306 · log₂ 3 < 485`. This is the sharpest upper convergent
of the ladder; `485/306 = 1.5849673… > log₂ 3`. -/
theorem conv_485_306 : 306 * Real.logb 2 3 < (485 : ℝ) := by
  have h := pow_gt_to_logb (p := 485) (q := 306) (by norm_num); push_cast at h; linarith

/-- **Headline sandwich.** The two sharpest convergents pin `log₂ 3` to the interval
`(84/53, 485/306)` of width `1/16218`:

  `84 < 53 · log₂ 3`   and   `306 · log₂ 3 < 485`. -/
theorem logb_two_three_sandwich :
    (84 : ℝ) < 53 * Real.logb 2 3 ∧ 306 * Real.logb 2 3 < (485 : ℝ) :=
  ⟨conv_84_53, conv_485_306⟩

/-! ## Part III: the sharp rational cycle bound (elementary, no logarithms) -/

/-- **Sharp halving bound from the convergent `84/53`.**

For a hypothetical non-trivial Collatz cycle with `J` odd steps and `M` even steps (halving
constraint `3^J < 2^M`), the halvings satisfy the sharp *integer* inequality

  `53 · M ≥ 84 · J + 1`.

The proof is purely arithmetic — no real logarithms. From the convergent inequality
`2^{84} < 3^{53}` we get `2^{84J} < 3^{53J}`, and raising the cycle constraint to the `53`rd
power gives `3^{53J} < 2^{53M}`; chaining and cancelling the base `2` yields `84J < 53M`. -/
theorem sharp_halving_bound {M J : ℕ} (h : 3 ^ J < 2 ^ M) :
    84 * J + 1 ≤ 53 * M := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · -- `J = 0`: the constraint is `1 < 2^M`, forcing `M ≥ 1`, so `84·0 + 1 ≤ 53·M`.
    subst hJ
    simp only [pow_zero] at h
    have hM : M ≠ 0 := by rintro rfl; simp at h
    omega
  · -- `J ≥ 1`: chain `2^{84J} < 3^{53J} < 2^{53M}`.
    have hbase : (2 : ℕ) ^ 84 < 3 ^ 53 := by norm_num
    have h1 : (2 : ℕ) ^ (84 * J) < 3 ^ (53 * J) := by
      rw [pow_mul, pow_mul]
      exact Nat.pow_lt_pow_left hbase hJ.ne'
    have h2 : (3 : ℕ) ^ (53 * J) < 2 ^ (53 * M) := by
      have e1 : (3 : ℕ) ^ (53 * J) = (3 ^ J) ^ 53 := by rw [← pow_mul, Nat.mul_comm]
      have e2 : (2 : ℕ) ^ (53 * M) = (2 ^ M) ^ 53 := by rw [← pow_mul, Nat.mul_comm]
      rw [e1, e2]
      exact Nat.pow_lt_pow_left h (by norm_num)
    have h3 : (2 : ℕ) ^ (84 * J) < 2 ^ (53 * M) := lt_trans h1 h2
    have h4 : 84 * J < 53 * M := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
    omega

/-- **Sharp cycle-length bound.** With total length `L = M + J`, the sharp halving bound
gives `53 · L ≥ 137 · J + 1`, i.e. `L > (137/53) · J = 2.5849… · J`. This reproduces the
parent's real-analytic slope `log₂ 6 ≈ 2.585` with an explicit rational constant drawn from
the continued fraction of `log₂ 3`. -/
theorem sharp_cycle_length_bound {M J : ℕ} (h : 3 ^ J < 2 ^ M) :
    137 * J + 1 ≤ 53 * (M + J) := by
  have := sharp_halving_bound h
  omega

/-! ## Part IV: the dual bound from the upper convergent `485/306`

Parts II–III used the *lower* convergent `84/53 < log₂ 3` (integer certificate `2^84 < 3^53`).
The *upper* convergent `log₂ 3 < 485/306` (integer certificate `3^306 < 2^485`) gives the
mirror-image inequality, closing the elementary two-sided pinning of the ratio `M/J`. -/

/-- **Dual sharp bound from the upper convergent `485/306`.**

In the *anti-cycle* regime where tripling dominates (`2^M < 3^J`), the halvings obey the
sharp *integer* upper bound

  `306 · M + 1 ≤ 485 · J`,

again with no real analysis. From the convergent certificate `3^306 < 2^485` we raise
`2^M < 3^J` to the `306`th power: `2^{306M} < 3^{306J} = (3^306)^J < (2^485)^J = 2^{485M}`,
and cancel the base `2`. Together with `sharp_halving_bound` this shows the two sharpest
convergents `84/53` and `485/306` *bracket* the crossover ratio `M/J = log₂ 3` from both
sides with explicit integer certificates. -/
theorem sharp_tripling_bound {M J : ℕ} (h : 2 ^ M < 3 ^ J) :
    306 * M + 1 ≤ 485 * J := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · -- `J = 0`: the hypothesis becomes `2^M < 1`, impossible since `2^M ≥ 1`.
    subst hJ
    simp only [pow_zero] at h
    have : 1 ≤ 2 ^ M := Nat.one_le_pow _ _ (by norm_num)
    omega
  · -- `J ≥ 1`: chain `2^{306M} < 3^{306J} < 2^{485J}`.
    have hbase : (3 : ℕ) ^ 306 < 2 ^ 485 := by norm_num
    have h1 : (2 : ℕ) ^ (306 * M) < 3 ^ (306 * J) := by
      have e1 : (2 : ℕ) ^ (306 * M) = (2 ^ M) ^ 306 := by rw [← pow_mul, Nat.mul_comm]
      have e2 : (3 : ℕ) ^ (306 * J) = (3 ^ J) ^ 306 := by rw [← pow_mul, Nat.mul_comm]
      rw [e1, e2]
      exact Nat.pow_lt_pow_left h (by norm_num)
    have h2 : (3 : ℕ) ^ (306 * J) < 2 ^ (485 * J) := by
      rw [pow_mul, pow_mul]
      exact Nat.pow_lt_pow_left hbase hJ.ne'
    have h3 : (2 : ℕ) ^ (306 * M) < 2 ^ (485 * J) := lt_trans h1 h2
    have h4 : 306 * M < 485 * J := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
    omega

/-- **Two-sided ratio pinning.** Combining the two sharpest convergents, for any `J ≥ 1`:
if the halving constraint `3^J < 2^M` holds (a genuine cycle) then `M/J > 84/53`, and if the
reverse `2^M < 3^J` holds then `M/J < 485/306`. Stated in cleared-denominator integer form,
the crossover `2^M` vs `3^J` is certified by these two convergents on either side. -/
theorem ratio_pinned_by_convergents {M J : ℕ} :
    (3 ^ J < 2 ^ M → 84 * J + 1 ≤ 53 * M) ∧
    (2 ^ M < 3 ^ J → 306 * M + 1 ≤ 485 * J) :=
  ⟨sharp_halving_bound, sharp_tripling_bound⟩

/-- Sanity check: `M = 6` is excluded at `J = 4` (the parent's ladder requires `M ≥ 7`),
since the halving constraint `3^4 < 2^6` is false (`81 > 64`). -/
theorem sharp_bound_excludes_M6_at_J4 : ¬ (3 ^ 4 < 2 ^ 6) := by norm_num

end CollatzCyclesOQ02OQ01

-- Axiom audit: only the standard foundational axioms, in particular no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms CollatzCyclesOQ02OQ01.sharp_halving_bound
#print axioms CollatzCyclesOQ02OQ01.sharp_tripling_bound
#print axioms CollatzCyclesOQ02OQ01.ratio_pinned_by_convergents
#print axioms CollatzCyclesOQ02OQ01.logb_two_three_sandwich
