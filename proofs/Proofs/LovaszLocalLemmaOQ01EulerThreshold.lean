/-
# Lovász Local Lemma — OQ-01: The Euler Symmetric Condition Implies the Tight Threshold

The gallery proof `LovaszLocalLemma.lean` records the *tight* symmetric threshold

  `T(d) = lllThreshold d = dᵈ / (d+1)^{d+1}`,

the exact maximum of `x (1 - x)ᵈ`, and proves the symmetric LLL under the hypothesis
`P[Aᵢ] ≤ T(d)`. The measure-theoretic OQ-01 front, meanwhile, is stated against the
*memorable* symmetric condition that appears throughout the literature,

  `e · p · (d + 1) ≤ 1`,

where `e = exp 1`. These are two different sufficient conditions, and the standard
textbook remark is that the Euler form is the (slightly weaker, hence safe)
consequence of the tight one: **`e · p · (d+1) ≤ 1` implies `p ≤ T(d)`.**

This file formalizes that bridge. It is elementary real analysis — *not* progress on
the hard measure-theoretic induction — but it ties the two thresholds together with
a machine-checked proof and pins down the exact inequality that makes the Euler form
usable: `(1 + 1/d)ᵈ ≤ e` (the classic `e` bound), from `1 + x ≤ exp x`.

## Main results

* `one_add_inv_pow_le_exp_one` : `(1 + 1/d)ᵈ ≤ e` for `d ≥ 1` — the elementary
  Euler bound, proved from `Real.add_one_le_exp` raised to the `d`-th power.
* `succ_pow_le_exp_mul` : `(d+1)ᵈ ≤ e · dᵈ`, the multiplicative form.
* `inv_exp_mul_le_lllThreshold` : `1 / (e · (d+1)) ≤ T(d)` — the Euler budget sits
  below the tight threshold.
* `euler_condition_implies_lllThreshold` : `e · p · (d+1) ≤ 1 → p ≤ T(d)`, the bridge:
  any probability admitted by the memorable symmetric condition is admitted by the
  tight threshold, so the tight-threshold symmetric LLL (`LovaszLocalLemma.symmetric_lll`)
  applies verbatim under `e · p · (d+1) ≤ 1`.

Everything is over `ℝ`; `lllThreshold` is cast from `ℚ` via `lllThreshold_cast`.
-/
import Proofs.LovaszLocalLemma

open Real ProbMethod.LovaszLocal

namespace LovaszLocalLemmaOQ01EulerThreshold

/-- The classic Euler bound `(1 + 1/d)ᵈ ≤ e` for `d ≥ 1`.

Proof: `Real.add_one_le_exp` gives `1/d + 1 ≤ exp (1/d)`; raising both nonnegative
sides to the `d`-th power and using `exp (1/d) ^ d = exp (d · (1/d)) = exp 1`
(with `d · (1/d) = 1` since `d ≠ 0`) finishes. -/
theorem one_add_inv_pow_le_exp_one (d : ℕ) (hd : 1 ≤ d) :
    (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hstep : (1 + 1 / (d : ℝ)) ≤ Real.exp (1 / d) := by
    have h := Real.add_one_le_exp (1 / (d : ℝ))
    linarith
  calc (1 + 1 / (d : ℝ)) ^ d
      ≤ (Real.exp (1 / d)) ^ d := by
        exact pow_le_pow_left₀ (by positivity) hstep d
    _ = Real.exp ((d : ℝ) * (1 / d)) := by rw [← Real.exp_nat_mul]
    _ = Real.exp 1 := by rw [mul_one_div, div_self (ne_of_gt hd0)]

/-- Multiplicative form of the Euler bound: `(d+1)ᵈ ≤ e · dᵈ`. -/
theorem succ_pow_le_exp_mul (d : ℕ) (hd : 1 ≤ d) :
    ((d : ℝ) + 1) ^ d ≤ Real.exp 1 * (d : ℝ) ^ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hbase : (1 + 1 / (d : ℝ)) = ((d : ℝ) + 1) / d := by field_simp
  have h := one_add_inv_pow_le_exp_one d hd
  rw [hbase, div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ d)] at h
  linarith

/-- Real-cast of the tight symmetric threshold for `d ≥ 1`:
`(T(d) : ℝ) = dᵈ / (d+1)^{d+1}`. -/
theorem lllThreshold_cast (d : ℕ) (hd : 1 ≤ d) :
    (lllThreshold d : ℝ) = (d : ℝ) ^ d / ((d : ℝ) + 1) ^ (d + 1) := by
  simp only [lllThreshold, if_neg (by omega : d ≠ 0)]
  push_cast
  ring

/-- The Euler budget lies below the tight threshold: `1 / (e · (d+1)) ≤ T(d)`.

Equivalently `(d+1)^{d+1} ≤ e · (d+1) · dᵈ`, which after cancelling `(d+1)` is the
multiplicative Euler bound `succ_pow_le_exp_mul`. -/
theorem inv_exp_mul_le_lllThreshold (d : ℕ) (hd : 1 ≤ d) :
    (1 : ℝ) / (Real.exp 1 * ((d : ℝ) + 1)) ≤ (lllThreshold d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [lllThreshold_cast d hd, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    pow_succ]
  have hkey := mul_le_mul_of_nonneg_right (succ_pow_le_exp_mul d hd) (le_of_lt hd1)
  nlinarith [hkey]

/-- **The Euler symmetric condition implies the tight threshold.**
If `e · p · (d+1) ≤ 1` (the memorable symmetric LLL condition), then
`p ≤ T(d)`, the tight threshold of the gallery proof. Hence the symmetric LLL under
the tight threshold (`LovaszLocalLemma.symmetric_lll`) applies verbatim to any family
whose event probabilities satisfy the Euler condition. -/
theorem euler_condition_implies_lllThreshold (d : ℕ) (hd : 1 ≤ d)
    (p : ℝ) (hcond : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
    p ≤ (lllThreshold d : ℝ) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hstep : p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hcond]
  exact le_trans hstep (inv_exp_mul_le_lllThreshold d hd)

end LovaszLocalLemmaOQ01EulerThreshold
