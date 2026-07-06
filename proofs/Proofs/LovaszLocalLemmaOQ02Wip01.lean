/-
  Lovász Local Lemma — OQ-02, wip-01:
  The exact algebraic threshold T(d) strictly beats the classical e-bound.

  The parent entry `LovaszLocalLemmaOQ02.lean` proves that

      T(d) = dᵈ / (d+1)ᵈ⁺¹ = (1/(d+1)) · (d/(d+1))ᵈ

  is the *exact algebraic maximum* of `x · (1-x)ᵈ` over `x ∈ [0,1]`, hence the
  sharp threshold of the symmetric Lovász Local Lemma: probabilities `p ≤ T(d)`
  are avoidable, `p > T(d)` is not (algebraically).

  The **classical** symmetric LLL (Erdős–Lovász 1975) is usually quoted in the
  looser form
      e · p · (d+1) ≤ 1      i.e.      p ≤ 1 / (e·(d+1)),
  where `e = exp 1`. This file quantifies the gap between the two criteria:

      **T(d)  >  1 / (e·(d+1))       for every d ≥ 1.**

  Equivalently `e·(d+1)·T(d) > 1`: the sharp threshold admits strictly more
  probability mass than the classical `1/(e(d+1))` bound. The single analytic
  ingredient is the classical inequality `(1 + 1/d)ᵈ < e`, which we derive from
  Mathlib's `Real.add_one_lt_exp` and `Real.exp_nat_mul`.

  Since `1/e` is irrational the comparison is stated over `ℝ`, using the real cast
  of the parent's rational threshold `lllThreshold`.

  Parent: LovaszLocalLemmaOQ02.lean  (T(d) = exact algebraic maximum)
  Reference: Erdős–Lovász 1975; Alon–Spencer, "The Probabilistic Method".
-/

import Mathlib
import Proofs.LovaszLocalLemmaOQ02

open Real
open ProbMethod.LovaszLocal

namespace ProbMethod.LovaszLocal.OQ02.Wip01

/-- Real closed form of the LLL threshold: `T(d) = dᵈ / (d+1)ᵈ⁺¹` for `d ≥ 1`. -/
theorem lllThreshold_cast (d : ℕ) (hd : 0 < d) :
    ((lllThreshold d : ℚ) : ℝ) = (d : ℝ) ^ d / ((d : ℝ) + 1) ^ (d + 1) := by
  simp only [lllThreshold, if_neg (Nat.pos_iff_ne_zero.mp hd)]
  push_cast
  ring

/-- **The classical bound `(1 + 1/d)ᵈ < e`** for every `d ≥ 1`.
    Proof: `1 + 1/d < exp(1/d)` (strict `add_one_lt_exp`), raised to the `d`-th
    power, gives `(1+1/d)ᵈ < exp(1/d)ᵈ = exp(d·(1/d)) = exp 1 = e`. -/
theorem one_add_inv_pow_lt_exp_one (d : ℕ) (hd : 0 < d) :
    (1 + 1 / (d : ℝ)) ^ d < Real.exp 1 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hxpos : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  have hstep : 1 + 1 / (d : ℝ) < Real.exp (1 / (d : ℝ)) := by
    have h := Real.add_one_lt_exp (ne_of_gt hxpos)
    linarith
  calc (1 + 1 / (d : ℝ)) ^ d
      < (Real.exp (1 / (d : ℝ))) ^ d :=
        pow_lt_pow_left₀ hstep (by positivity) (Nat.pos_iff_ne_zero.mp hd)
    _ = Real.exp ((d : ℝ) * (1 / (d : ℝ))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp 1 := by rw [mul_one_div, div_self hdr.ne']

/-- Reformulation `(d+1)ᵈ < dᵈ · e`, obtained from `(1+1/d)ᵈ < e` by clearing
    the `dᵈ` denominator. This is the exact fact consumed by the main theorem. -/
theorem succ_pow_lt_pow_mul_exp (d : ℕ) (hd : 0 < d) :
    ((d : ℝ) + 1) ^ d < (d : ℝ) ^ d * Real.exp 1 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hne : (d : ℝ) ≠ 0 := hdr.ne'
  have hkey := one_add_inv_pow_lt_exp_one d hd
  have hmul := mul_lt_mul_of_pos_right hkey (pow_pos hdr d)
  have hrw : (1 + 1 / (d : ℝ)) ^ d * (d : ℝ) ^ d = ((d : ℝ) + 1) ^ d := by
    rw [← mul_pow]
    congr 1
    rw [add_mul, one_mul, one_div_mul_cancel hne]
  rw [hrw, mul_comm (Real.exp 1) ((d : ℝ) ^ d)] at hmul
  exact hmul

/-- **Main theorem — the sharp LLL threshold beats the classical `e`-bound.**
    For every `d ≥ 1`,
        `1 / (e·(d+1))  <  T(d)`,
    where `T(d) = lllThreshold d` is the parent's exact algebraic threshold.
    The classical criterion `e·p·(d+1) ≤ 1` (i.e. `p ≤ 1/(e(d+1))`) is therefore
    strictly weaker than the sharp threshold. -/
theorem lllThreshold_gt_classical_ebound (d : ℕ) (hd : 0 < d) :
    1 / (Real.exp 1 * ((d : ℝ) + 1)) < ((lllThreshold d : ℚ) : ℝ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  rw [lllThreshold_cast d hd,
      div_lt_div_iff₀ (by positivity) (by positivity),
      one_mul, pow_succ, ← mul_assoc]
  exact mul_lt_mul_of_pos_right (succ_pow_lt_pow_mul_exp d hd) hd1

/-- **Product form of the main theorem:** `e · (d+1) · T(d) > 1`.
    This is the statement that the sharp threshold violates the classical
    criterion `e · p · (d+1) ≤ 1` at `p = T(d)`. -/
theorem exp_mul_threshold_gt_one (d : ℕ) (hd : 0 < d) :
    1 < Real.exp 1 * ((d : ℝ) + 1) * ((lllThreshold d : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < Real.exp 1 * ((d : ℝ) + 1) := by positivity
  have h := (div_lt_iff₀ hpos).mp (lllThreshold_gt_classical_ebound d hd)
  linarith [h, mul_comm (((lllThreshold d : ℚ) : ℝ)) (Real.exp 1 * ((d : ℝ) + 1))]

end ProbMethod.LovaszLocal.OQ02.Wip01
