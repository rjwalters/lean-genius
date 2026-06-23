import Mathlib

/-
# Non-Uniform Birthday Problem: Uniform Minimizes Collisions (OQ-02-OQ-01-OQ-02)

## What This Proves
The classic birthday problem assumes birthdays are *uniformly* distributed over
`d` days. Real distributions are non-uniform. A natural extremal question is:
among all probability distributions on `d` outcomes, which one is *least* likely
to produce a collision?

For two independent draws from a distribution `p = (p₀, …, p_{d-1})`, the
probability that they coincide ("collision") is

  C(p) = ∑ᵢ pᵢ².

This file proves the **n = 2 case of the non-uniform birthday extremality**:

  C(p) ≥ 1/d   for every probability vector p,   with equality iff p is uniform.

Equivalently, the no-collision probability `1 - C(p)` is *maximized* by the
uniform distribution. So uniform birthdays are the hardest case for the birthday
paradox — any seasonal bias only makes collisions *more* likely. This is the
two-draw instance of the Munford (1977) / Klamkin–Newman extremal result.

## Key Mathematical Idea
The whole result follows from a single **variance identity**: writing the
uniform value `1/d` as the mean,

  ∑ᵢ pᵢ² − 1/d = ∑ᵢ (pᵢ − 1/d)²    (when ∑ᵢ pᵢ = 1).

The right-hand side is a sum of squares, hence `≥ 0` (giving the bound) and `= 0`
iff every `pᵢ = 1/d` (giving the equality case). No Cauchy–Schwarz black box is
needed; the equality characterization falls out directly.

## Scope
- [x] Variance identity  `∑ pᵢ² − 1/d = ∑ (pᵢ − 1/d)²`
- [x] Lower bound  `∑ pᵢ² ≥ 1/d`  (uniform minimizes collision probability)
- [x] Equality iff uniform
- [x] Uniform collision value is exactly `1/d`
- [x] No-collision probability `1 − ∑ pᵢ² ≤ 1 − 1/d`

## Not Covered (gated)
The general `n`-draw statement — the no-collision probability
`n! · eₙ(p)` (with `eₙ` the elementary symmetric polynomial) is maximized at the
uniform distribution — needs Maclaurin's inequality / Schur-concavity of `eₙ` on
the simplex, neither of which is currently in Mathlib. Documented as the
follow-up gate.

## References
- T. W. Munford, *A note on the uniformity assumption in the birthday problem*,
  Amer. Statist. 31 (1977).
- Klamkin & Newman, *Extensions of the birthday surprise*, J. Combin. Theory (1967).
-/

open Finset

namespace BirthdayNonUniform

variable {d : ℕ}

/-- **Variance identity.** For a probability vector `p` on `d` outcomes
(`∑ᵢ pᵢ = 1`), the excess of the collision probability over the uniform value
`1/d` equals the sum of squared deviations from `1/d`:

  `∑ᵢ pᵢ² − 1/d = ∑ᵢ (pᵢ − 1/d)²`. -/
theorem sum_sq_sub_one_div_card (p : Fin d → ℝ) (hd : 0 < d)
    (hsum : ∑ i, p i = 1) :
    (∑ i, p i ^ 2) - 1 / (d : ℝ) = ∑ i, (p i - 1 / (d : ℝ)) ^ 2 := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have key : ∑ i, (p i - 1 / (d : ℝ)) ^ 2
      = ∑ i, (p i ^ 2 - (2 / (d : ℝ)) * p i + (1 / (d : ℝ)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **Uniform minimizes the two-draw collision probability.** For any probability
vector `p` on `d` outcomes, the collision probability is at least the uniform
value `1/d`:

  `1/d ≤ ∑ᵢ pᵢ²`. -/
theorem one_div_card_le_sum_sq (p : Fin d → ℝ) (hd : 0 < d)
    (hsum : ∑ i, p i = 1) :
    1 / (d : ℝ) ≤ ∑ i, p i ^ 2 := by
  have hnn : (0 : ℝ) ≤ ∑ i, (p i - 1 / (d : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h := sum_sq_sub_one_div_card p hd hsum
  linarith

/-- **Equality holds iff the distribution is uniform.** The collision probability
attains its minimum `1/d` exactly when every `pᵢ = 1/d`. -/
theorem sum_sq_eq_one_div_card_iff (p : Fin d → ℝ) (hd : 0 < d)
    (hsum : ∑ i, p i = 1) :
    (∑ i, p i ^ 2) = 1 / (d : ℝ) ↔ ∀ i, p i = 1 / (d : ℝ) := by
  rw [show ((∑ i, p i ^ 2) = 1 / (d : ℝ)) ↔ ((∑ i, p i ^ 2) - 1 / (d : ℝ) = 0)
        from sub_eq_zero.symm,
    sum_sq_sub_one_div_card p hd hsum,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _]
  constructor
  · intro h i
    have hi : (p i - 1 / (d : ℝ)) ^ 2 = 0 := h i (Finset.mem_univ i)
    have : p i - 1 / (d : ℝ) = 0 := by
      exact pow_eq_zero_iff (by norm_num) |>.mp hi
    linarith
  · intro h i _
    rw [h i]
    ring

/-- The collision probability of the **uniform** distribution is exactly `1/d`. -/
theorem uniform_sum_sq (hd : 0 < d) :
    ∑ _i : Fin d, (1 / (d : ℝ)) ^ 2 = 1 / (d : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The uniform distribution is a genuine probability vector: `∑ᵢ (1/d) = 1`. -/
theorem uniform_sum (hd : 0 < d) :
    ∑ _i : Fin d, (1 / (d : ℝ)) = 1 := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **No-collision probability is maximized by the uniform distribution.** The
probability that two independent draws are distinct, `1 − ∑ᵢ pᵢ²`, never exceeds
its uniform value `1 − 1/d = (d−1)/d`. -/
theorem no_collision_le (p : Fin d → ℝ) (hd : 0 < d) (hsum : ∑ i, p i = 1) :
    1 - ∑ i, p i ^ 2 ≤ 1 - 1 / (d : ℝ) := by
  have h := one_div_card_le_sum_sq p hd hsum
  linarith

/-- No-collision probability equals the uniform maximum iff `p` is uniform. -/
theorem no_collision_eq_iff (p : Fin d → ℝ) (hd : 0 < d) (hsum : ∑ i, p i = 1) :
    1 - ∑ i, p i ^ 2 = 1 - 1 / (d : ℝ) ↔ ∀ i, p i = 1 / (d : ℝ) := by
  rw [sub_right_inj, sum_sq_eq_one_div_card_iff p hd hsum]

end BirthdayNonUniform
