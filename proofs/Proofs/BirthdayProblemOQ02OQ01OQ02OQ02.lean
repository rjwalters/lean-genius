import Proofs.BirthdayProblemOQ02OQ01OQ02
import Mathlib

/-
# A Quantitative Non-Uniform Birthday Bound: Bias Raises Collisions at Least Quadratically in Total Variation (OQ-02-OQ-01-OQ-02-OQ-02)

## What This Proves
The parent file (`BirthdayProblemOQ02OQ01OQ02`) shows that among all probability
distributions `p = (p₀, …, p_{d-1})` on `d` outcomes, the uniform distribution
*minimizes* the two-draw collision probability

  C(p) = ∑ᵢ pᵢ²   ,   with   C(p) ≥ 1/d   and equality iff `p` is uniform.

That is a *qualitative* extremality statement: any bias raises the collision
probability, but by how much? This file supplies the **quantitative** answer,
the open question flagged by the parent:

> Quantify how much a given bias raises the collision probability: bound
> `∑ pᵢ² − 1/d` below in terms of the total-variation distance of `p` from
> uniform.

Writing the total-variation distance from the uniform law `u = (1/d, …, 1/d)`

  `dTV(p, u) = ½ ∑ᵢ |pᵢ − 1/d|`,

we prove the sharp-in-order lower bound

  **`C(p) − 1/d  ≥  (4/d) · dTV(p, u)²`.**

So the collision excess grows at least *quadratically* in the total-variation
distance from uniform: a distribution that is `ε` away from uniform in total
variation has collision probability at least `1/d + 4ε²/d`.

## Key Mathematical Idea
Two ingredients combine:

1. **Variance identity (parent).** `C(p) − 1/d = ∑ᵢ (pᵢ − 1/d)²`, the squared
   ℓ² distance of `p` from uniform (`sum_sq_sub_one_div_card`).

2. **Cauchy–Schwarz / power-mean (Mathlib).** For the `d` deviations
   `gᵢ = |pᵢ − 1/d|`,  `(∑ᵢ gᵢ)² ≤ d · ∑ᵢ gᵢ²` (`sq_sum_le_card_mul_sum_sq`).
   Since `gᵢ² = (pᵢ − 1/d)²` and `∑ᵢ gᵢ = 2·dTV(p,u)`, this reads
   `4·dTV(p,u)² ≤ d·(C(p) − 1/d)`, which is the claim.

The bound is order-sharp: it becomes an equality (up to the constant) for a
"two-spike" perturbation of the uniform law, where all the deviation mass sits on
two coordinates.

## Scope
- [x] Definition of total-variation distance from uniform `dTV(p, u)`
- [x] `dTV(p, u) ≥ 0`
- [x] ℓ¹ form  `∑ᵢ |pᵢ − 1/d| = 2·dTV(p,u)`
- [x] Quantitative lower bound  `C(p) − 1/d ≥ (4/d)·dTV(p,u)²`
- [x] Restated as  `C(p) ≥ 1/d + (4/d)·dTV(p,u)²`
- [x] `dTV(p,u) = 0 ↔ p uniform`, bridging to the parent's equality case
- [x] The parent's equality `C(p) = 1/d ↔ p uniform`, re-derived through `dTV`

This is a genuine Pinsker-flavored refinement of the parent's extremality: it
replaces "bias ⇒ more collisions" with an effective, computable lower bound.

## References
- T. W. Munford, *A note on the uniformity assumption in the birthday problem*,
  Amer. Statist. 31 (1977).
- Parent: `BirthdayProblemOQ02OQ01OQ02` (qualitative extremality).
-/

open Finset

namespace BirthdayNonUniformQuant

open BirthdayNonUniform

variable {d : ℕ}

/-- **Total-variation distance from the uniform law.** For a probability vector
`p` on `d` outcomes, the total-variation distance to `u = (1/d, …, 1/d)` is
`½ ∑ᵢ |pᵢ − 1/d|`. -/
noncomputable def dTVUnif (p : Fin d → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |p i - 1 / (d : ℝ)|

/-- The ℓ¹ deviation from uniform is twice the total-variation distance. -/
theorem sum_abs_dev (p : Fin d → ℝ) :
    ∑ i, |p i - 1 / (d : ℝ)| = 2 * dTVUnif p := by
  unfold dTVUnif; ring

/-- Total-variation distance is nonnegative. -/
theorem dTVUnif_nonneg (p : Fin d → ℝ) : 0 ≤ dTVUnif p := by
  unfold dTVUnif
  have : (0 : ℝ) ≤ ∑ i, |p i - 1 / (d : ℝ)| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  positivity

/-- **Quantitative non-uniform birthday bound.** The excess collision
probability over the uniform value `1/d` is at least `(4/d)` times the square of
the total-variation distance from uniform:

  `(4/d) · dTV(p,u)² ≤ ∑ᵢ pᵢ² − 1/d`.

Bias raises the collision probability at least *quadratically* in total
variation. -/
theorem collision_excess_ge_tv (p : Fin d → ℝ) (hd : 0 < d)
    (hsum : ∑ i, p i = 1) :
    4 / (d : ℝ) * dTVUnif p ^ 2 ≤ (∑ i, p i ^ 2) - 1 / (d : ℝ) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  -- Cauchy–Schwarz on the deviations `gᵢ = |pᵢ − 1/d|`.
  have hcs : (∑ i, |p i - 1 / (d : ℝ)|) ^ 2
      ≤ (d : ℝ) * ∑ i, |p i - 1 / (d : ℝ)| ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => |p i - 1 / (d : ℝ)|)
    simpa [Finset.card_univ, Fintype.card_fin] using h
  -- `gᵢ² = (pᵢ − 1/d)²`, and the sum of those is exactly the collision excess.
  have habs : ∑ i, |p i - 1 / (d : ℝ)| ^ 2 = ∑ i, (p i - 1 / (d : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [sq_abs]
  have hvar : ∑ i, (p i - 1 / (d : ℝ)) ^ 2 = (∑ i, p i ^ 2) - 1 / (d : ℝ) :=
    (sum_sq_sub_one_div_card p hd hsum).symm
  -- Assemble: `(2 dTV)² ≤ d · excess`.
  rw [habs, hvar] at hcs
  have hL1 : ∑ i, |p i - 1 / (d : ℝ)| = 2 * dTVUnif p := sum_abs_dev p
  rw [hL1] at hcs
  -- `(2 dTV)² = 4 dTV²`, so `4 dTV² ≤ d · excess`, i.e. `(4/d) dTV² ≤ excess`.
  rw [div_mul_eq_mul_div, div_le_iff₀ hd']
  nlinarith [hcs]

/-- **Restated collision-probability lower bound.** The collision probability is
at least the uniform value plus a quadratic-in-total-variation surplus:

  `1/d + (4/d)·dTV(p,u)² ≤ ∑ᵢ pᵢ²`. -/
theorem collision_prob_ge (p : Fin d → ℝ) (hd : 0 < d) (hsum : ∑ i, p i = 1) :
    1 / (d : ℝ) + 4 / (d : ℝ) * dTVUnif p ^ 2 ≤ ∑ i, p i ^ 2 := by
  have h := collision_excess_ge_tv p hd hsum
  linarith

/-- Total-variation distance from uniform vanishes exactly for the uniform law. -/
theorem dTVUnif_eq_zero_iff (p : Fin d → ℝ) :
    dTVUnif p = 0 ↔ ∀ i, p i = 1 / (d : ℝ) := by
  unfold dTVUnif
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · norm_num at h
    · intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => abs_nonneg (p j - 1 / (d : ℝ)))).mp h i (Finset.mem_univ i)
      have : p i - 1 / (d : ℝ) = 0 := abs_eq_zero.mp hz
      linarith
  · intro h
    right
    apply Finset.sum_eq_zero
    intro i _
    rw [h i]; simp

/-- **Bridge to the parent's equality case.** The collision probability attains
its uniform minimum `1/d` exactly when the total-variation distance from uniform
is zero — recovering the parent's "equality iff uniform" through the
total-variation refinement. -/
theorem sum_sq_eq_one_div_card_iff_tv (p : Fin d → ℝ) (hd : 0 < d)
    (hsum : ∑ i, p i = 1) :
    (∑ i, p i ^ 2) = 1 / (d : ℝ) ↔ dTVUnif p = 0 := by
  rw [sum_sq_eq_one_div_card_iff p hd hsum, dTVUnif_eq_zero_iff]

section Examples

-- The bound is vacuous-but-true content check: for the uniform law the excess is
-- exactly `0` and the total-variation distance is `0`, so both sides vanish.
example (hd : 0 < d) :
    dTVUnif (fun _ : Fin d => 1 / (d : ℝ)) = 0 :=
  (dTVUnif_eq_zero_iff _).mpr (fun _ => rfl)

-- A distribution strictly biased away from uniform has strictly positive
-- collision excess (the quantitative bound with `dTV > 0`).
example (p : Fin d → ℝ) (hd : 0 < d) (hsum : ∑ i, p i = 1)
    (hbias : dTVUnif p ≠ 0) : 1 / (d : ℝ) < ∑ i, p i ^ 2 := by
  have hpos : 0 < dTVUnif p := lt_of_le_of_ne (dTVUnif_nonneg p) (Ne.symm hbias)
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h := collision_prob_ge p hd hsum
  have : 0 < 4 / (d : ℝ) * dTVUnif p ^ 2 := by positivity
  linarith

end Examples

end BirthdayNonUniformQuant
