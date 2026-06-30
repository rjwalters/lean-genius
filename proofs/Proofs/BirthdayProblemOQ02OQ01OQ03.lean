import Mathlib

/-
# The Monotone Birthday Paradox (OQ-02-OQ-01-OQ-03)

## What this proves

The birthday problem: with `k` people and `d` equally likely birthdays, the
probability that all birthdays are **distinct** is the falling-factorial product

  `P(all distinct) = ∏_{i<k} (1 − i/d)`,

and the **collision** probability (at least two share a birthday) is its
complement `1 − P(all distinct)`.

The defining intuition of the "paradox" is a *monotonicity* statement that the
classic two-sided exponential estimates (parent file OQ-02-OQ-01) never make
explicit: **adding people can only raise the collision probability.** This file
proves exactly that, with no axioms:

* `birthdayProduct_step_le` — one more person cannot raise `P(all distinct)`;
* `birthdayProduct_antitone` — `P(all distinct)` is non-increasing in `k`
  (for `k ≤ d`);
* `collisionProb_monotone` — the collision probability is non-decreasing in `k`;
* `collisionProb_one` / `collisionProb_nonneg` — it is `0` for a single person
  and a genuine probability (`0 ≤ · ≤ 1`).

The argument is elementary: `P(all distinct)` is a nonnegative product, and the
recurrence `P(k+1) = P(k)·(1 − k/d)` multiplies it by a factor in `[0,1]`, which
cannot increase it.

(The file is self-contained — it restates the standard `birthdayProduct` of the
OQ-02-OQ-01 lineage rather than importing it — because the monotonicity needs
only the product recurrence, not the exponential machinery.)
-/

namespace BirthdayProblemOQ02OQ01OQ03

open Finset

/-- `P(all k birthdays distinct)` among `d` equally likely days:
`∏_{i<k} (1 − i/d)`, the falling factorial `d^{\underline{k}} / d^k`. -/
noncomputable def birthdayProduct (k d : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (1 - (i : ℝ) / (d : ℝ))

/-- The collision probability: `1 − P(all distinct)`. -/
noncomputable def collisionProb (k d : ℕ) : ℝ :=
  1 - birthdayProduct k d

/-- **Product recurrence.** `P(k+1) = P(k) · (1 − k/d)`. -/
theorem birthdayProduct_succ (k d : ℕ) :
    birthdayProduct (k + 1) d = birthdayProduct k d * (1 - (k : ℝ) / d) := by
  unfold birthdayProduct
  rw [Finset.prod_range_succ]

/-- Each factor `1 − i/d` is nonnegative when `i ≤ d`. -/
theorem factor_nonneg {d : ℕ} (hd : 0 < d) {i : ℕ} (hi : i ≤ d) :
    0 ≤ 1 - (i : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : (i : ℝ) / d ≤ 1 := by rw [div_le_one hd']; exact_mod_cast hi
  linarith

/-- Each factor `1 − i/d` is at most `1`. -/
theorem factor_le_one (d : ℕ) (i : ℕ) : 1 - (i : ℝ) / d ≤ 1 := by
  have : 0 ≤ (i : ℝ) / d := by positivity
  linarith

/-- `P(all distinct)` is nonnegative for `k ≤ d + 1`. -/
theorem birthdayProduct_nonneg {k d : ℕ} (hd : 0 < d) (hk : k ≤ d + 1) :
    0 ≤ birthdayProduct k d := by
  apply Finset.prod_nonneg
  intro i hi
  rw [Finset.mem_range] at hi
  exact factor_nonneg hd (by omega)

/-- `P(all distinct) ≤ 1` for `k ≤ d + 1` (a product of factors in `[0,1]`). -/
theorem birthdayProduct_le_one {k d : ℕ} (hd : 0 < d) (hk : k ≤ d + 1) :
    birthdayProduct k d ≤ 1 := by
  apply Finset.prod_le_one
  · intro i hi
    rw [Finset.mem_range] at hi
    exact factor_nonneg hd (by omega)
  · intro i _
    exact factor_le_one d i

/-- **One-step monotonicity.** For `k ≤ d`, adding one more person cannot raise
`P(all distinct)`: `P(k+1) ≤ P(k)`. -/
theorem birthdayProduct_step_le {k d : ℕ} (hd : 0 < d) (hk : k ≤ d) :
    birthdayProduct (k + 1) d ≤ birthdayProduct k d := by
  rw [birthdayProduct_succ]
  have hnn : 0 ≤ birthdayProduct k d := birthdayProduct_nonneg hd (by omega)
  have hle1 : 1 - (k : ℝ) / d ≤ 1 := factor_le_one d k
  calc birthdayProduct k d * (1 - (k : ℝ) / d)
      ≤ birthdayProduct k d * 1 := mul_le_mul_of_nonneg_left hle1 hnn
    _ = birthdayProduct k d := mul_one _

/-- **`P(all distinct)` is non-increasing in the number of people** (for the
relevant range `k ≤ d`): if `j ≤ k ≤ d` then `P(k) ≤ P(j)`. -/
theorem birthdayProduct_antitone {d : ℕ} (hd : 0 < d) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ d) :
    birthdayProduct k d ≤ birthdayProduct j d := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_refl _
  | succ k hjk ih =>
      exact (birthdayProduct_step_le hd (by omega)).trans (ih (by omega))

/-- **The monotone birthday paradox.** The collision probability is
non-decreasing in the number of people: if `j ≤ k ≤ d` then
`collisionProb j d ≤ collisionProb k d`. More people ⇒ a collision is at least
as likely — never less. -/
theorem collisionProb_monotone {d : ℕ} (hd : 0 < d) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ d) :
    collisionProb j d ≤ collisionProb k d := by
  unfold collisionProb
  have := birthdayProduct_antitone hd hjk hk
  linarith

/-- With a single person there is never a collision: `collisionProb 1 d = 0`. -/
theorem collisionProb_one (d : ℕ) : collisionProb 1 d = 0 := by
  simp [collisionProb, birthdayProduct]

/-- The collision probability is a genuine probability: `0 ≤ collisionProb k d`. -/
theorem collisionProb_nonneg {k d : ℕ} (hd : 0 < d) (hk : k ≤ d + 1) :
    0 ≤ collisionProb k d := by
  unfold collisionProb
  have := birthdayProduct_le_one hd hk
  linarith

/-- The collision probability never exceeds `1`: `collisionProb k d ≤ 1`. -/
theorem collisionProb_le_one {k d : ℕ} (hd : 0 < d) (hk : k ≤ d + 1) :
    collisionProb k d ≤ 1 := by
  unfold collisionProb
  have := birthdayProduct_nonneg hd hk
  linarith

/-! ## Strict monotonicity and the pigeonhole certainty

The monotonicity above is non-strict.  In the genuinely interesting range
`1 ≤ k ≤ d` the all-distinct probability is in fact **strictly** positive and
**strictly** decreasing: each added person multiplies by a factor `1 − k/d` that
is strictly below `1`, so the collision probability strictly increases.  Past the
pigeonhole threshold (`k > d`) a collision is *certain*: the factor `1 − d/d = 0`
kills the product, giving `collisionProb = 1`. -/

/-- Each factor `1 − i/d` is **strictly** positive when `i < d`. -/
theorem factor_pos {d : ℕ} (hd : 0 < d) {i : ℕ} (hi : i < d) :
    0 < 1 - (i : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : (i : ℝ) / d < 1 := by rw [div_lt_one hd']; exact_mod_cast hi
  linarith

/-- `P(all distinct)` is **strictly positive** while there are no more people than
days (`k ≤ d`): every factor `1 − i/d` with `i < k ≤ d` is strictly positive. -/
theorem birthdayProduct_pos {k d : ℕ} (hd : 0 < d) (hk : k ≤ d) :
    0 < birthdayProduct k d := by
  apply Finset.prod_pos
  intro i hi
  rw [Finset.mem_range] at hi
  exact factor_pos hd (by omega)

/-- **One-step strict monotonicity.** For `0 < k ≤ d`, adding one more person
*strictly* lowers `P(all distinct)`: `P(k+1) < P(k)` (the factor `1 − k/d < 1`
multiplies a strictly positive quantity). -/
theorem birthdayProduct_step_lt {k d : ℕ} (hd : 0 < d) (hk0 : 0 < k) (hk : k ≤ d) :
    birthdayProduct (k + 1) d < birthdayProduct k d := by
  rw [birthdayProduct_succ]
  have hpos : 0 < birthdayProduct k d := birthdayProduct_pos hd hk
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hfac : 1 - (k : ℝ) / d < 1 := by
    have : 0 < (k : ℝ) / d := div_pos hkr hdr
    linarith
  calc birthdayProduct k d * (1 - (k : ℝ) / d)
      < birthdayProduct k d * 1 := mul_lt_mul_of_pos_left hfac hpos
    _ = birthdayProduct k d := mul_one _

/-- **`P(all distinct)` is strictly decreasing** on `1 ≤ · ≤ d`: if `0 < j < k ≤ d`
then `P(k) < P(j)`. -/
theorem birthdayProduct_strict_lt {d : ℕ} (hd : 0 < d) {j k : ℕ}
    (hj : 0 < j) (hjk : j < k) (hk : k ≤ d) :
    birthdayProduct k d < birthdayProduct j d :=
  lt_of_le_of_lt
    (birthdayProduct_antitone hd hjk hk)
    (birthdayProduct_step_lt hd hj (by omega))

/-- **The strict monotone birthday paradox.** For `0 < j < k ≤ d` the collision
probability *strictly* increases with the number of people:
`collisionProb j d < collisionProb k d`. -/
theorem collisionProb_strict_lt {d : ℕ} (hd : 0 < d) {j k : ℕ}
    (hj : 0 < j) (hjk : j < k) (hk : k ≤ d) :
    collisionProb j d < collisionProb k d := by
  unfold collisionProb
  have := birthdayProduct_strict_lt hd hj hjk hk
  linarith

/-- **Pigeonhole.** With more people than days (`d < k`), `P(all distinct) = 0`:
the factor `1 − d/d = 0` occurs in the product. -/
theorem birthdayProduct_eq_zero_of_gt {k d : ℕ} (hd : 0 < d) (hk : d < k) :
    birthdayProduct k d = 0 := by
  unfold birthdayProduct
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine Finset.prod_eq_zero (i := d) (Finset.mem_range.mpr hk) ?_
  rw [div_self hdr]; ring

/-- **Pigeonhole certainty.** With more people than days (`d < k`) a collision is
*certain*: `collisionProb k d = 1`. -/
theorem collisionProb_eq_one_of_gt {k d : ℕ} (hd : 0 < d) (hk : d < k) :
    collisionProb k d = 1 := by
  unfold collisionProb
  rw [birthdayProduct_eq_zero_of_gt hd hk]; ring

end BirthdayProblemOQ02OQ01OQ03
