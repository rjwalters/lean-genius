import Mathlib
import Proofs.SylvesterSequenceOQ02

/-
# Sylvester's sequence OQ-02-OQ-01: the exact tail of the reciprocal series

Sylvester's sequence is `a₀ = 2`, `a_{n+1} = aₙ² - aₙ + 1`, giving `2, 3, 7, 43, 1807, …`.
The parent entry `SylvesterSequenceOQ02` proves the closed-form **partial** sum
`∑_{k≤n} 1/aₖ = 1 - 1/(a_{n+1} - 1)`, that the full series `∑' k, 1/aₖ = 1`, and that the
error term `1/(a_{n+1}-1) → 0`. Its first listed open question asks whether the
convergence can be made *quantitative*: an exact formula for the remainder after `n+1`
terms. This file answers that — and more sharply than an inequality.

We prove the **exact tail identity**: the remainder of the infinite series after the
first `n+1` terms is *exactly* `1/(a_{n+1}-1)`,

* `syl_tail_hasSum`  : `HasSum (fun m => 1/a_{m+(n+1)}) (1/(a_{n+1}-1))`,
* `syl_tsum_tail`    : `∑' m, 1/a_{m+(n+1)} = 1/(a_{n+1}-1)`,
* `syl_remainder_eq_tail` : `1 - ∑_{k≤n} 1/aₖ = ∑' m, 1/a_{m+(n+1)}` (remainder = tail),

together with the underlying **product structure** that makes the tail so small:

* `syl_prod_eq_pred` : `∏_{k≤n} aₖ = a_{n+1} - 1`  (so `a_{n+1} = 1 + ∏_{k≤n} aₖ`), and
* `syl_tsum_tail_eq_inv_prod` : `∑' m, 1/a_{m+(n+1)} = 1 / ∏_{k≤n} aₖ`.

The last form is the precise sense in which Sylvester's greedy Egyptian-fraction expansion
of `1` converges as fast as possible: the entire infinite tail past `aₙ` is no larger than
the reciprocal of the *product* of all preceding terms (which itself grows doubly
exponentially).

The proof reuses the parent's partial-sum closed form and `HasSum` statement; the tail is
extracted by `hasSum_nat_add_iff`, which peels the first `n+1` terms off a convergent
series. The product identity is a one-line induction on the recurrence
`a_{n+1}-1 = aₙ(aₙ-1)`.

No axioms, no sorries.
-/

namespace SylvesterSequenceOQ02OQ01

open SylvesterSequenceOQ02

/-! ## The product structure `a_{n+1} - 1 = ∏_{k≤n} aₖ` -/

/-- **Euclid/Sylvester product identity (over `ℤ`).** The predecessor of the next term is
the product of all terms so far: `∏_{k≤n} aₖ = a_{n+1} - 1`. Proved by induction from the
recurrence `a_{n+1}-1 = aₙ² - aₙ = aₙ(aₙ-1)`: multiplying the running product by `aₙ` is
exactly the step from `aₙ-1` to `a_{n+1}-1`. -/
theorem syl_prod_eq_pred_int (n : ℕ) :
    ∏ k ∈ Finset.range (n + 1), (syl k : ℤ) = (syl (n + 1) : ℤ) - 1 := by
  induction n with
  | zero =>
    simp [show syl 0 = 2 from rfl, show syl 1 = 3 from rfl]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, syl_cast_succ (m + 1)]
    ring

/-- The product identity in `ℝ`: `∏_{k≤n} aₖ = a_{n+1} - 1`. -/
theorem syl_prod_eq_pred_real (n : ℕ) :
    ∏ k ∈ Finset.range (n + 1), (syl k : ℝ) = (syl (n + 1) : ℝ) - 1 := by
  have h := syl_prod_eq_pred_int n
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h2
  exact h2

/-- Equivalent `ℕ` phrasing: each term is one more than the product of its predecessors,
`a_{n+1} = 1 + ∏_{k≤n} aₖ` (the defining property of the greedy Euclid/Sylvester growth). -/
theorem syl_succ_eq_prod_add_one (n : ℕ) :
    syl (n + 1) = (∏ k ∈ Finset.range (n + 1), syl k) + 1 := by
  have h := syl_prod_eq_pred_int n
  have hcast : (∏ k ∈ Finset.range (n + 1), (syl k : ℤ))
      = ((∏ k ∈ Finset.range (n + 1), syl k : ℕ) : ℤ) := by push_cast; ring
  rw [hcast] at h
  have hpos : 1 ≤ syl (n + 1) := le_trans (by norm_num) (two_le_syl (n + 1))
  omega

/-! ## The exact tail of the reciprocal series -/

/-- **Exact tail identity (`HasSum` form).** The remainder of the reciprocal series after
the first `n+1` terms is summable with sum exactly `1/(a_{n+1}-1)`:
`HasSum (fun m => 1/a_{m+(n+1)}) (1/(a_{n+1}-1))`.

Obtained by peeling the first `n+1` terms off the convergent full series
(`syl_reciprocal_hasSum`, value `1`) with `hasSum_nat_add_iff`, then identifying the leading
block with the parent's partial-sum closed form `1 - 1/(a_{n+1}-1)`. -/
theorem syl_tail_hasSum (n : ℕ) :
    HasSum (fun m => (1 : ℝ) / (syl (m + (n + 1)) : ℝ))
      (1 / ((syl (n + 1) : ℝ) - 1)) := by
  rw [hasSum_nat_add_iff (f := fun j => (1 : ℝ) / (syl j : ℝ)) (n + 1)]
  have hps : (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (syl i : ℝ))
      = 1 - 1 / ((syl (n + 1) : ℝ) - 1) := syl_real_partial_sum n
  rw [hps]
  have key : (1 : ℝ) / ((syl (n + 1) : ℝ) - 1) + (1 - 1 / ((syl (n + 1) : ℝ) - 1)) = 1 := by
    ring
  rw [key]
  exact syl_reciprocal_hasSum

/-- **Exact tail identity (`tsum` form):** `∑' m, 1/a_{m+(n+1)} = 1/(a_{n+1}-1)`. The
infinite tail past the first `n+1` terms is precisely `1/(a_{n+1}-1)`. -/
theorem syl_tsum_tail (n : ℕ) :
    ∑' m, (1 : ℝ) / (syl (m + (n + 1)) : ℝ) = 1 / ((syl (n + 1) : ℝ) - 1) :=
  (syl_tail_hasSum n).tsum_eq

/-- **Remainder equals tail.** The gap between `1` and the `(n+1)`-term partial sum is the
infinite tail — both equal `1/(a_{n+1}-1)`. This is the "quantitative convergence" statement
the parent entry leaves open: the error after `n+1` terms is given *exactly*, not just
bounded. -/
theorem syl_remainder_eq_tail (n : ℕ) :
    1 - ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (syl k : ℝ)
      = ∑' m, (1 : ℝ) / (syl (m + (n + 1)) : ℝ) := by
  rw [syl_tsum_tail n, syl_real_partial_sum n]
  ring

/-- **The tail as a reciprocal product:** `∑' m, 1/a_{m+(n+1)} = 1 / ∏_{k≤n} aₖ`. Combining
the tail identity with the product structure exhibits the doubly-exponential speed of
convergence: the entire infinite remainder past `aₙ` is the reciprocal of the product of all
preceding terms. -/
theorem syl_tsum_tail_eq_inv_prod (n : ℕ) :
    ∑' m, (1 : ℝ) / (syl (m + (n + 1)) : ℝ)
      = 1 / ∏ k ∈ Finset.range (n + 1), (syl k : ℝ) := by
  rw [syl_tsum_tail n, syl_prod_eq_pred_real n]

/-- Sanity check: the tail after the first term (`n = 0`) is `1/(a₁-1) = 1/2`, matching
`1 - 1/a₀ = 1 - 1/2`. -/
example : ∑' m, (1 : ℝ) / (syl (m + 1) : ℝ) = 1 / 2 := by
  have h := syl_tsum_tail 0
  norm_num [show syl 1 = 3 from rfl] at h
  simpa using h

end SylvesterSequenceOQ02OQ01
