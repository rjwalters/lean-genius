import Mathlib

/-
# Dini's Theorem — OQ-01-OQ-02-OQ-01-OQ-01: Optimality of the Dini Modulus ⌈log ε / log(1−δ)⌉

## Research Problem: dini-theorem-oq-01-oq-02-oq-01-oq-01

The parent file `DiniTheoremOQ01OQ02OQ01.lean` established that on the compact subinterval
`[0, 1−δ]` the witness sequence `fₙ(x) = xⁿ` converges to `0` uniformly, with the explicit
modulus

    N(ε, δ) = ⌈log ε / log(1−δ)⌉₊ ,

in the sense that `n ≥ N(ε,δ) ⟹ (1−δ)ⁿ ≤ ε` (`pow_lt_of_ceil_modulus`).  That is a
*sufficiency* statement: the modulus is large enough.

This file answers the parent's open question OQ-01:

> Is `N = ⌈log ε / log(1−δ)⌉₊` the **smallest** `N` with `(1−δ)^N ≤ ε`, or only the smallest
> under the particular log-threshold derivation?  Pin down the off-by-one from `Nat.ceil`
> exactly: prove the matching minimality `(1−δ)^{N-1} > ε`.

**Answer — the modulus is exactly optimal, not merely sufficient.**  Writing `r = 1−δ ∈ (0,1)`,
the key is the *sharp* characterisation

    (1−δ)ⁿ ≤ ε   ⟺   log ε / log(1−δ) ≤ n   ⟺   ⌈log ε / log(1−δ)⌉₊ ≤ n .

The first equivalence is genuine (both directions), because the monotone bijection
`t ↦ exp(t)` and the *order-reversing* division by `log(1−δ) < 0` turn the inequality on
powers into an inequality on exponents with **no slack**.  The second is the defining property
of `Nat.ceil`.  Combining the two:

* `isLeast_modulus` — `N(ε,δ) = ⌈log ε / log(1−δ)⌉₊` is the **least** element of the solution
  set `{ n : (1−δ)ⁿ ≤ ε }`.  This is the precise optimality statement: the parent's modulus is
  not just *a* working `N`, it is *the smallest* one.
* `lt_pow_of_lt_modulus` — strict minimality: every `n < N` *fails*, `(1−δ)ⁿ > ε`.
* `lt_pow_pred_modulus` — the explicit off-by-one the parent left open: for `ε ∈ (0,1)`,
  `N ≥ 1` and `(1−δ)^{N-1} > ε`, the matching lower bound that proves `N` cannot be reduced by
  even one.

## What is proved

* `pow_le_iff_log_div` — the sharp real characterisation
  `(1−δ)ⁿ ≤ ε ↔ log ε / log(1−δ) ≤ n` (both directions, no slack).
* `pow_le_iff_ceil_le` — its natural-number form
  `(1−δ)ⁿ ≤ ε ↔ ⌈log ε / log(1−δ)⌉₊ ≤ n`, fusing the parent's sufficiency with the new
  minimality into a single biconditional.
* `isLeast_modulus` — **the headline**: `N(ε,δ)` is the least `n` with `(1−δ)ⁿ ≤ ε`.
* `lt_pow_of_lt_modulus` — strict minimality for every smaller exponent.
* `one_le_modulus` — for `ε ∈ (0,1)`, `N(ε,δ) ≥ 1`.
* `lt_pow_pred_modulus` — the off-by-one lower bound `(1−δ)^{N-1} > ε`.

Tags: analysis, dini, uniform-convergence, modulus, optimality, isleast, sharp-bound, wiedijk
-/

namespace DiniTheoremOQ01OQ02OQ01OQ01

open Set

-- ============================================================
-- Part I: The sharp characterisation — no slack in either direction
-- ============================================================

/-- **The sharp real characterisation.**  For `δ ∈ (0,1)` and `ε > 0`,

    `(1−δ)ⁿ ≤ ε  ↔  log ε / log(1−δ) ≤ n`.

    Both directions hold: exponentiating `t ↦ exp(t)` is an order-isomorphism, and dividing by
    `log(1−δ) < 0` reverses the order *exactly*, so the power inequality and the exponent
    inequality are equivalent with no loss.  The parent file proved only the `⟸` direction
    (`pow_lt_of_log_modulus`); the `⟹` direction is what makes the modulus *minimal*. -/
theorem pow_le_iff_log_div {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (n : ℕ) :
    (1 - δ) ^ n ≤ ε ↔ Real.log ε / Real.log (1 - δ) ≤ (n : ℝ) := by
  set r : ℝ := 1 - δ with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hpow_pos : (0 : ℝ) < r ^ n := pow_pos hr0 n
  -- Replace the division by `log r < 0` with the equivalent product inequality.
  rw [div_le_iff_of_neg hlogr]
  -- Goal: `r ^ n ≤ ε ↔ (n : ℝ) * log r ≤ log ε`.
  constructor
  · -- `⟹` (the new, minimality-giving direction): take logs.
    intro h
    have h2 : Real.exp ((n : ℝ) * Real.log r) ≤ Real.exp (Real.log ε) := by
      rw [← Real.log_pow, Real.exp_log hpow_pos, Real.exp_log hε]; exact h
    exact Real.exp_le_exp.mp h2
  · -- `⟸` (sufficiency, as in the parent): exponentiate.
    intro h
    rw [← Real.exp_log hpow_pos, ← Real.exp_log hε]
    apply Real.exp_le_exp.mpr
    rwa [Real.log_pow]

/-- **The natural-number characterisation.**  Fusing minimality with the parent's sufficiency,

    `(1−δ)ⁿ ≤ ε  ↔  ⌈log ε / log(1−δ)⌉₊ ≤ n`.

    The right-hand side is exactly "`n` reaches the modulus `N(ε,δ)`", so this single
    biconditional says the modulus threshold is *sharp*. -/
theorem pow_le_iff_ceil_le {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (n : ℕ) :
    (1 - δ) ^ n ≤ ε ↔ ⌈Real.log ε / Real.log (1 - δ)⌉₊ ≤ n := by
  rw [pow_le_iff_log_div hδ0 hδ1 hε]
  exact (Nat.ceil_le).symm

-- ============================================================
-- Part II: Optimality — N is the LEAST working exponent
-- ============================================================

/-- **The optimality theorem.**  `N(ε,δ) = ⌈log ε / log(1−δ)⌉₊` is the *least* natural number
    `n` for which `(1−δ)ⁿ ≤ ε`.

    This upgrades the parent's `pow_lt_of_ceil_modulus` (which showed only that `N` *works*) to
    the statement that `N` is the smallest working modulus — there is no smaller one. -/
theorem isLeast_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    IsLeast {n : ℕ | (1 - δ) ^ n ≤ ε} ⌈Real.log ε / Real.log (1 - δ)⌉₊ := by
  constructor
  · -- `N` itself works (membership): apply the characterisation at `n = N`.
    exact (pow_le_iff_ceil_le hδ0 hδ1 hε _).mpr (le_refl _)
  · -- `N` is a lower bound: any working `m` satisfies `N ≤ m`.
    intro m hm
    exact (pow_le_iff_ceil_le hδ0 hδ1 hε m).mp hm

/-- **Strict minimality.**  Every exponent *below* the modulus fails: if `n < N(ε,δ)` then
    `(1−δ)ⁿ > ε`.  (Contrapositive of the lower-bound half of `isLeast_modulus`.) -/
theorem lt_pow_of_lt_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) {n : ℕ}
    (hn : n < ⌈Real.log ε / Real.log (1 - δ)⌉₊) :
    ε < (1 - δ) ^ n := by
  by_contra h
  push_neg at h
  exact absurd ((pow_le_iff_ceil_le hδ0 hδ1 hε n).mp h) (not_le.mpr hn)

-- ============================================================
-- Part III: The explicit off-by-one (1−δ)^{N-1} > ε
-- ============================================================

/-- For `ε ∈ (0,1)` the modulus is at least `1`: since `log ε < 0` and `log(1−δ) < 0`, the
    threshold `log ε / log(1−δ)` is strictly positive, so its ceiling is `≥ 1`. -/
theorem one_le_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 ≤ ⌈Real.log ε / Real.log (1 - δ)⌉₊ := by
  have hpos : 0 < ⌈Real.log ε / Real.log (1 - δ)⌉₊ := by
    rw [Nat.ceil_pos]
    -- ratio of two negatives is positive
    exact div_pos_iff.mpr (Or.inr ⟨Real.log_neg hε0 hε1, Real.log_neg (by linarith) (by linarith)⟩)
  omega

/-- **The explicit off-by-one — the parent's open lower bound.**  For `ε ∈ (0,1)`, the
    predecessor of the modulus already *fails*:

    `(1−δ)^{N-1} > ε`,   where `N = ⌈log ε / log(1−δ)⌉₊`.

    Together with the parent's `(1−δ)^N ≤ ε` this pins the modulus down exactly: `N` is the
    unique threshold at which `(1−δ)ⁿ` first drops to `≤ ε`. -/
theorem lt_pow_pred_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ε < (1 - δ) ^ (⌈Real.log ε / Real.log (1 - δ)⌉₊ - 1) := by
  apply lt_pow_of_lt_modulus hδ0 hδ1 hε0
  have h1 := one_le_modulus hδ0 hδ1 hε0 hε1
  omega

#check @pow_le_iff_log_div
#check @pow_le_iff_ceil_le
#check @isLeast_modulus
#check @lt_pow_of_lt_modulus
#check @one_le_modulus
#check @lt_pow_pred_modulus

/-
## Summary

Proved (0 sorries, 0 axioms — self-contained, imports only Mathlib):

* `pow_le_iff_log_div` — the **sharp** characterisation `(1−δ)ⁿ ≤ ε ↔ log ε / log(1−δ) ≤ n`
  (both directions, no slack); the parent proved only `⟸`.
* `pow_le_iff_ceil_le` — its natural-number form `(1−δ)ⁿ ≤ ε ↔ ⌈log ε / log(1−δ)⌉₊ ≤ n`.
* `isLeast_modulus` — **the optimality theorem**: `N(ε,δ) = ⌈log ε / log(1−δ)⌉₊` is the *least*
  `n` with `(1−δ)ⁿ ≤ ε`.
* `lt_pow_of_lt_modulus` — strict minimality: every `n < N` fails, `(1−δ)ⁿ > ε`.
* `one_le_modulus` / `lt_pow_pred_modulus` — the explicit off-by-one `(1−δ)^{N-1} > ε`, the
  matching lower bound the parent left open.

This answers `dini-theorem-oq-01-oq-02-oq-01` OQ-01: the modulus
`N(ε,δ) = ⌈log ε / log(1−δ)⌉₊` is not merely sufficient but **optimal** — the smallest `N` with
`(1−δ)^N ≤ ε` — and the bound is sharp, the predecessor `N-1` already failing with
`(1−δ)^{N-1} > ε`.
-/

end DiniTheoremOQ01OQ02OQ01OQ01
