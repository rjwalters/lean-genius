import Mathlib

/-
# Dini's Theorem — OQ-01-OQ-02-OQ-01-OQ-01: Exact Optimality of the Modulus `⌈log ε / log(1−δ)⌉`

## Research Problem: dini-theorem-oq-01-oq-02-oq-01-oq-01

The parent `DiniTheoremOQ01OQ02OQ01.lean` recovered uniform convergence of `xⁿ → 0` on the
compact subinterval `[0,1−δ]` with the explicit modulus

> `N(ε,δ) = ⌈log ε / log(1−δ)⌉₊`,

proving the *sufficiency* half: `N(ε,δ) ≤ n  ⟹  (1−δ)ⁿ ≤ ε` (`pow_lt_of_ceil_modulus`).

This file answers the parent's open question OQ-01:

> Is `N = ⌈log ε / log(1−δ)⌉` the **smallest** `N` with `(1−δ)^N ≤ ε`, or only the smallest
> under the log-threshold derivation?  Pin down the off-by-one from `Nat.le_ceil` exactly:
> show `(1−δ)^{N−1} > ε` (minimality) alongside the parent's `(1−δ)^N ≤ ε`.

**Answer — yes, it is exactly minimal, and the ceiling is forced.**  The key is to upgrade the
parent's one-way estimate to a clean *biconditional*.  Writing `r = 1−δ` (so `0 < r < 1`,
`log r < 0`):

* dividing the equivalent `m · log r ≤ log ε` by the negative `log r` reverses the inequality,
  giving the sharp real characterisation
  `(1−δ)^m ≤ ε  ⟺  log ε / log(1−δ) ≤ m`;
* `Nat.ceil_le` then converts this into the **discrete** characterisation
  `(1−δ)^m ≤ ε  ⟺  ⌈log ε / log(1−δ)⌉₊ ≤ m`.

From the biconditional everything about minimality is immediate:

* `N(ε,δ) = ⌈log ε / log(1−δ)⌉₊` is the **least** exponent with `(1−δ)^m ≤ ε`
  (`isLeast_modulus`);
* every strictly smaller exponent **fails**: `m < N ⟹ ε < (1−δ)^m` (`lt_pow_of_lt_modulus`);
* in particular the headline off-by-one `ε < (1−δ)^{N−1}` for `ε < 1` (`lt_pow_pred_modulus`),
  pinning the modulus exactly: the parent's `(1−δ)^N ≤ ε` cannot be improved to `N−1`.

## What is proved

* `pow_le_iff_log_le` — the sharp real biconditional `(1−δ)^m ≤ ε ⟺ log ε / log(1−δ) ≤ m`.
* `pow_le_iff_ceil_le` — the discrete biconditional `(1−δ)^m ≤ ε ⟺ ⌈log ε / log(1−δ)⌉₊ ≤ m`.
* `isLeast_modulus` — `⌈log ε / log(1−δ)⌉₊` is the least `m` with `(1−δ)^m ≤ ε`.
* `lt_pow_of_lt_modulus` — every smaller exponent is insufficient: `m < N ⟹ ε < (1−δ)^m`.
* `lt_pow_pred_modulus` — the exact off-by-one `ε < (1−δ)^{N−1}` (for `ε < 1`, where `N ≥ 1`).

Tags: analysis, dini, uniform-convergence, modulus, optimality, ceiling, logarithm, wiedijk
-/

namespace DiniTheoremOQ01OQ02OQ01OQ01

open Set Filter Topology

-- ============================================================
-- Part I: The sharp biconditional characterising `(1−δ)^m ≤ ε`
-- ============================================================

/-- **The sharp real characterisation.**  For `δ ∈ (0,1)` and `ε > 0`,
    `(1−δ)^m ≤ ε` holds **iff** `log ε / log(1−δ) ≤ m`.

    This upgrades the parent's one-way `pow_lt_of_log_modulus` to a biconditional: taking
    logarithms turns `(1−δ)^m ≤ ε` into `m · log(1−δ) ≤ log ε`, and since `log(1−δ) < 0`
    dividing by it reverses the inequality, yielding the threshold `m ≥ log ε / log(1−δ)`. -/
theorem pow_le_iff_log_le {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (m : ℕ) :
    (1 - δ) ^ m ≤ ε ↔ Real.log ε / Real.log (1 - δ) ≤ (m : ℝ) := by
  set r : ℝ := 1 - δ with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  -- compare via the strictly monotone `log`, then divide by the negative `log r`.
  rw [← Real.log_le_log_iff (pow_pos hr0 m) hε, Real.log_pow, div_le_iff_of_neg hlogr]

/-- **The discrete characterisation.**  For `δ ∈ (0,1)` and `ε > 0`,
    `(1−δ)^m ≤ ε` holds **iff** `⌈log ε / log(1−δ)⌉₊ ≤ m`.

    `Nat.ceil_le` converts the real threshold of `pow_le_iff_log_le` into the discrete one. -/
theorem pow_le_iff_ceil_le {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (m : ℕ) :
    (1 - δ) ^ m ≤ ε ↔ ⌈Real.log ε / Real.log (1 - δ)⌉₊ ≤ m := by
  rw [pow_le_iff_log_le hδ0 hδ1 hε, Nat.ceil_le]

-- ============================================================
-- Part II: Exact minimality of the modulus
-- ============================================================

/-- **The modulus is exactly minimal.**  `N(ε,δ) = ⌈log ε / log(1−δ)⌉₊` is the *least* natural
    number `m` for which `(1−δ)^m ≤ ε`: it satisfies the bound, and no smaller exponent does.
    Immediate from the discrete biconditional `pow_le_iff_ceil_le`. -/
theorem isLeast_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    IsLeast {m : ℕ | (1 - δ) ^ m ≤ ε} ⌈Real.log ε / Real.log (1 - δ)⌉₊ := by
  constructor
  · -- `(1−δ)^N ≤ ε`: apply the biconditional at `m = N` (reflexivity).
    rw [Set.mem_setOf_eq, pow_le_iff_ceil_le hδ0 hδ1 hε]
  · -- every member of the set dominates `N`.
    intro m hm
    rw [Set.mem_setOf_eq, pow_le_iff_ceil_le hδ0 hδ1 hε] at hm
    exact hm

/-- **Every smaller exponent is insufficient.**  For `m < N(ε,δ)` we have `ε < (1−δ)^m`: the
    uniform error has not yet dropped to `ε`.  This is the contrapositive of minimality. -/
theorem lt_pow_of_lt_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) {m : ℕ}
    (hm : m < ⌈Real.log ε / Real.log (1 - δ)⌉₊) :
    ε < (1 - δ) ^ m := by
  by_contra h
  push_neg at h
  rw [pow_le_iff_ceil_le hδ0 hδ1 hε] at h
  omega

/-- **The exact off-by-one.**  When `ε < 1` the modulus satisfies `N(ε,δ) ≥ 1`, and the
    predecessor *fails* the bound: `ε < (1−δ)^{N−1}`.  Together with the parent's
    `(1−δ)^N ≤ ε` this pins the modulus exactly — it cannot be lowered to `N−1`. -/
theorem lt_pow_pred_modulus {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) :
    ε < (1 - δ) ^ (⌈Real.log ε / Real.log (1 - δ)⌉₊ - 1) := by
  have hr0 : (0 : ℝ) < 1 - δ := by linarith
  have hr1 : 1 - δ < 1 := by linarith
  have hlogr : Real.log (1 - δ) < 0 := Real.log_neg hr0 hr1
  -- `0 < log ε / log(1−δ)` (a negative over a negative), so `N = ⌈·⌉₊ ≥ 1`.
  have hcpos : 0 < Real.log ε / Real.log (1 - δ) := by
    rw [div_pos_iff]
    exact Or.inr ⟨Real.log_neg hε hε1, hlogr⟩
  have hN1 : 1 ≤ ⌈Real.log ε / Real.log (1 - δ)⌉₊ := Nat.one_le_ceil_iff.mpr hcpos
  -- the predecessor is strictly below `N`, hence insufficient.
  exact lt_pow_of_lt_modulus hδ0 hδ1 hε (by omega)

#check @pow_le_iff_log_le
#check @pow_le_iff_ceil_le
#check @isLeast_modulus
#check @lt_pow_of_lt_modulus
#check @lt_pow_pred_modulus

/-
## Summary

Proved (0 sorries, 0 axioms — self-contained, imports only Mathlib):

* `pow_le_iff_log_le` — the sharp real biconditional `(1−δ)^m ≤ ε ⟺ log ε / log(1−δ) ≤ m`
  (upgrades the parent's one-way `pow_lt_of_log_modulus`).
* `pow_le_iff_ceil_le` — the discrete biconditional `(1−δ)^m ≤ ε ⟺ ⌈log ε / log(1−δ)⌉₊ ≤ m`.
* `isLeast_modulus` — `⌈log ε / log(1−δ)⌉₊` is the **least** exponent with `(1−δ)^m ≤ ε`.
* `lt_pow_of_lt_modulus` — every smaller exponent fails: `m < N ⟹ ε < (1−δ)^m`.
* `lt_pow_pred_modulus` — the exact off-by-one `ε < (1−δ)^{N−1}` for `ε < 1` (where `N ≥ 1`).

This answers `dini-theorem-oq-01-oq-02-oq-01` OQ-01: the modulus `N = ⌈log ε / log(1−δ)⌉` is
**exactly minimal** — the parent's `(1−δ)^N ≤ ε` holds, while `(1−δ)^{N−1} > ε`, so the
ceiling is forced and the off-by-one is sharp.  The whole optimality statement flows from one
biconditional obtained by dividing the log-linearised inequality by the negative `log(1−δ)`.
-/

end DiniTheoremOQ01OQ02OQ01OQ01
