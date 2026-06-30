/-
# Chebyshev–PNT Bridge OQ-05·OQ-01: The Two-Sided Chebyshev Bound for π(x)

The Prime Number Theorem states `π(x) ~ x / log x`. Decades before PNT,
Chebyshev proved the *order of magnitude* is correct: `π(x)` is squeezed
between two constant multiples of `x / log x`. Historically this two-sided
estimate is the pivotal pre-PNT result and the quantitative backbone of
Bertrand's postulate, Mertens' theorems, and prime density statements.

The two halves already live in the gallery, in separate files:

* **Lower half** — `ChebyshevPNTBridgeOQ05.primeCounting_mul_log_lower`:
  for every `m ≥ 2`,
  `⌊m/2⌋·log 4 − log(m+1) ≤ π(m)·log m`,
  i.e. the Chebyshev lower density `π(m)·log m / m ≥ log 2 − o(1)`.

* **Upper half** — `ChebyshevPNTBridgeOQ02.chebyshev_upper_real`
  (itself re-exporting `Erdos31PrimesDensity.primeCounting_le_chebyshev`):
  for every `N ≥ 2`,
  `π(N) ≤ 2·N·log 4 / log N + √N + 1`,
  i.e. the Chebyshev upper density `π(N)·log N / N ≤ 2·log 4 + o(1)`.

This file packages the two halves into single citable theorems, the natural
API other gallery entries should depend on.

## Results

* **`primeCounting_two_sided_exact`** — the raw conjunction of the two parent
  bounds, valid for every `m ≥ 2` with their exact error terms.

* **`primeCounting_le_order`** — a clean *order* upper bound with one explicit
  constant: for `m ≥ 2`,
  `π(m) ≤ (2·log 4 + 4)·(m / log m)`.
  The `+4` uniformly absorbs the `√m + 1` error term over the whole range
  `m ≥ 2` (using `log m ≤ 2√m` and `√m ≤ m`).

* **`primeCounting_ge_order`** — a clean *order* lower bound with one explicit
  constant and threshold: for `m ≥ 65`,
  `(2/5)·(m / log m) ≤ π(m)`.
  The threshold and the modest constant `2/5 < log 2` come from absorbing the
  `−log(m+1)` and `⌊m/2⌋ vs m/2` losses (using `log(m+1) ≤ 2√(m+1) ≤ m/4` for
  `m ≥ 65` and the explicit lower bound `log 2 > 0.6931471803`).

* **`chebyshev_order_two_sided`** — the headline packaged statement: for
  `m ≥ 65`,
  `(2/5)·(m / log m) ≤ π(m) ≤ (2·log 4 + 4)·(m / log m)`,
  the single "`π(x)` is of order `x / log x`" lemma.

Everything is derived from the two parent results plus elementary `Real.log` /
`Real.sqrt` estimates; the whole dependency chain
(`ChebyshevPNTBridge`, `ChebyshevPNTBridgeOQ02`, `ChebyshevPNTBridgeOQ05`,
`Erdos31PrimesDensity`) is `0 sorries, 0 axioms`, so this file is too.
`0 sorries, 0 axioms`.
-/

import Mathlib
import Proofs.ChebyshevPNTBridgeOQ02
import Proofs.ChebyshevPNTBridgeOQ05

namespace ChebyshevPNTBridgeOQ05OQ01

open Nat

/-! ═══════════════════════════════════════════════════════════════════════════════
PART 0: ELEMENTARY LOG/SQRT HELPER

A single clean estimate `log x ≤ 2√x` (for `x ≥ 0`) powers both the uniform
absorption of the upper-bound error term `√m + 1` and the lower-bound error
term `log(m+1)`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- For every `x ≥ 0`, `log x ≤ 2·√x`. Obtained from `log t ≤ t − 1` applied to
`t = √x`, since `log x = 2·log √x ≤ 2·(√x − 1) ≤ 2·√x`. -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp
  · have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hlog_sqrt : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    have hmul : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
    have hsplit : Real.log x = 2 * Real.log (Real.sqrt x) := by
      conv_lhs => rw [← hmul]
      rw [Real.log_mul (ne_of_gt hsqrt_pos) (ne_of_gt hsqrt_pos)]; ring
    rw [hsplit]; linarith

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: THE EXACT TWO-SIDED BOUND (ALL m ≥ 2)

The literal conjunction of the two parent results, with their exact error
terms. This is the most precise consolidated statement.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Two-sided Chebyshev bound, exact form.** For every `m ≥ 2`,

    (⌊m/2⌋·log 4 − log(m+1)) / log m  ≤  π(m)  ≤  2·m·log 4 / log m + √m + 1.

The lower half is `ChebyshevPNTBridgeOQ05.primeCounting_ge_div_log`; the upper
half is `ChebyshevPNTBridgeOQ02.chebyshev_upper_real`. -/
theorem primeCounting_two_sided_exact (m : ℕ) (hm : 2 ≤ m) :
    ((m / 2 : ℕ) * Real.log 4 - Real.log (m + 1)) / Real.log m
        ≤ (Nat.primeCounting m : ℝ)
      ∧ (Nat.primeCounting m : ℝ)
        ≤ 2 * m * Real.log 4 / Real.log m + Nat.sqrt m + 1 :=
  ⟨ChebyshevPNTBridgeOQ05.primeCounting_ge_div_log m hm,
   ChebyshevPNTBridgeOQ02.chebyshev_upper_real m hm⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: CLEAN ORDER UPPER BOUND (ALL m ≥ 2)

`π(m) ≤ (2·log 4 + 4)·(m / log m)`. The `√m + 1` error term is absorbed into
the `+4` uniformly over `m ≥ 2`, via `log m ≤ 2√m` and `√m ≤ m`:
`(√m + 1)·log m ≤ (√m + 1)·2√m = 2m + 2√m ≤ 4m`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Chebyshev order upper bound.** For every `m ≥ 2`,
`π(m) ≤ (2·log 4 + 4)·(m / log m)`. -/
theorem primeCounting_le_order (m : ℕ) (hm : 2 ≤ m) :
    (Nat.primeCounting m : ℝ) ≤ (2 * Real.log 4 + 4) * ((m : ℝ) / Real.log m) := by
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hupper := ChebyshevPNTBridgeOQ02.chebyshev_upper_real m hm
  -- log m ≤ 2√m and √m ≤ m
  have hlogm_le : Real.log m ≤ 2 * Real.sqrt m := log_le_two_mul_sqrt (by positivity)
  have hsqrt_le : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
    have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm_real, sq_nonneg ((m : ℝ) - 1)]
    have h : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt hmm
    rwa [Real.sqrt_sq (by positivity)] at h
  have hsqrt_nonneg : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  -- (√m + 1)·log m ≤ 4m
  have htail : (Real.sqrt (m : ℝ) + 1) * Real.log m ≤ 4 * (m : ℝ) := by
    have h1 : (Real.sqrt (m : ℝ) + 1) * Real.log m
        ≤ (Real.sqrt (m : ℝ) + 1) * (2 * Real.sqrt m) :=
      mul_le_mul_of_nonneg_left hlogm_le (by positivity)
    have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    nlinarith [h1, hsq, hsqrt_le, hsqrt_nonneg]
  -- hence √m + 1 ≤ 4·(m / log m)
  have htail2 : Real.sqrt (m : ℝ) + 1 ≤ 4 * ((m : ℝ) / Real.log m) := by
    rw [← mul_div_assoc, le_div_iff₀ hlogm_pos]; linarith [htail]
  -- expand the target constant and combine
  have hexpand : (2 * Real.log 4 + 4) * ((m : ℝ) / Real.log m)
      = 2 * (m : ℝ) * Real.log 4 / Real.log m + 4 * ((m : ℝ) / Real.log m) := by ring
  rw [hexpand]
  -- π(m) ≤ 2 m log4/log m + (√m + 1) ≤ 2 m log4/log m + 4·(m/log m)
  have hsqrt_cast : (↑(Nat.sqrt m) : ℝ) ≤ Real.sqrt (m : ℝ) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt m))]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' m)
  linarith [hupper, htail2, hsqrt_cast]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: CLEAN ORDER LOWER BOUND (m ≥ 65)

`(2/5)·(m / log m) ≤ π(m)`. From the parent lower bound
`⌊m/2⌋·log 4 − log(m+1) ≤ π(m)·log m`, using `⌊m/2⌋·log 4 ≥ (m−1)·log 2`
(since `log 4 = 2·log 2`) and the absorption `log(m+1) ≤ 2√(m+1) ≤ m/4`
valid for `m ≥ 65`. With `log 2 > 0.6931471803` the residual
`(m−1)·log 2 − m/4 ≥ (2/5)·m` for all `m ≥ 65`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Chebyshev order lower bound.** For every `m ≥ 65`,
`(2/5)·(m / log m) ≤ π(m)`. -/
theorem primeCounting_ge_order (m : ℕ) (hm : 65 ≤ m) :
    (2 / 5 : ℝ) * ((m : ℝ) / Real.log m) ≤ (Nat.primeCounting m : ℝ) := by
  have hm2 : 2 ≤ m := by omega
  have hm_real : (65 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlower := ChebyshevPNTBridgeOQ05.primeCounting_mul_log_lower m hm2
  -- log(m+1) ≤ m/4
  have hlog_m1 : Real.log ((m : ℝ) + 1) ≤ (m : ℝ) / 4 := by
    have h1 : Real.log ((m : ℝ) + 1) ≤ 2 * Real.sqrt ((m : ℝ) + 1) :=
      log_le_two_mul_sqrt (by positivity)
    have h2 : Real.sqrt ((m : ℝ) + 1) ≤ (m : ℝ) / 8 := by
      have hsq : (m : ℝ) + 1 ≤ ((m : ℝ) / 8) ^ 2 := by
        nlinarith [hm_real, sq_nonneg ((m : ℝ) - 65)]
      have hb : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (((m : ℝ) / 8) ^ 2) :=
        Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity)] at hb
    linarith
  -- log 4 = 2 log 2
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- m ≤ 2⌊m/2⌋ + 1
  have hfloor : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
    have h : m ≤ 2 * (m / 2) + 1 := by omega
    calc (m : ℝ) ≤ ((2 * (m / 2) + 1 : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by push_cast; ring
  have hlog2_lb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- (2/5)·m ≤ ⌊m/2⌋·log 4 − log(m+1)
  have hkey : (2 / 5 : ℝ) * (m : ℝ)
      ≤ ((m / 2 : ℕ) : ℝ) * Real.log 4 - Real.log ((m : ℝ) + 1) := by
    have h2q : (m : ℝ) - 1 ≤ 2 * ((m / 2 : ℕ) : ℝ) := by linarith [hfloor]
    have hlog2_pos : (0 : ℝ) < Real.log 2 := by linarith [hlog2_lb]
    have hprod : ((m : ℝ) - 1) * Real.log 2 ≤ 2 * ((m / 2 : ℕ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h2q hlog2_pos.le
    rw [hlog4]
    have hprod2 : (0 : ℝ) ≤ ((m : ℝ) - 1) * (Real.log 2 - 0.6931471803) :=
      mul_nonneg (by linarith [hm_real]) (by linarith [hlog2_lb])
    nlinarith [hprod, hlog_m1, hlog2_lb, hm_real, hprod2]
  -- combine with the parent lower bound and divide by log m
  have hcomb : (2 / 5 : ℝ) * (m : ℝ) ≤ (Nat.primeCounting m : ℝ) * Real.log m :=
    le_trans hkey hlower
  rw [← mul_div_assoc, div_le_iff₀ hlogm_pos]
  linarith [hcomb]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: THE PACKAGED TWO-SIDED ORDER BOUND

The headline statement: `π(x)` is of order `x / log x`, as a single lemma with
explicit constants `c₁ = 2/5`, `c₂ = 2·log 4 + 4` and threshold `x₀ = 65`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Two-sided Chebyshev order bound (headline).** For every `m ≥ 65`,

    (2/5)·(m / log m)  ≤  π(m)  ≤  (2·log 4 + 4)·(m / log m).

This is the single "`π(x)` is of order `x / log x`" lemma, with explicit
constants `0 < 2/5 ≤ 2·log 4 + 4` and threshold `65`. -/
theorem chebyshev_order_two_sided (m : ℕ) (hm : 65 ≤ m) :
    (2 / 5 : ℝ) * ((m : ℝ) / Real.log m) ≤ (Nat.primeCounting m : ℝ)
      ∧ (Nat.primeCounting m : ℝ) ≤ (2 * Real.log 4 + 4) * ((m : ℝ) / Real.log m) :=
  ⟨primeCounting_ge_order m hm, primeCounting_le_order m (by omega)⟩

#check @primeCounting_two_sided_exact  -- exact two-sided, all m ≥ 2
#check @primeCounting_le_order          -- order upper bound, all m ≥ 2
#check @primeCounting_ge_order          -- order lower bound, m ≥ 65
#check @chebyshev_order_two_sided       -- packaged two-sided order bound

end ChebyshevPNTBridgeOQ05OQ01
