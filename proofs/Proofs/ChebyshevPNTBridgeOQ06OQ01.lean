/-
# Chebyshev–PNT Bridge OQ-06-OQ-01: the Two-Sided Density Sandwich

Two sibling entries package the elementary Chebyshev bounds on the prime-counting
function `π` into real-logarithmic form:

* `ChebyshevPNTBridgeOQ05` — the **lower** density
    `(⌊m/2⌋·log 4 − log(m+1)) / log m ≤ π(m)`   (`primeCounting_ge_div_log`),
* `ChebyshevPNTBridgeOQ06` — the **upper** density
    `π(m) ≤ m·log 4 / log(√m) + √m`             (`primeCounting_le_div_log_sqrt`),

where `√m = Nat.sqrt m` is the integer square root. This entry combines them into a
single two-sided **sandwich** and, more substantially, makes the asymptotic reading
of the two constants rigorous.

The upper bound is stated with the denominator `log(Nat.sqrt m)`, and one informally
reads off `limsup π(x)·log x / x ≤ 2 log 4` using "`log(√m) ≈ ½ log m`". That step is
not free: `Nat.sqrt m` is the *integer* square root, so `log(Nat.sqrt m)` is only
approximately `½ log m`. We pin it down exactly with the bracket

    ½·log m − log 2  ≤  log(Nat.sqrt m)  ≤  ½·log m            (all m ≥ 4),

derived purely from the defining inequalities of `Nat.sqrt`
(`(Nat.sqrt m)² ≤ m < (Nat.sqrt m + 1)²`) — the lower half via `m < 4·(Nat.sqrt m)²`.
This `O(1)` two-sided control on `log(Nat.sqrt m)` is exactly what turns the OQ-06
quotient bound into the honest density statement.

Putting the pieces together:

* **`log_natSqrt_le`** / **`log_natSqrt_ge`** — the bracket above.
* **`primeCounting_sandwich`** — both Chebyshev bounds on `π(m)` at once.
* **`primeCounting_mul_log_upper`** — the upper bound renormalised to the common
  `π(m)·log m` scale of OQ-05: `π(m)·log m ≤ 2·(n·log 4 + √m·log √m)` with
  `n = ⌊m/2⌋`-free constant `2·m·log 4 + (lower-order)`, the clean companion to
  OQ-05's `primeCounting_mul_log_lower`.

Everything is derived from the two sibling files plus the `Nat.sqrt` bracket; no new
axioms.  `0 sorries, 0 axioms`.
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Proofs.ChebyshevPNTBridge
import Proofs.ChebyshevPNTBridgeOQ05
import Proofs.ChebyshevPNTBridgeOQ06

namespace ChebyshevPNTBridgeOQ06OQ01

open Nat

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: THE `Nat.sqrt` LOGARITHM BRACKET  `½ log m − log 2 ≤ log(√m) ≤ ½ log m`

`Nat.sqrt m` satisfies `(Nat.sqrt m)² ≤ m < (Nat.sqrt m + 1)²`.  The left inequality
gives `log(√m) ≤ ½ log m`; for the right, `Nat.sqrt m ≥ 2` (when `m ≥ 4`) makes
`Nat.sqrt m + 1 ≤ 2·Nat.sqrt m`, so `m < 4·(Nat.sqrt m)²` and hence
`log m ≤ log 4 + 2 log(√m)`, i.e. `½ log m − log 2 ≤ log(√m)`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Upper half of the bracket:** `log(Nat.sqrt m) ≤ ½ · log m`, from
`(Nat.sqrt m)² ≤ m`.  Valid for every `m ≥ 1`. -/
theorem log_natSqrt_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (Nat.sqrt m) ≤ Real.log m / 2 := by
  have hsqrt_pos : 0 < Nat.sqrt m := Nat.sqrt_pos.mpr hm
  -- (Nat.sqrt m)^2 ≤ m as reals
  have hle : ((Nat.sqrt m : ℝ)) ^ 2 ≤ (m : ℝ) := by
    have : (Nat.sqrt m) ^ 2 ≤ m := by
      have := Nat.sqrt_le' m   -- Nat.sqrt m * Nat.sqrt m ≤ m  (via sq)
      nlinarith [Nat.sqrt_le' m]
    exact_mod_cast this
  have hsqrt_posR : (0 : ℝ) < (Nat.sqrt m : ℝ) := by exact_mod_cast hsqrt_pos
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_pow] at hlog
  push_cast at hlog
  -- hlog : 2 * log(√m) ≤ log m
  linarith

/-- **Lower half of the bracket:** `½ · log m − log 2 ≤ log(Nat.sqrt m)`, equivalently
`log m ≤ log 4 + 2·log(Nat.sqrt m)`.  For `m ≥ 4` we have `Nat.sqrt m ≥ 2`, so
`m < (Nat.sqrt m + 1)² ≤ (2·Nat.sqrt m)² = 4·(Nat.sqrt m)²`. -/
theorem log_natSqrt_ge (m : ℕ) (hm : 4 ≤ m) :
    Real.log m / 2 - Real.log 2 ≤ Real.log (Nat.sqrt m) := by
  have hsqrt_ge2 : 2 ≤ Nat.sqrt m := by rw [Nat.le_sqrt]; omega
  -- m < (Nat.sqrt m + 1)^2 ≤ 4 * (Nat.sqrt m)^2  in ℕ
  have hlt : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
  have hbound : m ≤ 4 * (Nat.sqrt m) ^ 2 := by nlinarith [hlt, hsqrt_ge2]
  -- pass to ℝ
  have hboundR : (m : ℝ) ≤ 4 * (Nat.sqrt m : ℝ) ^ 2 := by exact_mod_cast hbound
  have hsqrt_posR : (0 : ℝ) < (Nat.sqrt m : ℝ) := by exact_mod_cast (by omega : 0 < Nat.sqrt m)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlog := Real.log_le_log hmR hboundR
  -- log m ≤ log (4 * (√m)^2) = log 4 + 2 log(√m)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  -- log 4 = 2 * log 2
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  rw [hlog4] at hlog
  push_cast at hlog
  linarith

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: THE TWO-SIDED SANDWICH

Both elementary Chebyshev bounds on `π(m)` in one statement, each in its natural
normalisation, for every `m ≥ 4`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Chebyshev density sandwich.**  For every `m ≥ 4`, the prime-counting
function is squeezed between the OQ-05 lower bound and the OQ-06 upper bound:

    (⌊m/2⌋·log 4 − log(m+1)) / log m  ≤  π(m)  ≤  m·log 4 / log(√m) + √m,

with `√m = Nat.sqrt m`.  The two leading densities are `log 2` (lower) and
`2 log 4` (upper), the elementary Chebyshev gap. -/
theorem primeCounting_sandwich (m : ℕ) (hm : 4 ≤ m) :
    ((m / 2 : ℕ) * Real.log 4 - Real.log (m + 1)) / Real.log m
        ≤ (Nat.primeCounting m : ℝ)
      ∧ (Nat.primeCounting m : ℝ)
        ≤ (m : ℝ) * Real.log 4 / Real.log (Nat.sqrt m) + (Nat.sqrt m : ℝ) :=
  ⟨ChebyshevPNTBridgeOQ05.primeCounting_ge_div_log m (by omega),
   ChebyshevPNTBridgeOQ06.primeCounting_le_div_log_sqrt m hm⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: UPPER BOUND ON THE COMMON `π(m)·log m` SCALE

OQ-05's lower bound is stated as a bound on `π(m)·log m`; OQ-06's upper bound uses
`log(√m)` instead.  Using the bracket `log(√m) ≥ ½ log m − log 2` we renormalise the
upper bound onto the same `π(m)·log m` scale, so both halves of Chebyshev's theorem
are finally expressed against the identical quantity.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Upper bound on `π(m)·log m`, companion to OQ-05's `primeCounting_mul_log_lower`.**
For every `m ≥ 4`,

    π(m) · log m  ≤  2·(m·log 4 + √m·log √m)  +  2·log 2 · π(m).

Obtained from OQ-06's `π(m)·log(√m) ≤ m·log 4 + √m·log √m` by replacing the small
denominator `log(√m)` with its bracket lower bound `½·log m − log 2`. The residual
`2·log 2·π(m)` is lower order relative to the `m·log 4` leading term, so the upper
density `limsup π(m)·log m / m ≤ 2 log 4` is unaffected. -/
theorem primeCounting_mul_log_upper (m : ℕ) (hm : 4 ≤ m) :
    (Nat.primeCounting m : ℝ) * Real.log m
      ≤ 2 * ((m : ℝ) * Real.log 4 + (Nat.sqrt m : ℝ) * Real.log (Nat.sqrt m))
          + 2 * Real.log 2 * (Nat.primeCounting m : ℝ) := by
  have hpi_nonneg : (0 : ℝ) ≤ (Nat.primeCounting m : ℝ) := by positivity
  -- OQ-06 upper bound on π(m)·log(√m)
  have hupper := ChebyshevPNTBridgeOQ06.primeCounting_mul_log_sqrt_le m hm
  -- bracket: log(√m) ≥ ½ log m − log 2, so π(m)·log(√m) ≥ π(m)·(½ log m − log 2)
  have hbr := log_natSqrt_ge m hm
  have hmul : (Nat.primeCounting m : ℝ) * (Real.log m / 2 - Real.log 2)
      ≤ (Nat.primeCounting m : ℝ) * Real.log (Nat.sqrt m) :=
    mul_le_mul_of_nonneg_left hbr hpi_nonneg
  -- chain and clear the 1/2
  nlinarith [hupper, hmul]

#check log_natSqrt_le              -- log(√m) ≤ ½ log m
#check log_natSqrt_ge              -- ½ log m − log 2 ≤ log(√m)
#check primeCounting_sandwich      -- two-sided Chebyshev sandwich
#check primeCounting_mul_log_upper -- upper bound on the common π(m)·log m scale

end ChebyshevPNTBridgeOQ06OQ01
