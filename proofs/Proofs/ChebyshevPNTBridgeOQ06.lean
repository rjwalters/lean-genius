/-
# Chebyshev–PNT Bridge OQ-06: Real-Logarithmic UPPER Bound on π(n)

The parent (`ChebyshevPNTBridge.lean`) proves the Chebyshev *upper* bound only in
its `ℕ`-power form

    (Nat.sqrt n) ^ (π(n) − π(√n)) ≤ 4^n          (`pow_sqrt_primeCounting_diff_le`),

stating the real-logarithmic consequence "π(n) ≤ √n + n·log 4 / log √n" only as a
comment in its header.  Its sibling `ChebyshevPNTBridgeOQ05.lean` carried the
*lower* bound into real-logarithmic form (`primeCounting_mul_log_lower`,
`primeCounting_ge_div_log`).  This file supplies the missing *upper* counterpart,
so both Chebyshev densities are now available in matching `Real.log` form.

The key content:

* **`primeCounting_diff_mul_log_sqrt_le`** — taking `Real.log` of the parent's
  power inequality, for every n ≥ 4,

      (π(n) − π(√n)) · log(√n) ≤ n · log 4

  (here `√n = Nat.sqrt n`, the integer square root).

* **`primeCounting_mul_log_sqrt_le`** — collapsing the `π(√n)` correction with the
  trivial bound `π(√n) ≤ √n` gives a clean upper bound on `π(n)·log(√n)`:

      π(n) · log(√n) ≤ n · log 4 + √n · log(√n).

* **`primeCounting_le_div_log_sqrt`** — dividing by `log(√n) > 0` records the
  Chebyshev *upper* density directly:

      π(n) ≤ n · log 4 / log(√n) + √n.

  Since `log(√n) ≈ ½ log n`, the leading term is `≈ 2 n log 4 / log n`, giving
  `limsup π(x)·log(x)/x ≤ 2 log 4` — the upper half of Chebyshev's 1852 theorem,
  matching the lower half from OQ-05.

Everything is derived from the parent results plus `Real.log` monotonicity and
`Nat.monotone_primeCounting`; no new axioms.  `0 sorries, 0 axioms`.
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Proofs.ChebyshevPNTBridge

namespace ChebyshevPNTBridgeOQ06

open Nat

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: REAL-LOGARITHMIC FORM OF THE PARENT'S POWER UPPER BOUND

`Real.log` is monotone and turns `a^k ≤ b^m` into `k·log a ≤ m·log b`.  Applied to
the parent's `(√n)^(π(n)−π(√n)) ≤ 4^n` this is the upper-density counterpart of
OQ-05's lower-density `primeCounting_mul_log_lower`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Real-logarithmic upper bound (difference form), all n ≥ 4.**

    (π(n) − π(√n)) · log(√n) ≤ n · log 4,

with `√n = Nat.sqrt n`.  This is `Real.log` applied to the parent's
`pow_sqrt_primeCounting_diff_le`. -/
theorem primeCounting_diff_mul_log_sqrt_le (n : ℕ) (hn : 4 ≤ n) :
    ((Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n) : ℕ) : ℝ)
        * Real.log (Nat.sqrt n)
      ≤ (n : ℝ) * Real.log 4 := by
  have hnat := ChebyshevPNTBridge.pow_sqrt_primeCounting_diff_le n hn
  have hsqrt_ge2 : 2 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
  -- Cast the Nat inequality into ℝ.
  have hcast : (Nat.sqrt n : ℝ) ^ (Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n))
      ≤ (4 : ℝ) ^ n := by
    have hl : (((Nat.sqrt n) ^ (Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n)) : ℕ) : ℝ)
        = (Nat.sqrt n : ℝ) ^ (Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n)) := by
      push_cast; ring
    have hr : ((4 ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n := by push_cast; ring
    calc (Nat.sqrt n : ℝ) ^ (Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n))
        = (((Nat.sqrt n) ^ (Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n)) : ℕ) : ℝ) :=
          hl.symm
      _ ≤ ((4 ^ n : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (4 : ℝ) ^ n := hr
  have hlhs_pos : (0 : ℝ) <
      (Nat.sqrt n : ℝ) ^ (Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n)) := by
    apply pow_pos; exact_mod_cast (by omega : 0 < Nat.sqrt n)
  have hlog := Real.log_le_log hlhs_pos hcast
  rw [Real.log_pow, Real.log_pow] at hlog
  exact hlog

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: CLEAN UPPER BOUND ON π(n) (absorbing the π(√n) correction)

`π(√n) ≤ √n` (the parent's `primeCounting_le`) lets us drop the small-prime
correction term, turning the difference bound into a bound on `π(n)` itself.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Real-logarithmic upper bound, π(n) form, all n ≥ 4.**

    π(n) · log(√n) ≤ n · log 4 + √n · log(√n).

Obtained from `primeCounting_diff_mul_log_sqrt_le` by writing
`π(n) = (π(n) − π(√n)) + π(√n)` (valid since `π` is monotone and `√n ≤ n`) and
bounding the correction `π(√n) · log(√n) ≤ √n · log(√n)`. -/
theorem primeCounting_mul_log_sqrt_le (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) * Real.log (Nat.sqrt n)
      ≤ (n : ℝ) * Real.log 4 + (Nat.sqrt n : ℝ) * Real.log (Nat.sqrt n) := by
  have hmono : Nat.primeCounting (Nat.sqrt n) ≤ Nat.primeCounting n :=
    Nat.monotone_primeCounting (Nat.sqrt_le_self n)
  have hsqrt_ge2 : 2 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
  have hLnn : 0 ≤ Real.log (Nat.sqrt n) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Nat.sqrt n))
  have hpi_sqrt_le : (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Nat.sqrt n : ℝ) := by
    exact_mod_cast ChebyshevPNTBridge.primeCounting_le (Nat.sqrt n)
  have hth1 := primeCounting_diff_mul_log_sqrt_le n hn
  have hcsub : ((Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n) : ℕ) : ℝ)
      = (Nat.primeCounting n : ℝ) - (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
    rw [Nat.cast_sub hmono]
  rw [hcsub] at hth1
  have hterm : (Nat.primeCounting (Nat.sqrt n) : ℝ) * Real.log (Nat.sqrt n)
      ≤ (Nat.sqrt n : ℝ) * Real.log (Nat.sqrt n) :=
    mul_le_mul_of_nonneg_right hpi_sqrt_le hLnn
  nlinarith [hth1, hterm]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: EXPLICIT CHEBYSHEV UPPER DENSITY (quotient form)

Dividing by `log(√n) > 0` (positive for n ≥ 4, since √n ≥ 2) records the upper
density directly — the mirror of OQ-05's `primeCounting_ge_div_log`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Chebyshev upper density in quotient form: for n ≥ 4,

    π(n) ≤ n · log 4 / log(√n) + √n.**

Dividing `primeCounting_mul_log_sqrt_le` by `log(√n) > 0`.  As `log(√n) ≈ ½ log n`,
the leading term is `≈ 2 n log 4 / log n`, so `limsup π(x)·log x / x ≤ 2 log 4`. -/
theorem primeCounting_le_div_log_sqrt (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ)
      ≤ (n : ℝ) * Real.log 4 / Real.log (Nat.sqrt n) + (Nat.sqrt n : ℝ) := by
  have hsqrt_ge2 : 2 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
  have hL : 0 < Real.log (Nat.sqrt n) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.sqrt n))
  have h2 := primeCounting_mul_log_sqrt_le n hn
  -- Multiply the RHS template by log(√n) and compare.
  have key : ((n : ℝ) * Real.log 4 / Real.log (Nat.sqrt n) + (Nat.sqrt n : ℝ))
        * Real.log (Nat.sqrt n)
      = (n : ℝ) * Real.log 4 + (Nat.sqrt n : ℝ) * Real.log (Nat.sqrt n) := by
    field_simp
  have hmul : (Nat.primeCounting n : ℝ) * Real.log (Nat.sqrt n)
      ≤ ((n : ℝ) * Real.log 4 / Real.log (Nat.sqrt n) + (Nat.sqrt n : ℝ))
          * Real.log (Nat.sqrt n) := by
    rw [key]; exact h2
  exact le_of_mul_le_mul_right hmul hL

#check primeCounting_diff_mul_log_sqrt_le   -- real-log difference form
#check primeCounting_mul_log_sqrt_le        -- real-log π(n) form
#check primeCounting_le_div_log_sqrt        -- quotient (upper density) form
#check ChebyshevPNTBridgeOQ06.primeCounting_le_div_log_sqrt

end ChebyshevPNTBridgeOQ06
