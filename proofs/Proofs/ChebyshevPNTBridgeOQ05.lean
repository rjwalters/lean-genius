/-
# Chebyshev–PNT Bridge OQ-05: Lower Bound on π(m) for ALL m (not just even)

Parent (`ChebyshevPNTBridge.lean`) proved the lower bound only along the
even-integer subsequence:

    4^n ≤ (2n+1) · (2n)^{π(2n)}          (`four_pow_le_mul_pow_primeCounting`)

which controls π(x)·log(x)/x ≥ log 2 − o(1) only when x = 2n runs over even
integers. The parent's open question OQ-05 asks to extend this to *arbitrary*
m (equivalently arbitrary real x ≥ 1, since π is the step function
π(x) = π(⌊x⌋)) via the monotonicity π(m) ≥ π(2⌊m/2⌋).

This file carries out that extension. The key new content:

* **`four_pow_half_le_mul_pow_primeCounting`** — for every m ≥ 2,

      4^{⌊m/2⌋} ≤ (m+1) · m^{π(m)},

  a single inequality valid for ODD and EVEN m alike. The parent's even-only
  bound is transferred to m by collapsing the even integer 2⌊m/2⌋ ≤ m into m
  on both the base (2⌊m/2⌋ ≤ m) and the exponent (π(2⌊m/2⌋) ≤ π(m)).

* **`primeCounting_mul_log_lower`** — the real-logarithmic form

      ⌊m/2⌋ · log 4 − log(m+1) ≤ π(m) · log m,

  obtained by taking `Real.log` of the previous inequality. Since log 4 =
  2 log 2 and ⌊m/2⌋/m → 1/2, log(m+1)/log m → 0, this gives the Chebyshev
  lower density π(m)·log(m)/m ≥ log 2 − o(1) along the FULL sequence m → ∞,
  answering OQ-05.

Everything is derived from the parent results plus `Real.log` monotonicity;
no new axioms. `0 sorries, 0 axioms`.
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Proofs.ChebyshevPNTBridge

namespace ChebyshevPNTBridgeOQ05

open Nat

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: NATURAL-NUMBER LOWER BOUND FOR ALL m

The parent bound `four_pow_le_mul_pow_primeCounting` holds at the even integer
2n. Writing n = ⌊m/2⌋ gives an even integer 2n ≤ m, and monotonicity of π
upgrades the bound from 2n to m.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- π is monotone in its argument (more integers ≤ b can be prime than ≤ a). -/
theorem primeCounting_mono {a b : ℕ} (hab : a ≤ b) :
    Nat.primeCounting a ≤ Nat.primeCounting b :=
  Nat.monotone_primeCounting hab

/-- **Lower bound on π(m) valid for every m ≥ 2 (odd or even).**

    4^{⌊m/2⌋} ≤ (m+1) · m^{π(m)}.

The parent file establishes this only for even arguments via
`four_pow_le_mul_pow_primeCounting`; here we transfer it to an arbitrary m by
taking n = ⌊m/2⌋ and absorbing the even integer 2n ≤ m into m on both the base
and the exponent. -/
theorem four_pow_half_le_mul_pow_primeCounting (m : ℕ) (hm : 2 ≤ m) :
    4 ^ (m / 2) ≤ (m + 1) * m ^ Nat.primeCounting m := by
  set n := m / 2 with hn_def
  have hn1 : 1 ≤ n := by
    rw [hn_def]; omega
  -- 2n is the even integer just below (or equal to) m
  have h2n_le : 2 * n ≤ m := by
    rw [hn_def]; omega
  have hm_pos : 0 < m := by omega
  -- Parent even-only bound at n
  have hparent : 4 ^ n ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) :=
    ChebyshevPNTBridge.four_pow_le_mul_pow_primeCounting n hn1
  -- Step 1: collapse the prefactor 2n+1 ≤ m+1
  have hpre : (2 * n + 1 : ℕ) ≤ m + 1 := by omega
  -- Step 2: collapse the base (2n)^k ≤ m^k for the same exponent k = π(2n)
  have hbase : (2 * n) ^ Nat.primeCounting (2 * n) ≤ m ^ Nat.primeCounting (2 * n) :=
    Nat.pow_le_pow_left h2n_le _
  -- Step 3: raise the exponent π(2n) ≤ π(m)
  have hexp : m ^ Nat.primeCounting (2 * n) ≤ m ^ Nat.primeCounting m :=
    Nat.pow_le_pow_right hm_pos (primeCounting_mono h2n_le)
  calc 4 ^ n
      ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) := hparent
    _ ≤ (m + 1) * m ^ Nat.primeCounting m := by
        apply Nat.mul_le_mul hpre
        exact le_trans hbase hexp

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: REAL-LOGARITHMIC FORM (CHEBYSHEV LOWER DENSITY)

Taking `Real.log` of the Nat inequality turns it into a linear lower bound on
π(m)·log(m), which is the form in which the Chebyshev constant log 2 appears.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Real-logarithmic lower bound, all m ≥ 2.**

    ⌊m/2⌋ · log 4 − log(m+1) ≤ π(m) · log m.

This is `Real.log` applied to `four_pow_half_le_mul_pow_primeCounting`. Since
log 4 = 2 log 2, the leading term is (⌊m/2⌋/m)·m·log 4 ≈ m·log 2, so dividing
by m gives π(m)·log(m)/m ≥ log 2 − o(1) over the full integer sequence. -/
theorem primeCounting_mul_log_lower (m : ℕ) (hm : 2 ≤ m) :
    (m / 2 : ℕ) * Real.log 4 - Real.log (m + 1)
      ≤ (Nat.primeCounting m : ℝ) * Real.log m := by
  have hnat := four_pow_half_le_mul_pow_primeCounting m hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hmp1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  -- Cast the Nat inequality into ℝ and take logs.
  have hcast : (4 : ℝ) ^ (m / 2) ≤ ((m : ℝ) + 1) * (m : ℝ) ^ Nat.primeCounting m := by
    have := hnat
    have h4 : ((4 ^ (m / 2) : ℕ) : ℝ) = (4 : ℝ) ^ (m / 2) := by push_cast; ring
    have hr : (((m + 1) * m ^ Nat.primeCounting m : ℕ) : ℝ)
        = ((m : ℝ) + 1) * (m : ℝ) ^ Nat.primeCounting m := by push_cast; ring
    calc (4 : ℝ) ^ (m / 2) = ((4 ^ (m / 2) : ℕ) : ℝ) := h4.symm
      _ ≤ (((m + 1) * m ^ Nat.primeCounting m : ℕ) : ℝ) := by exact_mod_cast this
      _ = ((m : ℝ) + 1) * (m : ℝ) ^ Nat.primeCounting m := hr
  -- Both sides positive, so log is monotone and additive.
  have hlhs_pos : (0 : ℝ) < (4 : ℝ) ^ (m / 2) := by positivity
  have hlog := Real.log_le_log hlhs_pos hcast
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  rw [Real.log_pow, Real.log_pow] at hlog
  -- hlog : ↑(m/2) * log 4 ≤ log (m+1) + ↑(π m) * log m
  -- Rearrange.
  have : ((m / 2 : ℕ) : ℝ) * Real.log 4
      ≤ Real.log ((m : ℝ) + 1) + (Nat.primeCounting m : ℝ) * Real.log m := hlog
  linarith

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: EXPLICIT CHEBYSHEV LOWER DENSITY (clean denominator-free form)

Dividing the previous bound by log m (positive for m ≥ 2) records the lower
density directly.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Chebyshev lower density in quotient form: for m ≥ 2,

    π(m) ≥ (⌊m/2⌋ · log 4 − log(m+1)) / log m. -/
theorem primeCounting_ge_div_log (m : ℕ) (hm : 2 ≤ m) :
    ((m / 2 : ℕ) * Real.log 4 - Real.log (m + 1)) / Real.log m
      ≤ (Nat.primeCounting m : ℝ) := by
  have hlogm_pos : 0 < Real.log m := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < m)
  rw [div_le_iff₀ hlogm_pos]
  exact primeCounting_mul_log_lower m hm

#check four_pow_half_le_mul_pow_primeCounting  -- Nat lower bound, all m
#check primeCounting_mul_log_lower             -- real-log form
#check primeCounting_ge_div_log                -- quotient form
#check ChebyshevPNTBridge.four_pow_le_mul_pow_primeCounting  -- parent (even only)

end ChebyshevPNTBridgeOQ05
