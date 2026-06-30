/-
# Chebyshev–PNT Bridge OQ-06-OQ-02: an `n·log n` lower bound on the n-th prime

The sibling entries OQ-05 / OQ-06 and the sandwich OQ-06-OQ-01 package the elementary
Chebyshev bounds on the prime-counting function `π` into real-logarithmic form, with
upper density `limsup π(x)·log x / x ≤ 2·log 4`.  Reading that **upper** bound at the
primes themselves *inverts* it into a growth statement for the n-th prime
`pₙ := Nat.nth Nat.Prime n` (`Nat`-indexed from `0`, so `p₀ = 2`).

The bridge is the identity `π(pₙ) = n + 1` (`primeCounting_nth_prime`): `pₙ` is the
`(n+1)`-st prime, and `π` counts primes `≤ pₙ`.  Feeding `m = pₙ` into OQ-06's
`primeCounting_mul_log_sqrt_le` gives

    (n + 1)·log(√pₙ) ≤ pₙ·log 4 + √pₙ·log(√pₙ).

The correction `√pₙ·log(√pₙ)` is absorbed by `√pₙ·log(√pₙ) ≤ pₙ·log 4`
(because `log(√pₙ) ≤ √pₙ ≤ √pₙ·log 4`, using `log 4 ≥ 1`), collapsing this to

    (n + 1)·log(√pₙ) ≤ 2·pₙ·log 4.

Finally the OQ-06-OQ-01 bracket `log(√pₙ) ≥ ½·log pₙ − log 2` together with the trivial
`pₙ ≥ n + 2` (`Nat.add_two_le_nth_prime`) gives the explicit

    pₙ ≥ (n + 1)·(½·log(n+2) − log 2) / (2·log 4)      ~   n·log n / (4·log 4),

an honest `n·log n` lower bound on the n-th prime — strictly sharper than Mathlib's
linear `Nat.add_two_le_nth_prime` (`pₙ ≥ n + 2`).  This is the elementary-Chebyshev
inverse of the prime-counting upper density.  `0 sorries, 0 axioms`.
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Proofs.ChebyshevPNTBridge
import Proofs.ChebyshevPNTBridgeOQ06

namespace ChebyshevPNTBridgeOQ06OQ02

open Nat

/-! ═══════════════════════════════════════════════════════════════════════════════
PART 0: THE `Nat.sqrt` LOGARITHM BRACKET (lower half)

`log(√m) ≥ ½·log m − log 2` for `m ≥ 4`.  This mirrors `log_natSqrt_ge` from the
sibling `ChebyshevPNTBridgeOQ06OQ01`; it is reproved here (self-contained, needs only
the defining inequalities of `Nat.sqrt`) so this file depends on nothing beyond OQ-06.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Lower half of the `Nat.sqrt` log bracket:** `½·log m − log 2 ≤ log(Nat.sqrt m)`
for `m ≥ 4`, from `m < (Nat.sqrt m + 1)² ≤ (2·Nat.sqrt m)² = 4·(Nat.sqrt m)²`. -/
theorem log_natSqrt_ge (m : ℕ) (hm : 4 ≤ m) :
    Real.log m / 2 - Real.log 2 ≤ Real.log (Nat.sqrt m) := by
  have hsqrt_ge2 : 2 ≤ Nat.sqrt m := by rw [Nat.le_sqrt]; omega
  have hlt : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
  have hbound : m ≤ 4 * (Nat.sqrt m) ^ 2 := by nlinarith [hlt, hsqrt_ge2]
  have hboundR : (m : ℝ) ≤ 4 * (Nat.sqrt m : ℝ) ^ 2 := by exact_mod_cast hbound
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlog := Real.log_le_log hmR hboundR
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  rw [hlog4] at hlog
  push_cast at hlog
  linarith

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: THE BRIDGE IDENTITY  `π(nth Prime n) = n + 1`

`Nat.nth Nat.Prime n` is the `(n+1)`-st prime (`Nat`-indexed from `0`).  Mathlib's
`primeCounting'` counts primes *strictly below* its argument, so
`π'(nth Prime n) = n`; since `nth Prime n` is itself prime, the inclusive count
`π(nth Prime n) = π'(nth Prime n + 1)` adds exactly one, giving `n + 1`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Bridge identity:** `π(nth Prime n) = n + 1`. -/
theorem primeCounting_nth_prime (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  have h : Nat.primeCounting' (Nat.nth Nat.Prime n + 1)
      = Nat.primeCounting' (Nat.nth Nat.Prime n) + 1 := by
    unfold Nat.primeCounting'
    rw [Nat.count_succ]
    simp [Nat.prime_nth_prime n]
  unfold Nat.primeCounting
  rw [h, Nat.primeCounting'_nth_eq]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: THE `n·log n` LOWER BOUND ON THE N-TH PRIME

Read OQ-06's upper bound at `m = nth Prime n`, absorb the `√pₙ` correction, and
substitute the `Nat.sqrt` log bracket of OQ-06-OQ-01.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Chebyshev `n·log n` lower bound on the n-th prime.**  For every `n ≥ 2`,
with `pₙ = Nat.nth Nat.Prime n`,

    (n + 1)·(½·log(n+2) − log 2)  ≤  2·log 4·pₙ,

i.e. `pₙ ≥ (n + 1)·(½·log(n+2) − log 2) / (2·log 4) ~ n·log n / (4·log 4)`.  This is the
elementary-Chebyshev inverse of the prime-counting upper density, strictly sharper than
the linear `Nat.add_two_le_nth_prime` (`pₙ ≥ n + 2`). -/
theorem nth_prime_lower_bound (n : ℕ) (hn : 2 ≤ n) :
    (n + 1 : ℝ) * (Real.log (n + 2) / 2 - Real.log 2)
      ≤ 2 * Real.log 4 * (Nat.nth Nat.Prime n : ℝ) := by
  set p := Nat.nth Nat.Prime n with hp
  -- pₙ ≥ n + 2 ≥ 4
  have hge : n + 2 ≤ p := by
    have := Nat.add_two_le_nth_prime n; rw [← hp] at this; exact this
  have hp4 : 4 ≤ p := by omega
  -- positivity scaffolding
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hsqrt_ge2 : 2 ≤ Nat.sqrt p := by rw [Nat.le_sqrt]; omega
  have hsqrtR2 : (2 : ℝ) ≤ (Nat.sqrt p : ℝ) := by exact_mod_cast hsqrt_ge2
  have hsqrtR : (0 : ℝ) < (Nat.sqrt p : ℝ) := by linarith
  have hlogsqrt_pos : 0 < Real.log (Nat.sqrt p) := Real.log_pos (by linarith)
  -- log 4 ≥ 1, via 1 = log(exp 1) ≤ log 4 (exp 1 < 2.72 ≤ 4)
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  -- π(pₙ) = n + 1
  have hpi : (Nat.primeCounting p : ℝ) = (n + 1 : ℝ) := by
    rw [hp, primeCounting_nth_prime]; push_cast; ring
  -- (A) OQ-06 mul bound at m = pₙ:  (n+1)·log√p ≤ p·log4 + √p·log√p
  have hA := ChebyshevPNTBridgeOQ06.primeCounting_mul_log_sqrt_le p hp4
  rw [hpi] at hA
  -- (B) absorb the correction:  √p·log√p ≤ p·log4
  have hlogle : Real.log (Nat.sqrt p) ≤ (Nat.sqrt p : ℝ) := by
    have := Real.log_le_sub_one_of_pos hsqrtR; linarith
  have hsqNat : Nat.sqrt p ^ 2 ≤ p := Nat.sqrt_le' p
  have hsq : (Nat.sqrt p : ℝ) * (Nat.sqrt p : ℝ) ≤ (p : ℝ) := by
    have hR : (Nat.sqrt p : ℝ) ^ 2 ≤ (p : ℝ) := by exact_mod_cast hsqNat
    nlinarith [hR]
  have hB : (Nat.sqrt p : ℝ) * Real.log (Nat.sqrt p) ≤ (p : ℝ) * Real.log 4 := by
    have h1 : (Nat.sqrt p : ℝ) * Real.log (Nat.sqrt p)
        ≤ (Nat.sqrt p : ℝ) * (Nat.sqrt p : ℝ) :=
      mul_le_mul_of_nonneg_left hlogle (by linarith)
    have h3 : (p : ℝ) ≤ (p : ℝ) * Real.log 4 := by nlinarith [hlog4, hpR]
    linarith
  -- (C) collapse:  (n+1)·log√p ≤ 2·p·log4
  have hC : (n + 1 : ℝ) * Real.log (Nat.sqrt p) ≤ 2 * (p : ℝ) * Real.log 4 := by
    nlinarith [hA, hB]
  -- (D) bracket + monotonicity:  ½·log(n+2) − log2 ≤ log√p
  have hbr := log_natSqrt_ge p hp4
  have hnp : (n + 2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hge
  have hlogmono : Real.log (n + 2) ≤ Real.log p :=
    Real.log_le_log (by positivity) hnp
  have hD : Real.log (n + 2) / 2 - Real.log 2 ≤ Real.log (Nat.sqrt p) := by
    linarith [hbr, hlogmono]
  -- combine (D) and (C)
  have hn1 : (0 : ℝ) ≤ (n + 1 : ℝ) := by positivity
  have hfin : (n + 1 : ℝ) * (Real.log (n + 2) / 2 - Real.log 2)
      ≤ (n + 1 : ℝ) * Real.log (Nat.sqrt p) := mul_le_mul_of_nonneg_left hD hn1
  nlinarith [hfin, hC]

#check primeCounting_nth_prime   -- π(nth Prime n) = n + 1
#check nth_prime_lower_bound      -- (n+1)·(½log(n+2)−log2) ≤ 2·log4·pₙ

end ChebyshevPNTBridgeOQ06OQ02
