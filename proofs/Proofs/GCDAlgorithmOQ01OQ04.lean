/-
GCD Algorithm OQ-01-OQ-04: Binary GCD vs Euclidean — an unbounded step-count gap

The parent file `BinaryGcdOQ01` proves matching *upper* bounds for the step
counts of the Euclidean algorithm (`euclidSteps`) and Stein's binary GCD
algorithm (`binaryGcdSteps`): both are O(log) in the inputs.  Upper bounds
alone do not settle which algorithm is faster, and the parent's concrete
examples already show that neither dominates the other pointwise
(e.g. `euclidSteps 12 8 = 2 < 5 = binaryGcdSteps 12 8`, but
`euclidSteps 89 55 = 9 > 8 = binaryGcdSteps 89 55`).

This file pins down a *sharp separation* on the diagonal `a = a`:

  * The Euclidean algorithm finishes in a single step:  `euclidSteps a a = 1`.
  * Binary GCD takes `ν₂(a) + 1` steps, where `ν₂(a) = a.factorization 2`
    is the 2-adic valuation (number of trailing zero bits):
    `binaryGcdSteps a a = a.factorization 2 + 1`.

Consequently the step-count gap `binaryGcdSteps a a - euclidSteps a a = ν₂(a)`
is **unbounded**: taking `a = 2 ^ n` makes binary GCD spend `n` extra steps
removing factors of two that the Euclidean algorithm never sees.  This is a
formal worst-case witness that, in the division-step model, binary GCD is not
within any additive (or multiplicative) constant of the Euclidean algorithm.

References:
  - Stein (1967); Knuth, TAOCP Vol. 2, §4.5.2 (Algorithm B)
  - Lamé (1844) for the Euclidean worst case
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Proofs.BinaryGcdOQ01

open Nat

namespace GCDAlgorithmOQ01OQ04

open BinaryGcdOQ01

/-! ## Euclidean algorithm on equal inputs

On `a = a` the Euclidean algorithm performs one division `a % a = 0` and stops. -/

/-- **Euclidean diagonal.** For positive `a`, `euclidSteps a a = 1`. -/
theorem euclidSteps_self {a : ℕ} (ha : 0 < a) : euclidSteps a a = 1 := by
  obtain ⟨a', rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  rw [euclidSteps.eq_3]
  -- The guard `b' + 1 ≤ a'`, i.e. `a' + 1 ≤ a'`, is false, so we take the
  -- `else` branch: `1 + euclidSteps (a'+1) ((a'+1) % (a'+1))`.
  rw [if_neg (by omega), Nat.mod_self]
  simp [euclidSteps]

/-! ## Binary GCD on equal inputs

One step of binary GCD on `a = a`:
* if `a` is even, both arguments are halved and the count drops by one;
* if `a` is odd, the subtraction `a - a = 0` terminates after one step. -/

/-- Even/even unfolding of one binary-GCD step. -/
private theorem binaryGcdSteps_even_even {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hae : a % 2 = 0) (hbe : b % 2 = 0) :
    binaryGcdSteps a b = 1 + binaryGcdSteps (a / 2) (b / 2) := by
  obtain ⟨a', rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  rw [binaryGcdSteps.eq_3, if_pos hae, if_pos hbe]

/-- Binary GCD on an odd diagonal finishes in one step: `binaryGcdSteps a a = 1`. -/
private theorem binaryGcdSteps_self_odd {a : ℕ} (hao : a % 2 = 1) :
    binaryGcdSteps a a = 1 := by
  obtain ⟨a', rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  rw [binaryGcdSteps.eq_3, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- `else` branch: `1 + binaryGcdSteps (a'+1) ((a'+1 - (a'+1)) / 2)`.
  rw [show (a' + 1 - (a' + 1)) / 2 = 0 from by omega, binaryGcdSteps_zero_right]

/-- **Binary GCD diagonal, valuation form (powers of two times an odd number).**
For odd `m`, `binaryGcdSteps (2^v * m) (2^v * m) = v + 1`: each of the `v`
factors of two costs one halving step, then the odd core finishes in one. -/
private theorem binaryGcdSteps_two_pow_mul_self (v m : ℕ) (hm : m % 2 = 1) :
    binaryGcdSteps (2 ^ v * m) (2 ^ v * m) = v + 1 := by
  induction v with
  | zero =>
      simpa using binaryGcdSteps_self_odd hm
  | succ v ih =>
      have hmpos : 0 < m := by omega
      have hpos : 0 < 2 ^ (v + 1) * m := by positivity
      have heven : (2 ^ (v + 1) * m) % 2 = 0 := by
        have h2 : 2 ∣ 2 ^ (v + 1) * m :=
          (dvd_pow_self 2 (Nat.succ_ne_zero v)).mul_right m
        omega
      have hhalf : (2 ^ (v + 1) * m) / 2 = 2 ^ v * m := by
        rw [pow_succ, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ (by norm_num)]
      rw [binaryGcdSteps_even_even hpos hpos heven heven, hhalf, ih]
      omega

/-- **Binary GCD diagonal.** For positive `a`, the number of binary-GCD steps on
`a = a` equals the 2-adic valuation of `a` plus one. -/
theorem binaryGcdSteps_self (a : ℕ) (ha : 0 < a) :
    binaryGcdSteps a a = a.factorization 2 + 1 := by
  -- Write `a = 2 ^ ν₂(a) * m` with `m = a / 2 ^ ν₂(a)` (the odd core) odd.
  have hne : a ≠ 0 := by omega
  set v := a.factorization 2 with hv
  set m := a / 2 ^ v with hm
  have hsplit : a = 2 ^ v * m := by
    rw [hm, hv]
    exact (Nat.ordProj_mul_ordCompl_eq_self a 2).symm
  have hmodd : m % 2 = 1 := by
    have hnd : ¬ (2 ∣ m) := by
      rw [hm, hv]; exact Nat.not_dvd_ordCompl (by norm_num) hne
    omega
  calc binaryGcdSteps a a
      = binaryGcdSteps (2 ^ v * m) (2 ^ v * m) := by rw [← hsplit]
    _ = v + 1 := binaryGcdSteps_two_pow_mul_self v m hmodd

/-! ## The separation -/

/-- **Pointwise gap on the diagonal.** Binary GCD spends exactly `ν₂(a)` more
division steps than the Euclidean algorithm on the input `(a, a)`. -/
theorem diagonal_gap (a : ℕ) (ha : 0 < a) :
    binaryGcdSteps a a = euclidSteps a a + a.factorization 2 := by
  rw [binaryGcdSteps_self a ha, euclidSteps_self ha]; ring

/-- On powers of two the Euclidean algorithm still uses a single step. -/
theorem euclidSteps_two_pow (n : ℕ) : euclidSteps (2 ^ n) (2 ^ n) = 1 :=
  euclidSteps_self (by positivity)

/-- Binary GCD on `(2^n, 2^n)` uses exactly `n + 1` steps. -/
theorem binaryGcdSteps_two_pow (n : ℕ) : binaryGcdSteps (2 ^ n) (2 ^ n) = n + 1 := by
  have := binaryGcdSteps_two_pow_mul_self n 1 (by norm_num)
  simpa using this

/-- **Unbounded separation.** For every `N` there is a positive input on which
binary GCD takes at least `N` more steps than the Euclidean algorithm.  Hence no
additive (let alone multiplicative) constant bounds `binaryGcdSteps` in terms of
`euclidSteps`: the witness `a = 2 ^ N` forces an `N`-step overhead. -/
theorem gap_unbounded (N : ℕ) :
    ∃ a : ℕ, 0 < a ∧ binaryGcdSteps a a ≥ euclidSteps a a + N := by
  refine ⟨2 ^ N, by positivity, ?_⟩
  rw [euclidSteps_two_pow, binaryGcdSteps_two_pow]
  omega

/-- **Ratio form.** On `(2^n, 2^n)` binary GCD uses `n + 1` times as many steps
as the Euclidean algorithm, so the ratio is unbounded. -/
theorem diagonal_ratio (n : ℕ) :
    binaryGcdSteps (2 ^ n) (2 ^ n) = (n + 1) * euclidSteps (2 ^ n) (2 ^ n) := by
  rw [euclidSteps_two_pow, binaryGcdSteps_two_pow]; ring

/-! ## Sanity checks

These specialise the general theorems above (all kernel-checked, no
`native_decide`, hence no `Lean.ofReduceBool` dependency):
* `binaryGcdSteps 8 8 = 4`  since `ν₂(8) = 3`  (`binaryGcdSteps_two_pow 3`);
* `euclidSteps 8 8 = 1`      (`euclidSteps_self`);
* `binaryGcdSteps 12 12 = 3` since `12 = 2² · 3`, `ν₂(12) = 2`. -/

example : binaryGcdSteps 8 8 = 4 := by
  have := binaryGcdSteps_two_pow 3; norm_num at this ⊢; exact this

example : euclidSteps 8 8 = 1 := euclidSteps_self (by norm_num)

example : binaryGcdSteps 12 12 = 3 := by
  have := binaryGcdSteps_two_pow_mul_self 2 3 (by norm_num); norm_num at this; exact this

/-! ## Summary

**Proved (0 axioms, 0 sorries):**
1. `euclidSteps_self` : Euclidean steps on `(a, a)` equal `1`.
2. `binaryGcdSteps_self` : binary GCD steps on `(a, a)` equal `ν₂(a) + 1`.
3. `diagonal_gap` : the pointwise gap is exactly `ν₂(a)`.
4. `gap_unbounded` : the gap is unbounded (witness `a = 2^N`).
5. `diagonal_ratio` : the step ratio on `(2^n, 2^n)` is `n + 1`.

Together with the parent's O(log) upper bounds, this shows the two algorithms'
division-step counts are genuinely incomparable: binary GCD can be a Θ(log a)
factor slower on highly-even inputs.
-/

end GCDAlgorithmOQ01OQ04
