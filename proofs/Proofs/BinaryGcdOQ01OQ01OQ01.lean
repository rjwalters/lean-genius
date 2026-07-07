/-
  Binary GCD OQ-01-OQ-01-OQ-01: A matching Ω((log N)²) lower bound for the
  total bit-operation cost of Stein's binary GCD.

  The parent file `BinaryGcdOQ01OQ01` defines the honest total bit-operation
  cost `binaryGcdCost a b` (each reduction step on the pair `(a, b)` costs
  `Nat.size a + Nat.size b` bit operations) and proves the classical *upper*
  bound

      binaryGcdCost a b ≤ (2·(log₂ a + log₂ b) + 2)·(log₂ a + log₂ b + 2)
                        = O((log N)²)      (Brent 1976, Knuth TAOCP 4.5.2).

  The open question asks whether this quadratic bound is *tight* — i.e. whether
  there is an input family on which the cost is genuinely `Ω((log N)²)`, rather
  than the bound being a loose over-estimate.

  This file answers it affirmatively, and in the sharpest possible form: on the
  **diagonal power-of-two family** `a = b = 2^k` the cost is not merely bounded
  below by a quadratic, it is *exactly* a quadratic:

      binaryGcdCost (2^k) (2^k) = (k+1)·(k+2).

  Reason: `(2^k, 2^k)` is an even/even pair, so a single step halves both
  operands to `(2^(k-1), 2^(k-1))` at cost `2·size(2^k) = 2·(k+1)`. Iterating,
  the algorithm walks through `(2^k,2^k), (2^(k-1),2^(k-1)), …, (1,1)` and pays

      Σ_{j=0}^{k} 2·(j+1) = (k+1)·(k+2).

  Since `log₂(2^k) = k`, this gives the matching lower bound

      (log₂ N)² ≤ binaryGcdCost N N        for  N = 2^k,

  and, combined with the parent's upper bound, squeezes the cost on this family
  into `Θ((log N)²)`. The quadratic upper bound is therefore asymptotically
  tight, not a loose over-estimate.

  Main results.

  * `binaryGcdCost_two_pow_diag`
        binaryGcdCost (2^k) (2^k) = (k+1)·(k+2)          (exact closed form)
  * `binaryGcdCost_two_pow_diag_lower`
        k² ≤ binaryGcdCost (2^k) (2^k)                   (clean quadratic floor)
  * `binaryGcdCost_diag_log_lower`
        (log₂ (2^k))² ≤ binaryGcdCost (2^k) (2^k)        (Ω((log N)²), N = 2^k)
  * `binaryGcdCost_omega_log_sq`
        an explicit family with cost ≥ (log N)²          (the requested family)
  * `binaryGcdCost_diag_two_sided`
        (L/2)² ≤ binaryGcdCost ≤ (2L+2)(L+2), L = log a + log b
                                                          (Θ((log N)²) squeeze)

  All results are axiom-free (only the foundational propext / Classical.choice /
  Quot.sound), 0 sorries, no `native_decide`.

  References:
  - Stein (1967), Binary GCD Algorithm
  - Brent (1976), analysis of the binary GCD
  - Knuth, TAOCP 4.5.2
  - BinaryGcdOQ01OQ01.lean (total bit-operation cost model `binaryGcdCost`)
-/
import Mathlib
import Proofs.BinaryGcdOQ01
import Proofs.BinaryGcdOQ01OQ01

namespace BinaryGcdOQ01OQ01OQ01

open Nat BinaryGcdOQ01 BinaryGcdOQ01OQ01

/-! ## One even/even reduction step on the diagonal

The engine of the exact formula: on an even positive operand `a`, the diagonal
pair `(a, a)` is halved to `(a/2, a/2)` at cost `2·Nat.size a`. -/

/-- A single binary-GCD reduction step on a diagonal even pair `(a, a)` with
    `a` positive and even: it halves both operands, charging `2·Nat.size a`. -/
theorem cost_even_diag (a : ℕ) (ha : 0 < a) (he : a % 2 = 0) :
    binaryGcdCost a a = 2 * Nat.size a + binaryGcdCost (a / 2) (a / 2) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  rw [binaryGcdCost.eq_3]
  rw [if_pos he, if_pos he]
  ring

/-! ## Exact cost on the diagonal power-of-two family -/

/-- **Exact total cost on the diagonal power-of-two family.** For every `k`,

        binaryGcdCost (2^k) (2^k) = (k+1)·(k+2).

    The `k+1` even/even reduction steps `(2^k,2^k) → (2^(k-1),2^(k-1)) → … →
    (1,1)` each cost `2·(j+1)` bit operations, and these sum to `(k+1)(k+2)`. -/
theorem binaryGcdCost_two_pow_diag (k : ℕ) :
    binaryGcdCost (2 ^ k) (2 ^ k) = (k + 1) * (k + 2) := by
  induction k with
  | zero =>
      -- (1,1) is odd/odd: one step to (1,0) at cost size 1 + size 1 = 2.
      have h : binaryGcdCost (0 + 1) (0 + 1) = 2 := by
        rw [binaryGcdCost.eq_3]
        norm_num [Nat.size_one, binaryGcdCost_zero_right]
      simpa using h
  | succ n ih =>
      have hev : 2 ^ (n + 1) % 2 = 0 := by
        rw [pow_succ]; omega
      have hhalf : 2 ^ (n + 1) / 2 = 2 ^ n := by
        rw [pow_succ]; omega
      rw [cost_even_diag (2 ^ (n + 1)) (by positivity) hev, hhalf, ih,
        Nat.size_pow]
      ring

/-! ## The matching lower bound -/

/-- **Clean quadratic floor.** `k² ≤ binaryGcdCost (2^k) (2^k)`. -/
theorem binaryGcdCost_two_pow_diag_lower (k : ℕ) :
    k ^ 2 ≤ binaryGcdCost (2 ^ k) (2 ^ k) := by
  rw [binaryGcdCost_two_pow_diag]; nlinarith [sq_nonneg k]

/-- **Ω((log N)²) on the power-of-two family.** Writing `N = 2^k` so that
    `log₂ N = k`, the cost is bounded below by `(log₂ N)²`. This matches the
    parent's `O((log N)²)` upper bound: the quadratic bound is tight. -/
theorem binaryGcdCost_diag_log_lower (k : ℕ) :
    (Nat.log 2 (2 ^ k)) ^ 2 ≤ binaryGcdCost (2 ^ k) (2 ^ k) := by
  rw [Nat.log_pow (by norm_num)]
  exact binaryGcdCost_two_pow_diag_lower k

/-- **The requested input family.** For every `k` there are positive inputs
    `a = b = 2^k` with `log₂ a = log₂ b = k` whose binary-GCD cost is at least
    `k² = (log N)²`. This exhibits the `Ω((log N)²)` lower bound explicitly. -/
theorem binaryGcdCost_omega_log_sq (k : ℕ) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.log 2 a = k ∧ Nat.log 2 b = k ∧
      k ^ 2 ≤ binaryGcdCost a b :=
  ⟨2 ^ k, 2 ^ k, by positivity, by positivity,
    Nat.log_pow (by norm_num) k, Nat.log_pow (by norm_num) k,
    binaryGcdCost_two_pow_diag_lower k⟩

/-! ## Two-sided squeeze: the cost is Θ((log N)²) on the diagonal family -/

/-- **Matching two-sided bound.** With `L = log₂ a + log₂ b` the combined input
    bit-length, on the diagonal family `a = b = 2^k` the cost satisfies

        (L/2)² ≤ binaryGcdCost a b ≤ (2·L + 2)·(L + 2).

    Both bounds are quadratic in `L`, so the cost is `Θ(L²) = Θ((log N)²)`; the
    parent's `O((log N)²)` upper bound is asymptotically tight, not a loose
    over-estimate. -/
theorem binaryGcdCost_diag_two_sided (k : ℕ) :
    ((Nat.log 2 (2 ^ k) + Nat.log 2 (2 ^ k)) / 2) ^ 2 ≤
        binaryGcdCost (2 ^ k) (2 ^ k) ∧
      binaryGcdCost (2 ^ k) (2 ^ k) ≤
        (2 * (Nat.log 2 (2 ^ k) + Nat.log 2 (2 ^ k)) + 2) *
          (Nat.log 2 (2 ^ k) + Nat.log 2 (2 ^ k) + 2) := by
  have hlog : Nat.log 2 (2 ^ k) = k := Nat.log_pow (by norm_num) k
  refine ⟨?_, ?_⟩
  · -- lower: L/2 = k, so (L/2)² = k² ≤ cost
    rw [hlog, show (k + k) / 2 = k by omega]
    exact binaryGcdCost_two_pow_diag_lower k
  · -- upper: the parent's quadratic bound, specialised to a = b = 2^k
    exact binaryGcdCost_le_quadratic (2 ^ k) (2 ^ k) (by positivity) (by positivity)

end BinaryGcdOQ01OQ01OQ01
