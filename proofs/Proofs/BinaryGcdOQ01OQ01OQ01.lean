/-
  Binary GCD OQ-01-OQ-01-OQ-01: a matching Ω((log N)²) lower bound for the
  total bit-operation cost of Stein's binary GCD.

  The grandparent `BinaryGcdOQ01` counts reduction *steps* (`binaryGcdSteps`)
  and bounds them by `2*(log₂ a + log₂ b) + 2`. The parent `BinaryGcdOQ01OQ01`
  charges each step its honest bit cost `Nat.size a + Nat.size b`, accumulates
  it into `binaryGcdCost`, and proves the classical **upper** bound

      binaryGcdCost a b ≤ (2*(log₂ a + log₂ b) + 2) * (log₂ a + log₂ b + 2)
                        = O((log N)²).

  The open question left by that file (its `openQuestions[0]`) asks for a
  **matching lower bound**: an input family for which `binaryGcdCost` is
  `Ω((log N)²)`, showing the quadratic upper bound is tight and not merely an
  over-estimate. This file answers it.

  The worst-case family is the all-ones odd number against `1`:

      N = 2^(k+1) - 1   (binary: k+1 ones),   b = 1.

  Both operands are odd and `N > 1`, so a single reduction subtracts `1` and
  halves, sending `(2^(m+1) - 1, 1) → (2^m - 1, 1)` at a per-step cost of
  `Nat.size (2^(m+1) - 1) + Nat.size 1 = (m+1) + 1 = m + 2`. Summing the arithmetic
  progression `2, 3, …, k+2` gives the exact closed form

      binaryGcdCost (2^(k+1) - 1) 1 = (k+1)(k+4) / 2,

  stated here division-free as `2 * binaryGcdCost (2^(k+1) - 1) 1 = (k+1)(k+4)`.
  Since `log₂ (2^(k+1) - 1) = k`, this is `Ω(k²) = Ω((log N)²)`, matching the
  parent's `O((log N)²)` upper bound: the binary GCD really can cost a quadratic
  number of bit operations.

  Main results.

  * `cost_family`
        2 * binaryGcdCost (2^(k+1) - 1) 1 = (k+1) * (k+4)
    the exact per-family cost (division-free).

  * `binaryGcdCost_lower_bound`
        (k+1)^2 ≤ 2 * binaryGcdCost (2^(k+1) - 1) 1
    the clean quadratic lower bound in the bit-length parameter `k`.

  * `binaryGcdCost_omega_lower`
        (log₂ N)^2 ≤ 2 * binaryGcdCost N 1        (N = 2^(k+1) - 1)
    the Ω((log N)²) statement in the parent's `Nat.log 2` units.

  * `binaryGcdCost_family_matching`
    the lower bound together with the parent's quadratic upper bound, both
    Θ((log N)²): the quadratic total-cost bound is tight.

  All results are axiom-free (only the foundational
  propext / Classical.choice / Quot.sound), 0 sorries, no `native_decide`.

  References:
  - Stein (1967), Binary GCD Algorithm
  - Brent (1976), analysis of the binary GCD
  - Knuth, TAOCP 4.5.2
  - BinaryGcdOQ01OQ01.lean (total cost `binaryGcdCost` + O((log N)²) upper bound)
-/
import Mathlib
import Proofs.BinaryGcdOQ01OQ01

namespace BinaryGcdOQ01OQ01OQ01

open Nat BinaryGcdOQ01 BinaryGcdOQ01OQ01

/-! ## Bit-length helpers -/

/-- The bit-length of `2^k - 1` is exactly `k`: in binary it is a block of `k`
    ones. -/
theorem size_two_pow_sub_one (k : ℕ) : Nat.size (2 ^ k - 1) = k := by
  cases k with
  | zero => simp
  | succ n =>
    have hpow : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    apply le_antisymm
    · rw [Nat.size_le]; omega
    · exact Nat.lt_size.mpr (by omega)

/-- `Nat.size 1 = 1` (specialisation of `size_two_pow_sub_one` at `k = 1`). -/
theorem size_one : Nat.size 1 = 1 := by
  have h := size_two_pow_sub_one 1
  norm_num at h
  exact h

/-! ## The worst-case recursion

On the family `(2^(m+1) - 1, 1)` both operands are odd and the first exceeds the
second, so the binary GCD takes the "subtract then halve" branch:
`(2^(m+1) - 1, 1) → (2^m - 1, 1)`. -/

/-- Base of the family recursion: `binaryGcdCost 1 1 = 2` (one odd/odd step of
    cost `size 1 + size 1 = 2`, landing on `(1, 0)`). -/
theorem cost_base : binaryGcdCost 1 1 = 2 := by
  show binaryGcdCost (0 + 1) (0 + 1) = 2
  rw [binaryGcdCost.eq_3, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  norm_num [Nat.sub_self, Nat.zero_div, binaryGcdCost_zero_right, size_one]

/-- One reduction step of the worst-case family: peeling `(2^(k+2) - 1, 1)`
    costs `size (2^(k+2) - 1) + size 1 = (k+2) + 1 = k+3` and reduces to
    `(2^(k+1) - 1, 1)`. -/
theorem cost_step (k : ℕ) :
    binaryGcdCost (2 ^ (k + 2) - 1) 1
      = (k + 3) + binaryGcdCost (2 ^ (k + 1) - 1) 1 := by
  have hk : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have hp1 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have hp2 : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
  obtain ⟨a', ha'⟩ : ∃ a', 2 ^ (k + 2) - 1 = a' + 1 := ⟨2 ^ (k + 2) - 2, by omega⟩
  rw [ha']
  show binaryGcdCost (a' + 1) (0 + 1)
      = (k + 3) + binaryGcdCost (2 ^ (k + 1) - 1) 1
  rw [binaryGcdCost.eq_3, if_neg (by omega), if_neg (by decide), if_pos (by omega)]
  have harg : (a' + 1 - (0 + 1)) / 2 = 2 ^ (k + 1) - 1 := by omega
  have hsize : Nat.size (a' + 1) = k + 2 := by
    rw [← ha']; exact size_two_pow_sub_one (k + 2)
  rw [harg]
  simp only [Nat.zero_add]
  rw [hsize, size_one]
  omega

/-! ## The matching lower bound -/

/-- **Exact cost of the worst-case family (division-free).** The all-ones odd
    number `2^(k+1) - 1` run against `1` costs exactly `(k+1)(k+4)/2` bit
    operations, here stated as a doubled identity to stay in `ℕ`. -/
theorem cost_family (k : ℕ) :
    2 * binaryGcdCost (2 ^ (k + 1) - 1) 1 = (k + 1) * (k + 4) := by
  induction k with
  | zero =>
    norm_num [show (2 : ℕ) ^ (0 + 1) - 1 = 1 from by norm_num, cost_base]
  | succ n ih =>
    show 2 * binaryGcdCost (2 ^ (n + 2) - 1) 1 = (n + 2) * (n + 5)
    rw [cost_step, Nat.mul_add, ih]
    ring

/-- **Quadratic lower bound.** In the bit-length parameter `k`, the worst-case
    family costs at least `(k+1)²/2` bit operations. Together with the parent's
    `O((log N)²)` upper bound this shows the quadratic total cost is genuine. -/
theorem binaryGcdCost_lower_bound (k : ℕ) :
    (k + 1) ^ 2 ≤ 2 * binaryGcdCost (2 ^ (k + 1) - 1) 1 := by
  have h := cost_family k
  nlinarith [h]

/-- **Matching Ω((log N)²) lower bound.** For every `k`, the binary-GCD input
    `N = 2^(k+1) - 1` has `Nat.log 2 N = k`, yet its total bit-operation cost
    obeys `(log₂ N)² ≤ 2 · binaryGcdCost N 1`. Hence `binaryGcdCost N 1` is
    `Ω((log N)²)`: the parent's `O((log N)²)` upper bound is tight, not an
    over-estimate. -/
theorem binaryGcdCost_omega_lower (k : ℕ) :
    (Nat.log 2 (2 ^ (k + 1) - 1)) ^ 2 ≤ 2 * binaryGcdCost (2 ^ (k + 1) - 1) 1 := by
  have hk : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have hp1 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have hlog : Nat.log 2 (2 ^ (k + 1) - 1) = k :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  rw [hlog]
  calc k ^ 2 ≤ (k + 1) ^ 2 := by nlinarith
    _ ≤ 2 * binaryGcdCost (2 ^ (k + 1) - 1) 1 := binaryGcdCost_lower_bound k

/-- **Tightness of the quadratic total-cost bound.** For the family
    `N = 2^(k+1) - 1` (with `b = 1`) the total cost is squeezed between
    `(log₂ N)²/2` and the parent's quadratic upper bound — both `Θ((log N)²)`. -/
theorem binaryGcdCost_family_matching (k : ℕ) :
    (Nat.log 2 (2 ^ (k + 1) - 1)) ^ 2 ≤ 2 * binaryGcdCost (2 ^ (k + 1) - 1) 1
      ∧ binaryGcdCost (2 ^ (k + 1) - 1) 1
          ≤ (2 * (Nat.log 2 (2 ^ (k + 1) - 1) + Nat.log 2 1) + 2)
              * (Nat.log 2 (2 ^ (k + 1) - 1) + Nat.log 2 1 + 2) := by
  have hpos : 0 < 2 ^ (k + 1) - 1 := by
    have h2 : 2 ≤ 2 ^ (k + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact ⟨binaryGcdCost_omega_lower k,
    BinaryGcdOQ01OQ01.binaryGcdCost_le_quadratic _ 1 hpos (by norm_num)⟩

end BinaryGcdOQ01OQ01OQ01
