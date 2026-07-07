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

  Part 2 (recovered from draft PR #32737) complements the even/even diagonal
  with the **coprime odd worst-case family** `N = 2^(k+1) − 1` against `b = 1`,
  which forces the subtract-and-halve branch at every step:

  * `cost_family`
        2 · binaryGcdCost (2^(k+1) − 1) 1 = (k+1)·(k+4)   (exact closed form)
  * `binaryGcdCost_omega_lower`
        (log₂ N)² ≤ 2 · binaryGcdCost N 1                 (Ω((log N)²), gcd = 1)
  * `binaryGcdCost_family_matching`
        two-sided Θ((log N)²) squeeze on the coprime family

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

/-! ## Part 2: the coprime odd worst-case family `(2^(k+1) − 1, 1)`

The diagonal family above is even/even: every step takes the halving branch and
`gcd = N` itself. A critic could object that the *coprime* case — where the
algorithm must do real subtraction work — was not exhibited. This section
(recovered from draft PR #32737) closes that gap with the all-ones odd number
against `1`:

    N = 2^(k+1) − 1  (binary: k+1 ones),  b = 1,  gcd(N, 1) = 1.

Both operands are odd and `N > 1`, so every reduction takes the
subtract-then-halve branch, `(2^(m+1) − 1, 1) → (2^m − 1, 1)`, at per-step cost
`Nat.size (2^(m+1) − 1) + Nat.size 1 = m + 2`. Summing the arithmetic
progression gives the exact division-free closed form

    2 · binaryGcdCost (2^(k+1) − 1) 1 = (k+1)(k+4),

hence `(log₂ N)² ≤ 2 · binaryGcdCost N 1` with `log₂ N = k`: the quadratic
upper bound is tight on a coprime family exercising the subtraction branch,
not only on the degenerate halving diagonal. -/

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

/-- Base of the family recursion: `binaryGcdCost 1 1 = 2` (one odd/odd step of
    cost `size 1 + size 1 = 2`, landing on `(1, 0)`). -/
theorem cost_base : binaryGcdCost 1 1 = 2 := by
  show binaryGcdCost (0 + 1) (0 + 1) = 2
  rw [binaryGcdCost.eq_3, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  norm_num [Nat.sub_self, Nat.zero_div, binaryGcdCost_zero_right, Nat.size_one]

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
  rw [hsize, Nat.size_one]

/-- **Exact cost of the coprime worst-case family (division-free).** The
    all-ones odd number `2^(k+1) - 1` run against `1` costs exactly
    `(k+1)(k+4)/2` bit operations, here stated as a doubled identity to stay
    in `ℕ`. -/
theorem cost_family (k : ℕ) :
    2 * binaryGcdCost (2 ^ (k + 1) - 1) 1 = (k + 1) * (k + 4) := by
  induction k with
  | zero =>
    norm_num [show (2 : ℕ) ^ (0 + 1) - 1 = 1 from by norm_num, cost_base]
  | succ n ih =>
    show 2 * binaryGcdCost (2 ^ (n + 2) - 1) 1 = (n + 2) * (n + 5)
    rw [cost_step, Nat.mul_add, ih]
    ring

/-- **Quadratic lower bound (odd family).** In the bit-length parameter `k`,
    the coprime worst-case family costs at least `(k+1)²/2` bit operations. -/
theorem binaryGcdCost_lower_bound (k : ℕ) :
    (k + 1) ^ 2 ≤ 2 * binaryGcdCost (2 ^ (k + 1) - 1) 1 := by
  have h := cost_family k
  nlinarith [h]

/-- **Matching Ω((log N)²) lower bound on a coprime family.** For every `k`,
    the binary-GCD input `N = 2^(k+1) - 1` has `Nat.log 2 N = k`, yet its total
    bit-operation cost obeys `(log₂ N)² ≤ 2 · binaryGcdCost N 1`. Hence
    `binaryGcdCost N 1` is `Ω((log N)²)` already for coprime inputs driven
    through the subtraction branch. -/
theorem binaryGcdCost_omega_lower (k : ℕ) :
    (Nat.log 2 (2 ^ (k + 1) - 1)) ^ 2 ≤ 2 * binaryGcdCost (2 ^ (k + 1) - 1) 1 := by
  have hk : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have hp1 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have hlog : Nat.log 2 (2 ^ (k + 1) - 1) = k :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  rw [hlog]
  calc k ^ 2 ≤ (k + 1) ^ 2 := by nlinarith
    _ ≤ 2 * binaryGcdCost (2 ^ (k + 1) - 1) 1 := binaryGcdCost_lower_bound k

/-- **Tightness on the coprime family.** For `N = 2^(k+1) - 1` (with `b = 1`)
    the total cost is squeezed between `(log₂ N)²/2` and the parent's quadratic
    upper bound — both `Θ((log N)²)`. -/
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

-- Axiom audit: headline theorems of both families (expect only the
-- foundational propext / Classical.choice / Quot.sound).
#print axioms BinaryGcdOQ01OQ01OQ01.binaryGcdCost_two_pow_diag
#print axioms BinaryGcdOQ01OQ01OQ01.binaryGcdCost_diag_two_sided
#print axioms BinaryGcdOQ01OQ01OQ01.cost_family
#print axioms BinaryGcdOQ01OQ01OQ01.binaryGcdCost_omega_lower
#print axioms BinaryGcdOQ01OQ01OQ01.binaryGcdCost_family_matching
