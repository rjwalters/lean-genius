/-
Large Schröder numbers: positivity, strict growth, and an exponential lower bound

Source: Open question from the schroder-numbers gallery family
Status: VERIFIED (0 axioms, 0 sorries)

The large Schröder numbers `Nat.largeSchroder` (OEIS A006318: 1, 2, 6, 22, 90, …)
are defined in Mathlib (`Mathlib/Combinatorics/Enumerative/Schroder.lean`) by the
convolution recurrence

    L 0       = 1
    L (n + 1) = L n + ∑ i ≤ n, L i * L (n - i).

Mathlib records the base values, the recurrence (`largeSchroder_succ`), the parity
fact `even_largeSchroder`, and the small/large bridge `two_mul_smallSchroder_succ`.
It does **not** record any *order* information: positivity, monotonicity, or growth.
We fill that gap with elementary consequences of the recurrence:

  * `largeSchroder_pos`            :  0 < L n
  * `two_mul_largeSchroder_le_succ`:  2 * L n ≤ L (n + 1)        (the doubling step)
  * `largeSchroder_lt_succ`        :  L n < L (n + 1)
  * `strictMono_largeSchroder`     :  StrictMono L
  * `two_pow_le_largeSchroder`     :  2 ^ n ≤ L n                (exponential lower bound)

The doubling step is the crux: in `L (n + 1) = L n + ∑ i ≤ n, L i * L (n - i)` the
single `i = 0` term already equals `L 0 * L n = L n`, so the whole sum is `≥ L n`
and hence `L (n + 1) ≥ L n + L n = 2 * L n`. Strict monotonicity and the `2 ^ n`
bound then follow by induction. We also record positivity for the small Schröder
numbers as a companion.

All proofs are kernel-checked with no `axiom`, `sorry`, or `native_decide`.
-/
import Mathlib

namespace SchroderNumbersOQ01

open Finset
open Nat (largeSchroder smallSchroder)

/-- The large Schröder numbers are strictly positive. -/
theorem largeSchroder_pos : ∀ n, 0 < largeSchroder n
  | 0 => by simp
  | n + 1 => by
      rw [Nat.largeSchroder_succ]
      exact lt_of_lt_of_le (largeSchroder_pos n) (Nat.le_add_right _ _)

/-- The single `i = 0` term of the convolution sum equals `L n`, so the whole sum
is at least `L n`. -/
theorem largeSchroder_le_sum (n : ℕ) :
    largeSchroder n ≤ ∑ i ≤ n, largeSchroder i * largeSchroder (n - i) := by
  have h0 : largeSchroder n
      = largeSchroder 0 * largeSchroder (n - 0) := by simp
  rw [h0]
  exact Finset.single_le_sum
    (f := fun i => largeSchroder i * largeSchroder (n - i))
    (fun i _ => Nat.zero_le _) (Finset.mem_Iic.mpr (Nat.zero_le n))

/-- The **doubling step**: each large Schröder number is at least twice its
predecessor. This is the engine behind both monotonicity and exponential growth. -/
theorem two_mul_largeSchroder_le_succ (n : ℕ) :
    2 * largeSchroder n ≤ largeSchroder (n + 1) := by
  rw [Nat.largeSchroder_succ, two_mul]
  gcongr
  exact largeSchroder_le_sum n

/-- The large Schröder numbers are strictly increasing along the recurrence. -/
theorem largeSchroder_lt_succ (n : ℕ) :
    largeSchroder n < largeSchroder (n + 1) := by
  have hpos := largeSchroder_pos n
  have hdbl := two_mul_largeSchroder_le_succ n
  omega

/-- The large Schröder sequence is strictly monotone. -/
theorem strictMono_largeSchroder : StrictMono largeSchroder :=
  strictMono_nat_of_lt_succ largeSchroder_lt_succ

/-- **Exponential lower bound**: `2 ^ n ≤ L n`. In particular the large Schröder
numbers grow at least geometrically. -/
theorem two_pow_le_largeSchroder (n : ℕ) : 2 ^ n ≤ largeSchroder n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        _ ≤ 2 * largeSchroder n := by gcongr
        _ ≤ largeSchroder (n + 1) := two_mul_largeSchroder_le_succ n

/-- The large Schröder numbers tend to infinity. -/
theorem largeSchroder_atTop : Filter.Tendsto largeSchroder Filter.atTop Filter.atTop :=
  strictMono_largeSchroder.tendsto_atTop

/-- Companion: the small Schröder numbers are also strictly positive. For `n ≥ 1`,
`S (n+1) = L n / 2` with `L n` positive and even, so the quotient is `≥ 1`. -/
theorem smallSchroder_pos : ∀ n, 0 < smallSchroder n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      have h2 : 2 * smallSchroder (n + 2) = largeSchroder (n + 1) :=
        Nat.two_mul_smallSchroder_succ (Nat.succ_ne_zero n)
      have hpos := largeSchroder_pos (n + 1)
      omega

/-! ### Concrete values

The first few large Schröder numbers are `1, 2, 6, 22, 90` and the small ones are
`1, 1, 3, 11, 45`. -/

theorem largeSchroder_three : largeSchroder 3 = 22 := by
  have hset : Finset.Iic 2 = {0, 1, 2} := by decide
  rw [Nat.largeSchroder_succ 2, hset,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [Nat.largeSchroder_zero, Nat.largeSchroder_one, Nat.largeSchroder_two]

theorem largeSchroder_four : largeSchroder 4 = 90 := by
  have hset : Finset.Iic 3 = {0, 1, 2, 3} := by decide
  rw [Nat.largeSchroder_succ 3, hset, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [largeSchroder_three, Nat.largeSchroder_zero, Nat.largeSchroder_one,
    Nat.largeSchroder_two]

/-- Sanity check against the doubling bound at a concrete value: `2 * L 3 = 44 ≤ 90 = L 4`. -/
example : 2 * largeSchroder 3 ≤ largeSchroder 4 := two_mul_largeSchroder_le_succ 3

end SchroderNumbersOQ01
