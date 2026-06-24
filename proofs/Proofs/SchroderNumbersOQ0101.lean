/-
Large Schröder numbers: the sharp tripling step and the `2·3^(n-1)` lower bound

Source: Open question (oq-01-oq-01) from the schroder-numbers gallery family.
Status: VERIFIED (0 axioms, 0 sorries).

The parent entry (`SchroderNumbersOQ01`) established the **doubling step**
`2·L n ≤ L (n+1)` by keeping only the `i = 0` term `L 0 · L n = L n` of the
convolution sum

    L (n + 1) = L n + ∑ i ≤ n, L i · L (n - i).

That is wasteful for `n ≥ 1`: the symmetric `i = n` term `L n · L 0 = L n` is a
*second, distinct* summand, so the sum is at least `2·L n` and therefore

    L (n + 1) = L n + (sum) ≥ L n + 2·L n = 3·L n.

This file proves that **tripling** step and its exponential consequence:

  * `two_mul_largeSchroder_le_sum`      :  2·L n ≤ ∑ i ≤ n, L i·L (n-i)   (n ≥ 1)
  * `three_mul_largeSchroder_le_succ`   :  3·L n ≤ L (n+1)                (n ≥ 1)
  * `two_mul_three_pow_le_largeSchroder_succ` : 2·3^n ≤ L (n+1)           (all n)
  * `two_mul_three_pow_pred_le_largeSchroder` : 2·3^(n-1) ≤ L n           (n ≥ 1)

**Sharpness.** The constant `3` cannot be raised: equality `3·L 1 = L 2 = 6`
holds at `n = 1`, so no constant `c > 3` satisfies `c·L n ≤ L (n+1)` for all
`n ≥ 1`. Likewise the lower bound is attained, `L 1 = 2·3^0` and `L 2 = 2·3^1`.
The hypothesis `n ≥ 1` is genuinely needed: at `n = 0` we have
`3·L 0 = 3 > 2 = L 1`, so tripling fails. (All three facts are recorded as
`example`s below.)

The large Schröder numbers `Nat.largeSchroder` (OEIS A006318: 1, 2, 6, 22, 90, …)
and the recurrence `Nat.largeSchroder_succ` are from Mathlib
(`Mathlib/Combinatorics/Enumerative/Schroder.lean`). All proofs are
kernel-checked with no `axiom`, `sorry`, or `native_decide`.
-/
import Mathlib

namespace SchroderNumbersOQ0101

open Finset
open Nat (largeSchroder)

/-- **Two-term sum bound** (the engine behind tripling). For `n ≥ 1` the indices
`0` and `n` are distinct, and the corresponding convolution terms are
`L 0 · L n = L n` and `L n · L 0 = L n`. Their sum `2·L n` is a lower bound for
the full nonnegative sum. -/
theorem two_mul_largeSchroder_le_sum (n : ℕ) (hn : 1 ≤ n) :
    2 * largeSchroder n ≤ ∑ i ≤ n, largeSchroder i * largeSchroder (n - i) := by
  have hne : (0 : ℕ) ≠ n := by omega
  have hsub : ({0, n} : Finset ℕ) ⊆ Finset.Iic n := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · subst h; exact Finset.mem_Iic.mpr (Nat.zero_le n)
    · rw [Finset.mem_singleton] at h; subst h; exact Finset.mem_Iic.mpr le_rfl
  -- The pair `{0, n}` contributes exactly `2 * L n`.
  have hpair :
      ∑ i ∈ ({0, n} : Finset ℕ), largeSchroder i * largeSchroder (n - i)
        = 2 * largeSchroder n := by
    rw [Finset.sum_pair hne]
    simp [two_mul]
  calc 2 * largeSchroder n
      = ∑ i ∈ ({0, n} : Finset ℕ), largeSchroder i * largeSchroder (n - i) := hpair.symm
    _ ≤ ∑ i ≤ n, largeSchroder i * largeSchroder (n - i) :=
        Finset.sum_le_sum_of_subset hsub

/-- The **tripling step**: for `n ≥ 1`, each large Schröder number is at least
three times its predecessor. Sharp at `n = 1` (`3·L 1 = L 2 = 6`). -/
theorem three_mul_largeSchroder_le_succ (n : ℕ) (hn : 1 ≤ n) :
    3 * largeSchroder n ≤ largeSchroder (n + 1) := by
  rw [Nat.largeSchroder_succ]
  have h := two_mul_largeSchroder_le_sum n hn
  omega

/-- **Exponential lower bound**, shift-indexed to avoid `n - 1`: `2·3^n ≤ L (n+1)`
for every `n`. Proof by induction, driving each step with the tripling lemma. -/
theorem two_mul_three_pow_le_largeSchroder_succ (n : ℕ) :
    2 * 3 ^ n ≤ largeSchroder (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have htrip := three_mul_largeSchroder_le_succ (n + 1) (by omega)
      calc 2 * 3 ^ (n + 1)
          = 3 * (2 * 3 ^ n) := by ring
        _ ≤ 3 * largeSchroder (n + 1) := by gcongr
        _ ≤ largeSchroder (n + 1 + 1) := htrip

/-- **Exponential lower bound** in the stated form: `2·3^(n-1) ≤ L n` for `n ≥ 1`.
Attained at `n = 1` and `n = 2`. -/
theorem two_mul_three_pow_pred_le_largeSchroder (n : ℕ) (hn : 1 ≤ n) :
    2 * 3 ^ (n - 1) ≤ largeSchroder n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using two_mul_three_pow_le_largeSchroder_succ m

/-! ### Sharpness witnesses -/

/-- Tripling is attained at `n = 1`: `3·L 1 = L 2 = 6`. Hence the constant `3` is
the largest possible: no `c > 3` has `c·L n ≤ L (n+1)` for all `n ≥ 1`. -/
example : 3 * largeSchroder 1 = largeSchroder 2 := by
  norm_num [Nat.largeSchroder_one, Nat.largeSchroder_two]

/-- The lower bound is attained at `n = 2`: `2·3^(2-1) = 6 = L 2`. -/
example : 2 * 3 ^ (2 - 1) = largeSchroder 2 := by
  norm_num [Nat.largeSchroder_two]

/-- The hypothesis `n ≥ 1` is necessary: at `n = 0`, tripling fails because
`3·L 0 = 3 > 2 = L 1`. -/
example : ¬ 3 * largeSchroder 0 ≤ largeSchroder 1 := by
  norm_num [Nat.largeSchroder_zero, Nat.largeSchroder_one]

end SchroderNumbersOQ0101
