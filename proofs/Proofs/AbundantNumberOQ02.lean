/-
  The smallest odd abundant number is 945.

  A positive integer `n` is *abundant* when the sum of its proper divisors
  exceeds `n` (equivalently `σ(n) > 2n`). The smallest abundant number is 12
  (see `AbundantNumberOQ01.lean`), but 12, and indeed every abundant number
  below 945, is even. The smallest *odd* abundant number is 945 = 3³·5·7:
  its divisors sum to `σ(945) = 40·6·8 = 1920 > 1890 = 2·945`, and no smaller
  odd number is abundant.

  The minimality half is a bounded check `∀ n < 945, Odd n → ¬ Nat.Abundant n`.
  Unlike the `n < 12` check in `AbundantNumberOQ01.lean`, this range is far too
  large to discharge by `decide` directly on Mathlib's `Nat.Abundant`: that
  predicate unfolds to a `Finset` divisor sum whose kernel reduction is
  structural (Multiset/`range` folds) and blows up well before 945.

  This file supplies the missing ingredient: a **kernel-reducible** sum-of-
  divisors `sigmaFast`, defined by plain structural recursion on `ℕ` (no
  `Finset`/`Multiset` at reduction time), proved equal to Mathlib's canonical
  divisor sum, and used to run the bounded minimality check by kernel `decide`.
  Because `decide` reduces in the kernel — not `native_decide` — the result is
  axiom-free (`verified`, no `Lean.ofReduceBool`).
-/
import Mathlib

namespace AbundantNumberOQ02

open Finset

/-- A kernel-efficient partial sum of divisors: `∑_{d=1}^{m} (d if d ∣ n else 0)`,
computed by structural recursion on `m`. No `Finset`/`Multiset` appears, so the
Lean kernel reduces it through ordinary (GMP-accelerated) `ℕ` arithmetic. -/
def sigmaAux (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | (m + 1) => (if (m + 1) ∣ n then (m + 1) else 0) + sigmaAux n m

/-- The full sum of divisors `σ(n) = ∑_{d ∣ n} d`, computed kernel-efficiently
by summing the divisor contributions of every `d ∈ [1, n]`. -/
def sigmaFast (n : ℕ) : ℕ := sigmaAux n n

/-- `sigmaAux n m` is the `Finset` sum `∑_{d ∈ range (m+1)} (d if d ∣ n else 0)`.
Proved by structural induction on `m`; this is the bridge from the kernel-fast
recursion to Mathlib's `Finset` divisor machinery. -/
theorem sigmaAux_eq_sum (n m : ℕ) :
    sigmaAux n m = ∑ d ∈ Finset.range (m + 1), (if d ∣ n then d else 0) := by
  induction m with
  | zero => simp [sigmaAux]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [sigmaAux]
    ring

/-- `sigmaFast` agrees with Mathlib's canonical divisor sum `∑_{d ∣ n} d` for
every positive `n`. The contribution-indicator sum over `range (n+1)` collapses
to the sum over `n.divisors` because `d ∣ n` with `n ≠ 0` forces `1 ≤ d ≤ n`. -/
theorem sigmaFast_eq_sigma {n : ℕ} (hn : n ≠ 0) :
    sigmaFast n = ∑ d ∈ n.divisors, d := by
  rw [sigmaFast, sigmaAux_eq_sum, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨-, hd⟩
    exact ⟨hd, hn⟩
  · rintro ⟨hd, -⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd), hd⟩

/-- A number is abundant exactly when twice it is below the fast divisor sum. -/
theorem abundant_iff_sigmaFast {n : ℕ} (hn : n ≠ 0) :
    Nat.Abundant n ↔ 2 * n < sigmaFast n := by
  rw [Nat.Abundant, sigmaFast_eq_sigma hn,
    Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

set_option maxRecDepth 4000 in
/-- **945 is abundant.** `σ(945) = 1920 > 1890 = 2·945`. The single divisor-sum
`sigmaFast 945` reduces in the kernel. -/
theorem abundant_945 : Nat.Abundant 945 :=
  (abundant_iff_sigmaFast (by norm_num)).mpr (by decide)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
/-- **No odd number below 945 is abundant.** The bounded quantifier is decidable
via `Nat.decidableBallLT`; for each *odd* `n < 945` the kernel reduces the fast
divisor sum `sigmaFast n` and checks `sigmaFast n ≤ 2n` (even `n` are discharged
without computing any sum, since `Odd n` is false). This is the step that the
direct `Finset`-based `decide` cannot perform at this scale; the raised
`maxHeartbeats` covers the elaborator's whnf check of the ~470 odd-case sum. -/
theorem not_abundant_odd_below_945 : ∀ n < 945, Odd n → sigmaFast n ≤ 2 * n := by
  decide

/-- **The smallest odd abundant number is 945.** It is odd and abundant, and it
is a lower bound for the set of odd abundant numbers. Proved axiom-free: the
minimality bound is a kernel `decide` over the kernel-reducible `sigmaFast`
(no `native_decide`, hence no `Lean.ofReduceBool`). -/
theorem smallest_odd_abundant :
    IsLeast {n : ℕ | Odd n ∧ Nat.Abundant n} 945 := by
  refine ⟨⟨by decide, abundant_945⟩, ?_⟩
  rintro n ⟨hodd, habund⟩
  by_contra hlt
  push_neg at hlt
  have hn : n ≠ 0 := by rintro rfl; exact (by decide : ¬ Odd 0) hodd
  rw [abundant_iff_sigmaFast hn] at habund
  have hle := not_abundant_odd_below_945 n hlt hodd
  omega

end AbundantNumberOQ02
