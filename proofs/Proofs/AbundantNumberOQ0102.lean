/-
  The smallest ODD abundant number is 945.

  A positive integer `n` is *abundant* when the sum of its proper divisors
  exceeds `n` (`Nat.Abundant n : n < ∑ d ∈ n.properDivisors, d`). The smallest
  abundant number is 12 (see `AbundantNumberOQ01.lean`), but 12 is even. Every
  abundant number below 945 turns out to be even; the smallest *odd* abundant
  number is `945 = 3³·5·7`, whose proper divisors sum to
  `1+3+5+7+9+15+21+27+35+45+63+105+135+189+315 = 975 > 945`
  (equivalently `σ(945) = 40·6·8 = 1920 > 1890 = 2·945`). This is OEIS A005231.

  ## Staying axiom-free over a large range

  The minimality claim quantifies over the 472 odd numbers below 945. Discharging
  `∀ n < 945, Odd n → ¬ Nat.Abundant n` by `decide` directly on Mathlib's
  `Nat.Abundant` would force the kernel to evaluate `Finset.filter`/`Finset.sum`
  over `Finset.range n` for each `n` — a `Quotient`-backed computation the Lean
  kernel reduces very slowly, risking a memory blow-up at this scale.

  Instead we compute the proper-divisor sum with a `List`-based function `pdSum`,
  which the kernel reduces cheaply (structural recursion on `List` plus
  GMP-accelerated `Nat.mod` for the divisibility tests, no `Quotient`). The
  bridge lemma `pdSum_eq` identifies it with `∑ d ∈ n.properDivisors, d` once,
  symbolically; the bounded check then runs on `pdSum` and `Odd n` short-circuits
  the even cases. The whole development uses kernel `decide` only — no
  `native_decide`, hence no `Lean.ofReduceBool`: the result is axiom-free.
-/
import Mathlib

namespace AbundantNumberOQ0102

/-- `List`-based sum of the proper divisors of `n`: the divisors `d` with
`d < n` (and `d ≥ 1`, automatic since `0 ∣ n` only for `n = 0`). Defined over
`List.range n` so the kernel can reduce it without `Finset`/`Quotient` overhead. -/
def pdSum (n : ℕ) : ℕ := ((List.range n).filter (fun d => decide (d ∣ n))).sum

/-- Bridge: the `List`-based filtered sum over `List.range n` agrees with the
`Finset`-based filtered sum over `Finset.range n`. Proved by induction so it does
not depend on exact Mathlib lemma names; used purely symbolically (never under
`decide`). -/
theorem listRange_filter_sum_eq (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((List.range n).filter (fun d => decide (p d))).sum
      = ∑ i ∈ (Finset.range n).filter p, i := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filter_append, List.sum_append, ih,
        Finset.range_succ, Finset.filter_insert]
    by_cases hk : p k
    · rw [if_pos hk, Finset.sum_insert (by simp)]
      simp [List.filter_cons, hk, Nat.add_comm]
    · rw [if_neg hk]
      simp [List.filter_cons, hk]

/-- `pdSum n` equals the proper-divisor sum used in `Nat.Abundant` (for `n ≠ 0`). -/
theorem pdSum_eq (n : ℕ) (hn : n ≠ 0) :
    pdSum n = ∑ d ∈ n.properDivisors, d := by
  rw [pdSum, listRange_filter_sum_eq n (· ∣ n), Nat.filter_dvd_eq_properDivisors hn]

/-- **945 is abundant.** Its proper divisors sum to `975 > 945`. -/
theorem abundant_945 : Nat.Abundant 945 := by
  unfold Nat.Abundant
  rw [← pdSum_eq 945 (by decide)]
  decide

/-- 945 is odd. -/
theorem odd_945 : Odd (945 : ℕ) := by decide

/-- The bounded, kernel-cheap minimality check: every odd `n < 945` has
proper-divisor sum at most `n`, i.e. is not abundant. The `Odd n` hypothesis is
evaluated first, so the even cases are discharged immediately without computing
`pdSum`. -/
set_option maxHeartbeats 4000000 in
theorem check_odd_below : ∀ n < 945, Odd n → pdSum n ≤ n := by decide

/-- No odd number below 945 is abundant. -/
theorem not_abundant_odd_below (n : ℕ) (hlt : n < 945) (hodd : Odd n) :
    ¬ Nat.Abundant n := by
  have hn : n ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  unfold Nat.Abundant
  rw [← pdSum_eq n hn]
  exact Nat.not_lt.mpr (check_odd_below n hlt hodd)

/-- **945 is the smallest odd abundant number.** It is odd and abundant, and it
is a lower bound for the set of odd abundant numbers. -/
theorem smallest_odd_abundant :
    IsLeast {n : ℕ | Odd n ∧ Nat.Abundant n} 945 := by
  refine ⟨⟨odd_945, abundant_945⟩, ?_⟩
  intro n hn
  obtain ⟨hodd, hab⟩ := hn
  by_contra h
  push_neg at h
  exact not_abundant_odd_below n h hodd hab

end AbundantNumberOQ0102
