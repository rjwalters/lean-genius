import Mathlib

/-
# Shallow-Diagonal Sums with Stride recover Lagged Fibonacci Recurrences (OQ-08-OQ-02)

Parent entry `combinations-formula-oq-08` proves that the Fibonacci numbers are the sums
along the **shallow diagonals** of Pascal's triangle,

  `fib (n + 1) = ∑ k ∈ range (n + 1), C(n - k, k)`,

and the follow-up `combinations-formula-oq-08-oq-01` re-derives the Fibonacci recurrence
`F_{n+2} = F_{n+1} + F_n` from that sum by applying Pascal's rule term-by-term.

This entry answers the open question raised there:

  *Does the analogous shallow-diagonal sum with a fixed stride `s` (stepping `s` columns
  per row) recover a higher-order / lagged recurrence, and can that be formalized
  uniformly?*

**Answer: yes, uniformly.**  Writing the stride as `s = t + 1`, define the stride-`(t+1)`
diagonal total

  `Dg t n := ∑ k ∈ range (n + 1), C(n - t·k, k)`.

The single theorem `Dg_recurrence` shows that, **for every stride `t + 1` and every `n`**,

  `Dg t (n + t + 1) = Dg t (n + t) + Dg t n`,

i.e. `Dg t` satisfies the *lagged Fibonacci recurrence* `a(m) = a(m-1) + a(m-(t+1))`.  The
proof is pure Pascal's rule: the whole content is the term identity `stride_term`, which
splits one diagonal entry into the two entries feeding it under the stride, handled
uniformly in `t` (including the truncated tail where the entries vanish).

Two specializations pin down the "recovers higher-order recurrence numbers" claim:

* `Dg_zero : Dg 0 n = 2 ^ n`         — stride `1` gives the row sums `2ⁿ`
  (recurrence `a(m) = 2·a(m-1)`, the degenerate lag-`1` case);
* `Dg_one  : Dg 1 n = fib (n + 1)`   — stride `2` gives the Fibonacci diagonals
  (recurrence `a(m) = a(m-1) + a(m-2)`).

The stride-`3` case `Dg 2` is the lag-`2` recurrence `a(m) = a(m-1) + a(m-3)` — Narayana's
cows / the "Padovan-like" sequence — obtained as `Dg_recurrence 2`.

## Proof of the recurrence (sketch)

The `k`-th entry on diagonal `n + t + 1` of the stride-`(t+1)` family is
`C(n + t + 1 - t·k, k)`.  Pascal's rule `C(a+1, b+1) = C(a, b) + C(a, b+1)` applied to it
(when the top index does not truncate) yields, after matching indices,

  `C(n+t+1 - t(k+1), k+1) = C(n+t - t(k+1), k+1) + C(n - t·k, k)`   (`stride_term`),

i.e. it splits into the entry directly above it on diagonal `n + t` and the entry `t`
steps back on diagonal `n`.  Summing over `k` and peeling the constant `k = 0` term gives
the recurrence.  Where the top index truncates (`t·(k+1) > n + t`), both entries are `0`
and the identity holds trivially — this uniform handling of the tail is what lets a single
statement cover all strides.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ08OQ02

open Finset

/-- `Dg t n` is the total along the shallow diagonal of Pascal's triangle taken with
    **stride `t + 1`** (stepping `t + 1` columns per row):

      `Dg t n = C(n, 0) + C(n - t, 1) + C(n - 2t, 2) + ⋯ = ∑ₖ C(n - t·k, k)`.

    Stride `1` (`t = 0`) gives the row sums `2ⁿ`; stride `2` (`t = 1`) gives the Fibonacci
    shallow diagonals; stride `t + 1` gives the lag-`t` recurrence `a(m) = a(m-1) + a(m-t-1)`.
    Terms with `t·k > n` vanish, so the generous range `range (n + 1)` is harmless. -/
def Dg (t n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.choose (n - t * k) k

/-- **The stride term identity — the combinatorial core.**
    One diagonal entry on level `n + t + 1` splits, by Pascal's rule, into the entry
    directly above it on level `n + t` and the entry `t` columns back on level `n`.
    Holds uniformly in `t` and `k`: where the top index truncates the two entries vanish
    and both sides are `0`. -/
theorem stride_term (t n k : ℕ) :
    Nat.choose (n + t + 1 - t * (k + 1)) (k + 1)
      = Nat.choose (n + t - t * (k + 1)) (k + 1) + Nat.choose (n - t * k) k := by
  rcases le_or_gt (t * (k + 1)) (n + t) with hle | hlt
  · -- No truncation: the top index is a successor, apply Pascal directly.
    have hb : n + t + 1 - t * (k + 1) = (n + t - t * (k + 1)) + 1 := by omega
    have hc : n + t - t * (k + 1) = n - t * k := by rw [Nat.mul_succ]; omega
    rw [hb, Nat.choose_succ_succ, hc, Nat.add_comm]
  · -- Truncation: both top indices are `0`, and `k ≥ 1`, so both sides are `0`.
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp only [Nat.zero_add, Nat.mul_one] at hlt; omega
      · exact h
    have h1 : n + t + 1 - t * (k + 1) = 0 := by omega
    have h2 : n + t - t * (k + 1) = 0 := by omega
    have h3 : n - t * k = 0 := by
      have hlt' := hlt; rw [Nat.mul_succ] at hlt'; omega
    have hz : Nat.choose 0 k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2, h3, hz]
    omega

/-- **The stride recurrence — uniform in the stride `t + 1`.**
    For every stride `t + 1` and every `n`, the stride diagonal totals satisfy the lagged
    Fibonacci recurrence `a(m) = a(m-1) + a(m-(t+1))`, derived purely by Pascal's rule.
    Specializes to the Fibonacci recurrence (`t = 1`) and to `2ⁿ`'s doubling (`t = 0`). -/
theorem Dg_recurrence (t n : ℕ) : Dg t (n + t + 1) = Dg t (n + t) + Dg t n := by
  -- Expand the LHS, peel the `k = 0` term, and split each remaining term via `stride_term`.
  have hLHS : Dg t (n + t + 1)
      = (∑ k ∈ range (n + t + 1),
          (Nat.choose (n + t - t * (k + 1)) (k + 1) + Nat.choose (n - t * k) k)) + 1 := by
    unfold Dg
    rw [Finset.sum_range_succ' (fun k => Nat.choose (n + t + 1 - t * k) k) (n + t + 1)]
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.choose_zero_right]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact stride_term t n k
  rw [hLHS, Finset.sum_add_distrib]
  -- First sum + 1 = Dg t (n + t): reassemble the peeled diagonal on level `n + t`.
  have hS1 : (∑ k ∈ range (n + t + 1), Nat.choose (n + t - t * (k + 1)) (k + 1)) + 1
      = Dg t (n + t) := by
    have peel : (∑ k ∈ range (n + t + 2), Nat.choose (n + t - t * k) k)
        = (∑ k ∈ range (n + t + 1), Nat.choose (n + t - t * (k + 1)) (k + 1)) + 1 := by
      rw [Finset.sum_range_succ' (fun k => Nat.choose (n + t - t * k) k) (n + t + 1)]
      simp
    have shrink : (∑ k ∈ range (n + t + 2), Nat.choose (n + t - t * k) k) = Dg t (n + t) := by
      unfold Dg
      rw [Finset.sum_range_succ]
      rw [Nat.choose_eq_zero_of_lt (show n + t - t * (n + t + 1) < n + t + 1 by omega),
          Nat.add_zero]
    rw [← peel]; exact shrink
  -- Second sum = Dg t n: the extra tail terms `k > n` vanish.
  have hS2 : (∑ k ∈ range (n + t + 1), Nat.choose (n - t * k) k) = Dg t n := by
    unfold Dg
    have hsub : range (n + 1) ⊆ range (n + t + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    have hvanish : ∀ k ∈ range (n + t + 1), k ∉ range (n + 1) →
        Nat.choose (n - t * k) k = 0 := by
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      apply Nat.choose_eq_zero_of_lt
      omega
    exact (Finset.sum_subset hsub hvanish).symm
  omega

/-! ### Stride `1`: the row sums `2ⁿ` (degenerate lag-`1` recurrence) -/

/-- Stride `1` (`t = 0`) recovers the binomial row sums `∑ₖ C(n, k) = 2ⁿ`. -/
theorem Dg_zero (n : ℕ) : Dg 0 n = 2 ^ n := by
  unfold Dg
  simp only [Nat.zero_mul, Nat.sub_zero]
  exact Nat.sum_range_choose n

/-- The stride-`1` recurrence is the doubling `2^{m+1} = 2·2^m`. -/
theorem Dg_zero_recurrence (n : ℕ) : Dg 0 (n + 1) = Dg 0 n + Dg 0 n := by
  have h := Dg_recurrence 0 n
  simpa using h

/-! ### Stride `2`: the Fibonacci diagonals -/

/-- **Parent identity (`combinations-formula-oq-08`)**, reproved inline so this file stands
    alone: the stride-`2` shallow-diagonal sum is a Fibonacci number.  Reindexes Mathlib's
    antidiagonal form `Nat.fib_succ_eq_sum_choose` via the reflection `k ↦ n - k`. -/
theorem fib_eq_sum_range_choose (n : ℕ) :
    Nat.fib (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose (n - k) k := by
  rw [Nat.fib_succ_eq_sum_choose,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose i j) n,
      ← Finset.sum_range_reflect (fun k => Nat.choose (n - k) k) (n + 1)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk]

/-- Stride `2` (`t = 1`) recovers the Fibonacci shallow diagonals `Dg 1 n = fib (n + 1)`. -/
theorem Dg_one (n : ℕ) : Dg 1 n = Nat.fib (n + 1) := by
  unfold Dg
  simp only [Nat.one_mul]
  exact (fib_eq_sum_range_choose n).symm

/-- The stride-`2` recurrence is the Fibonacci recurrence `F_{n+3} = F_{n+2} + F_{n+1}`,
    obtained here entirely from Pascal's rule on the stride diagonals. -/
theorem fib_recurrence_via_stride (n : ℕ) :
    Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1) := by
  have h := Dg_recurrence 1 n
  rw [Dg_one, Dg_one, Dg_one] at h
  -- `n + 1 + 1 = n + 2`, `n + 1 = n + 1`; the arguments align after normalization.
  simpa [Nat.add_assoc] using h

/-! ### Stride `3`: Narayana's cows (lag-`2` recurrence `a(m) = a(m-1) + a(m-3)`) -/

/-- Stride `3` (`t = 2`) satisfies the lag-`2` recurrence `a(m) = a(m-1) + a(m-3)`
    (Narayana's cows sequence), a genuinely higher-order recurrence with no `n-2` term. -/
theorem Dg_two_recurrence (n : ℕ) : Dg 2 (n + 3) = Dg 2 (n + 2) + Dg 2 n := by
  have h := Dg_recurrence 2 n
  simpa [Nat.add_assoc] using h

/-! ### Sanity checks -/

/-- `Dg 1 6 = fib 7 = 13`, from `C(6,0)+C(5,1)+C(4,2)+C(3,3) = 1+5+6+1 = 13`. -/
example : Dg 1 6 = 13 := by decide

/-- `Dg 0 4 = 2^4 = 16`, the fourth row sum of Pascal's triangle. -/
example : Dg 0 4 = 16 := by decide

/-- Stride `3` gives Narayana's cows `1,1,1,2,3,4,6,9,13,…`: `Dg 2 7 = 9` and the lagged
    recurrence `Dg 2 8 = Dg 2 7 + Dg 2 5`, i.e. `13 = 9 + 4`. -/
example : Dg 2 7 = 9 := by decide
example : Dg 2 8 = Dg 2 7 + Dg 2 5 := by decide

end CombinationsFormulaOQ08OQ02
