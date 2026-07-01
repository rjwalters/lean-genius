import Mathlib

/-
# Stride-`s` Shallow Diagonals: a Uniform `s`-bonacci Recurrence (OQ-08-OQ-02)

Parent entry `combinations-formula-oq-08` proves that the Fibonacci numbers are the
sums along the *shallow* diagonals of Pascal's triangle (stepping one row up and one
column right), and the sibling follow-up `combinations-formula-oq-08-oq-01` derives the
Fibonacci recurrence directly from those diagonals by Pascal's rule.

Both entries left the same open question:

  *Does the analogous shallow-diagonal sum with a fixed stride `s` (stepping `s` columns
  per row) satisfy a higher-order recurrence, and can the same peeling-then-Pascal method
  formalize it uniformly in `s`?*

This entry answers it.  Fix a stride parameter `t = s - 1 ≥ 0` and define the `t`-strided
diagonal total

  `D t n := ∑ k ∈ range (n + 1), C(n - t·k, k)`.

The centerpiece is the **uniform strided recurrence**

  `D_recurrence : D t (n + t + 1) = D t (n + t) + D t n`,

proved for *every* stride `t` by a single term-by-term Pascal expansion and reindexing of
finite sums — no generating functions, no case split on `t`.  Specializing `t` recovers a
whole family of classical sequences from one theorem:

  * `t = 0`:  `D 0 n = 2 ^ n`         and  `2 ^ (n+1) = 2 ^ n + 2 ^ n`      (`two_pow_recurrence`)
  * `t = 1`:  `D 1 n = fib (n + 1)`   and  `fib (n+3) = fib (n+2) + fib (n+1)` (`fib_recurrence_via_diagonal`)
  * `t = 2`:  `D 2 n` is the Padovan sequence `1,1,1,2,3,4,6,9,…`, obeying `D 2 (n+3) = D 2 (n+2) + D 2 n`.

## Proof of the recurrence (sketch)

Peeling the `k = 0` term of `D t (n+t+1)` and of `D t (n+t)` with `Finset.sum_range_succ'`
(each contributes the constant `C(·, 0) = 1`) reduces the goal, after cancelling the `+1`,
to a single sum identity.  The driving arithmetic fact is the **unconditional** Pascal
split of one strided diagonal term

  `pascal_stride : C(n+1 - t·k, k+1) = C(n - t·k, k) + C(n - t·k, k+1)`,

valid for all `k` (when `t·k > n` both sides collapse to `0` in `ℕ`).  Summing it over
`range (n+t+1)` and splitting with `Finset.sum_add_distrib` yields two sums: the first,
`∑ C(n - t·k, k)`, is `D t n` once the vanishing tail terms `C(n - t·k, k) = 0`
(for `k > n`) are dropped via `Finset.sum_subset`; the second, `∑ C(n - t·k, k+1)`,
is the peeled body of `D t (n+t)` once its single vanishing top term is dropped via
`Finset.sum_range_succ`.  Matching the two sides gives the recurrence.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ08OQ02

open Finset

/-- `D t n` is the total of the shallow diagonal of Pascal's triangle taken with stride
    `t` (i.e. stepping `t` columns per row):
    `D t n = C(n, 0) + C(n - t, 1) + C(n - 2t, 2) + ⋯`.
    `t = 0` gives `∑ C(n,k) = 2^n`; `t = 1` gives the Fibonacci diagonal `∑ C(n-k,k)`. -/
def D (t n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.choose (n - t * k) k

/-- **Unconditional strided Pascal split.**
    Each strided diagonal entry on level `n + 1` splits into the two entries below it on
    level `n`.  When `t * k > n` the upper index truncates to `0` and both sides vanish, so
    the identity needs no side condition — the single arithmetic fact driving the whole
    recurrence. -/
theorem pascal_stride (t n k : ℕ) :
    Nat.choose (n + 1 - t * k) (k + 1)
      = Nat.choose (n - t * k) k + Nat.choose (n - t * k) (k + 1) := by
  rcases le_or_gt (t * k) n with h | h
  · have h1 : n + 1 - t * k = (n - t * k) + 1 := by omega
    rw [h1, Nat.choose_succ_succ]
  · have h1 : n + 1 - t * k = 0 := by omega
    have h2 : n - t * k = 0 := by omega
    have hk : k ≠ 0 := by rintro rfl; simp at h
    rw [h1, h2, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk),
        Nat.choose_eq_zero_of_lt (show 0 < k + 1 by omega)]

/-- After peeling the `k = 0` term, the diagonal total `D t (n + t + 1)` is a single sum
    over `range (n + t + 1)` plus the constant `1`.  The upper index simplifies as
    `n + t + 1 - t·(k+1) = n + 1 - t·k`. -/
theorem D_peel_top (t n : ℕ) :
    D t (n + t + 1) = (∑ k ∈ range (n + t + 1), Nat.choose (n + 1 - t * k) (k + 1)) + 1 := by
  unfold D
  rw [Finset.sum_range_succ' (fun k => Nat.choose (n + t + 1 - t * k) k) (n + t + 1)]
  simp only [mul_zero, Nat.sub_zero, Nat.choose_zero_right]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hmul : t * (k + 1) = t * k + t := by ring
  congr 1
  omega

/-- After peeling the `k = 0` term, the diagonal total `D t (n + t)` is a single sum over
    `range (n + t)` plus the constant `1`.  The upper index simplifies as
    `n + t - t·(k+1) = n - t·k`. -/
theorem D_peel_mid (t n : ℕ) :
    D t (n + t) = (∑ k ∈ range (n + t), Nat.choose (n - t * k) (k + 1)) + 1 := by
  unfold D
  rw [Finset.sum_range_succ' (fun k => Nat.choose (n + t - t * k) k) (n + t)]
  simp only [mul_zero, Nat.sub_zero, Nat.choose_zero_right]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hmul : t * (k + 1) = t * k + t := by ring
  congr 1
  omega

/-- **The uniform strided recurrence — the combinatorial core.**
    For every stride `t`, the strided diagonal totals satisfy
    `D t (n + t + 1) = D t (n + t) + D t n`, derived purely by applying the strided Pascal
    rule to each diagonal term.  No case split on `t`, no appeal to any named recurrence. -/
theorem D_recurrence (t n : ℕ) : D t (n + t + 1) = D t (n + t) + D t n := by
  rw [D_peel_top, D_peel_mid]
  unfold D
  -- Drop the vanishing tail of `∑_{range(n+t+1)} C(n - t·k, k)` back to `range (n+1)`.
  have eqA : (∑ k ∈ range (n + t + 1), Nat.choose (n - t * k) k)
      = ∑ k ∈ range (n + 1), Nat.choose (n - t * k) k := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro k hk hk'
      rw [Finset.mem_range] at hk
      rw [Finset.mem_range, not_lt] at hk'
      exact Nat.choose_eq_zero_of_lt
        (lt_of_le_of_lt (Nat.sub_le n (t * k)) (by omega))
  -- Drop the single vanishing top term of `∑_{range(n+t+1)} C(n - t·k, k+1)`.
  have eqB : (∑ k ∈ range (n + t + 1), Nat.choose (n - t * k) (k + 1))
      = ∑ k ∈ range (n + t), Nat.choose (n - t * k) (k + 1) := by
    rw [Finset.sum_range_succ,
        Nat.choose_eq_zero_of_lt
          (lt_of_le_of_lt (Nat.sub_le n (t * (n + t))) (by omega : n < n + t + 1)),
        add_zero]
  -- Split the peeled top sum by strided Pascal and reassemble.
  have hsplit : ∀ k ∈ range (n + t + 1),
      Nat.choose (n + 1 - t * k) (k + 1)
        = Nat.choose (n - t * k) k + Nat.choose (n - t * k) (k + 1) :=
    fun k _ => pascal_stride t n k
  have key : (∑ k ∈ range (n + t + 1), Nat.choose (n + 1 - t * k) (k + 1))
      = (∑ k ∈ range (n + 1), Nat.choose (n - t * k) k)
        + ∑ k ∈ range (n + t), Nat.choose (n - t * k) (k + 1) :=
    calc (∑ k ∈ range (n + t + 1), Nat.choose (n + 1 - t * k) (k + 1))
        = ∑ k ∈ range (n + t + 1),
            (Nat.choose (n - t * k) k + Nat.choose (n - t * k) (k + 1)) :=
          Finset.sum_congr rfl hsplit
      _ = (∑ k ∈ range (n + t + 1), Nat.choose (n - t * k) k)
            + ∑ k ∈ range (n + t + 1), Nat.choose (n - t * k) (k + 1) :=
          Finset.sum_add_distrib
      _ = (∑ k ∈ range (n + 1), Nat.choose (n - t * k) k)
            + ∑ k ∈ range (n + t), Nat.choose (n - t * k) (k + 1) := by rw [eqA, eqB]
  rw [key]
  omega

/-! ### Specializations: one recurrence, three classical sequences -/

/-- **Stride `0` is the full binomial row.**  `D 0 n = ∑ C(n,k) = 2 ^ n`. -/
theorem D_zero_eq_two_pow (n : ℕ) : D 0 n = 2 ^ n := by
  unfold D
  simp only [zero_mul, Nat.sub_zero]
  exact Nat.sum_range_choose n

/-- **Stride `1` is the Fibonacci diagonal.**  `D 1 n = fib (n + 1)`, reproved inline by
    reindexing Mathlib's antidiagonal form so this file stands alone. -/
theorem D_one_eq_fib (n : ℕ) : D 1 n = Nat.fib (n + 1) := by
  unfold D
  simp only [one_mul]
  symm
  rw [Nat.fib_succ_eq_sum_choose,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose i j) n,
      ← Finset.sum_range_reflect (fun k => Nat.choose (n - k) k) (n + 1)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk]

/-- **Powers of two from the diagonal recurrence.**  Specializing `D_recurrence` at
    stride `0` and applying `D_zero_eq_two_pow` recovers `2^(n+1) = 2^n + 2^n`. -/
theorem two_pow_recurrence (n : ℕ) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
  have h := D_recurrence 0 n
  simp only [D_zero_eq_two_pow] at h
  simpa using h

/-- **The Fibonacci recurrence from the diagonal recurrence.**  Specializing `D_recurrence`
    at stride `1` and applying `D_one_eq_fib` recovers `fib (n+3) = fib (n+2) + fib (n+1)`,
    as a special case of the uniform strided recurrence. -/
theorem fib_recurrence_via_diagonal (n : ℕ) :
    Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1) := by
  have h := D_recurrence 1 n
  simp only [D_one_eq_fib] at h
  exact h

/-! ### Sanity checks -/

/-- Stride `0`: `D 0 5 = 2^5 = 32`. -/
example : D 0 5 = 32 := by decide

/-- Stride `1`: `D 1 6 = fib 7 = 13`. -/
example : D 1 6 = 13 := by decide

/-- Stride `2` gives the Padovan sequence `D 2 : 1,1,1,2,3,4,6,9,13,…`. -/
example : D 2 6 = 6 := by decide

/-- Stride `2` recurrence instance: `D 2 6 = D 2 5 + D 2 3`, i.e. `6 = 4 + 2`. -/
example : D 2 (3 + 2 + 1) = D 2 (3 + 2) + D 2 3 := by decide

end CombinationsFormulaOQ08OQ02
