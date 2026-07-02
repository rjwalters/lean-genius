import Mathlib

/-!
# The general factorial moment of a binomial row

## What This Proves

For a fixed row `n` of Pascal's triangle and any order `j`, the **`j`-th falling
factorial moment** of the binomial coefficients has the closed form

  **`∑_{k=0}^{n} (k)_j · C(n,k) = (n)_j · 2^{n-j}`,**

where `(m)_j = m·(m-1)···(m-j+1)` is the falling (descending) factorial
`Nat.descFactorial m j`.

This is the uniform, all-`j` generalisation of the parent entry
`combinations-formula-oq-09`, which established only the first two cases:

* `j = 1`: `∑ k·C(n,k) = n·2^{n-1}`   (first moment);
* `j = 2`: `∑ k(k-1)·C(n,k) = n(n-1)·2^{n-2}`   (second *factorial* moment).

The open question asked whether "the same peel-then-absorb pattern gives the
general factorial moment."  The answer is **yes**, and the cleanest route is not
iterated peeling but a single *subset-of-a-subset* reindexing.

## The mechanism

The falling factorial packages the absorption identity all at once.  Writing
`(m)_j = j!·C(m,j)` (`Nat.descFactorial_eq_factorial_mul_choose`), the summand
factors through the trinomial revision / subset-of-a-subset identity
`C(n,k)·C(k,j) = C(n,j)·C(n-j,k-j)` (`Nat.choose_mul`):

  `(k)_j · C(n,k) = (n)_j · C(n-j, k-j).`

The lower terms `k < j` vanish (a falling factorial with a zero factor), so after
shifting the index `k = j + i` the sum collapses to the plain row sum
`∑_i C(n-j, i) = 2^{n-j}` (`Nat.sum_range_choose`).  No Stirling numbers are
needed — that is the advantage of phrasing the moment in the *falling factorial*
basis rather than the ordinary power basis.

## Main results

* `descFactorial_choose_shift` — the pointwise reindexed identity
  `(j+i)_j · C(n, j+i) = (n)_j · C(n-j, i)`;
* `factorial_moment` — the headline, **unconditional in `j`**
  `∑_{k∈range(n+1)} (k)_j · C(n,k) = (n)_j · 2^{n-j}`;
* `sum_range_choose_mul_id` — `j = 1`, recovering the parent's first moment;
* `sum_range_choose_mul_pred_mul` — `j = 2`, the second factorial moment in the
  expanded form `∑ (k-1)·k·C(n,k) = (n-1)·n·2^{n-2}`.
-/

namespace CombinationsFormulaOQ09OQ01

open Finset Nat

/-! ## Pointwise reindexed identity -/

/-- **Subset-of-a-subset in falling-factorial form.**  After shifting the summation
index by `j`, the weighted binomial term factors cleanly:

  `(j+i)_j · C(n, j+i) = (n)_j · C(n-j, i).`

Proof: expand each falling factorial as `(m)_j = j!·C(m,j)`
(`Nat.descFactorial_eq_factorial_mul_choose`) and apply the trinomial-revision
identity `C(n, j+i)·C(j+i, j) = C(n,j)·C(n-j, i)` (`Nat.choose_mul`, using
`(j+i) - j = i`). -/
theorem descFactorial_choose_shift (n j i : ℕ) :
    (j + i).descFactorial j * n.choose (j + i)
      = n.descFactorial j * (n - j).choose i := by
  rw [Nat.descFactorial_eq_factorial_mul_choose (j + i) j,
      Nat.descFactorial_eq_factorial_mul_choose n j]
  have hmul := Nat.choose_mul (n := n) (k := j + i) (s := j) (Nat.le_add_right j i)
  rw [Nat.add_sub_cancel_left] at hmul
  calc j ! * (j + i).choose j * n.choose (j + i)
      = j ! * (n.choose (j + i) * (j + i).choose j) := by ring
    _ = j ! * (n.choose j * (n - j).choose i) := by rw [hmul]
    _ = j ! * n.choose j * (n - j).choose i := by ring

/-! ## The headline: the general factorial moment -/

/-- **The `j`-th falling factorial moment of a binomial row.**  For every `n` and
every order `j`,

  `∑_{k=0}^{n} (k)_j · C(n,k) = (n)_j · 2^{n-j}.`

The identity holds unconditionally: when `j > n` both sides are `0`
(every `(k)_j` with `k ≤ n < j` vanishes, and `(n)_j = 0`).

Proof (case `j ≤ n`): the head block `k < j` contributes nothing, so the sum
runs over `Ico j (n+1)`; shifting `k = j + i` (`Finset.sum_Ico_eq_sum_range`) and
applying `descFactorial_choose_shift` pulls the constant `(n)_j` out, leaving the
plain row sum `∑_i C(n-j, i) = 2^{n-j}` (`Nat.sum_range_choose`). -/
theorem factorial_moment (n j : ℕ) :
    ∑ k ∈ range (n + 1), k.descFactorial j * n.choose k
      = n.descFactorial j * 2 ^ (n - j) := by
  rcases le_or_gt j n with hjn | hjn
  · -- Head terms `k < j` vanish.
    have hhead : ∑ k ∈ Ico 0 j, k.descFactorial j * n.choose k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Nat.descFactorial_eq_zero_iff_lt.2 hk.2, Nat.zero_mul]
    have hcons := Finset.sum_Ico_consecutive
      (fun k => k.descFactorial j * n.choose k) (Nat.zero_le j) (by omega : j ≤ n + 1)
    rw [range_eq_Ico, ← hcons, hhead, Nat.zero_add, Finset.sum_Ico_eq_sum_range]
    have hrw : ∀ i ∈ range (n + 1 - j),
        (j + i).descFactorial j * n.choose (j + i)
          = n.descFactorial j * (n - j).choose i :=
      fun i _ => descFactorial_choose_shift n j i
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum,
        show n + 1 - j = (n - j) + 1 from by omega, Nat.sum_range_choose]
  · -- `j > n`: every term vanishes and `(n)_j = 0`.
    rw [Nat.descFactorial_eq_zero_iff_lt.2 hjn, Nat.zero_mul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : k < j), Nat.zero_mul]

/-! ## Corollaries: recovering the parent's first and second moments -/

/-- **First moment (`j = 1`), the parent identity.**  `∑ k·C(n,k) = n·2^{n-1}`,
recovered as the `j = 1` instance of `factorial_moment` via
`(m)_1 = m` (`Nat.descFactorial_one`). -/
theorem sum_range_choose_mul_id (n : ℕ) :
    ∑ k ∈ range (n + 1), k * n.choose k = n * 2 ^ (n - 1) := by
  simpa [Nat.descFactorial_one] using factorial_moment n 1

/-- The second falling factorial in expanded form: `(m)_2 = (m-1)·m`. -/
theorem descFactorial_two (m : ℕ) : m.descFactorial 2 = (m - 1) * m := by
  rw [Nat.descFactorial_succ, Nat.descFactorial_one]

/-- **Second factorial moment (`j = 2`).**  `∑ (k-1)·k·C(n,k) = (n-1)·n·2^{n-2}`,
the `j = 2` instance expanded through `descFactorial_two`.  Combined with the
first moment this recovers the parent's ordinary second moment
`∑ k²·C(n,k)` via `k² = (k-1)·k + k`. -/
theorem sum_range_choose_mul_pred_mul (n : ℕ) :
    ∑ k ∈ range (n + 1), (k - 1) * k * n.choose k = (n - 1) * n * 2 ^ (n - 2) := by
  simpa [descFactorial_two] using factorial_moment n 2

/-! ## Concrete instances (from the general theorem, not `native_decide`) -/

/-- Base case sanity (`j = 0`): the falling factorial is `1`, recovering the total
row sum `∑ C(n,k) = 2ⁿ`. -/
theorem factorial_moment_zero (n : ℕ) :
    ∑ k ∈ range (n + 1), k.descFactorial 0 * n.choose k = 2 ^ n := by
  simpa using factorial_moment n 0

/-- `∑_{k≤4} (k)_2 · C(4,k) = 0+0+12+24+12 = 48 = (4)_2 · 2² = 12·4`. -/
example : ∑ k ∈ range 5, k.descFactorial 2 * (4 : ℕ).choose k = 48 := by decide

/-- `∑_{k≤5} (k)_3 · C(5,k) = 60+120+60 = 240 = (5)_3 · 2² = 60·4` — a genuinely
higher-order instance the parent's first/second-moment results cannot reach. -/
example : ∑ k ∈ range 6, k.descFactorial 3 * (5 : ℕ).choose k = 240 := by decide

end CombinationsFormulaOQ09OQ01
