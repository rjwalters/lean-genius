/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-01:
# Worpitzky's row sum and explicit closed forms for the low columns of the Eulerian triangle

The parent entry `geometric-series-oq-07-oq-01-oq-01-oq-01` builds the combinatorial
**Eulerian numbers** `⟨n,k⟩` from the triangle recurrence
`⟨n+1,k+1⟩ = (k+2)·⟨n,k+1⟩ + (n−k)·⟨n,k⟩`, `⟨n,0⟩ = 1`, and identifies them with the
coefficients of the Eulerian polynomial.  It leaves open (`oq-01`) the **row-sum (Worpitzky)
identity** `∑ⱼ ⟨n,j⟩ = n!`.  This entry settles that and, alongside it, supplies the famous
**explicit closed forms** for the low columns — the first nontrivial cases of the general
inclusion–exclusion formula `⟨n,k⟩ = ∑_{i=0}^{k} (−1)ⁱ·C(n+1,i)·(k+1−i)ⁿ`:

* `eulerian_row_sum`   : `∑_{j} ⟨n,j⟩ = n!`       — the descent statistic is exhaustive;
* `eulerian_col_zero`  : `⟨n,0⟩ = 1`              — the left border;
* `eulerian_top`       : `⟨n+1,n⟩ = 1`            — the right border (largest index with a descent);
* `eulerian_col_one`   : `⟨n,1⟩ = 2ⁿ − n − 1`     — the second column (OEIS A000295, the Eulerian
                                                    numbers `2ⁿ − n − 1`);
* `eulerian_col_two`   : `2·⟨n,2⟩ = 2·3ⁿ − (n+1)·2ⁿ⁺¹ + n·(n+1)`
                                                  — the third column (`⟨n,2⟩ = 3ⁿ − (n+1)·2ⁿ + C(n+1,2)`,
                                                    OEIS A000460), stated cleared of its `/2` so the
                                                    statement stays over `ℤ` with no division.

For example `⟨3,1⟩ = 2³ − 3 − 1 = 4` and `2·⟨3,2⟩ = 2·27 − 4·16 + 12 = 2`, matching the third row
`1, 4, 1`; `⟨4,1⟩ = 16 − 5 = 11` and `2·⟨4,2⟩ = 2·81 − 5·32 + 20 = 22`, matching `1, 11, 11, 1`.

## Method

Each closed form is an induction on `n` driven by the single-step Eulerian recurrence
(`eulerian_succ_succ`).  The column `k = 0` is definitional.  `eulerian_top` uses the parent's
diagonal-vanishing `eulerian_succ_self` (`⟨n+1,n+1⟩ = 0`) to kill the leading term, leaving the
identity unchanged down the right edge.  `eulerian_col_one` recurs by `⟨n+1,1⟩ = 2·⟨n,1⟩ + n`, and
`eulerian_col_two` by `⟨n+1,2⟩ = 3·⟨n,2⟩ + (n−1)·⟨n,1⟩`, feeding in the previous column.  The only
care needed is the truncated subtraction `(n − 1 : ℕ)`: at `n = 0` it collapses to `0`, but there
`⟨0,1⟩ = 0` as well, so the contribution vanishes either way and the integer identity goes through.

The full inclusion–exclusion formula for *every* column reduces (see this session's notes) to the
pure binomial recurrence `W(n+1,k+1) = (k+2)·W n (k+1) + (n−k)·W n k` for
`W n k = ∑_{i=0}^{k} (−1)ⁱ·C(n+1,i)·(k+1−i)ⁿ`; that step is left as a follow-up.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ01

open Nat Finset Polynomial GeometricSeriesOQ07OQ01OQ01 GeometricSeriesOQ07OQ01OQ01OQ01

/-! ## Worpitzky's row identity: `∑ⱼ ⟨n,j⟩ = n!` -/

/-- The Eulerian numbers `⟨m+1,j⟩` for `j = 0,…,m` sum to `(m+1)!`.  Proved by evaluating the
parent's coefficient identity `eulerPoly_eq_eulerianNumbers` (`E_{m+1}(X) = ∑ⱼ ⟨m+1,j⟩·X^{j+1}`)
at `X = 1` and using the parent's row sum `eval_eulerPoly_one` (`Eₘ(1) = m!`). -/
private theorem eulerian_row_sum_succ (m : ℕ) :
    ∑ j ∈ range (m + 1), eulerian (m + 1) j = (m + 1)! := by
  have h := congrArg (Polynomial.eval (1 : ℤ)) (eulerPoly_eq_eulerianNumbers (R := ℤ) m)
  rw [eval_eulerPoly_one] at h
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one] at h
  exact_mod_cast h.symm

/-- **Worpitzky's row identity**: the Eulerian numbers in row `n` sum to `n!`.  Every permutation
of `{1,…,n}` has between `0` and `n−1` descents, so the descent statistic partitions the `n!`
permutations across the row.  (The parent obtains `Eₘ(1) = m!` analytically; here it is read off the
combinatorial triangle.) -/
theorem eulerian_row_sum (n : ℕ) : ∑ j ∈ range (n + 1), eulerian n j = n ! := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [sum_range_succ, eulerian_succ_self, add_zero]
    exact eulerian_row_sum_succ m

/-! ## The borders of the triangle -/

/-- The **left border**: `⟨n,0⟩ = 1`. -/
theorem eulerian_col_zero (n : ℕ) : eulerian n 0 = 1 := by
  cases n <;> rfl

/-- The **right border**: `⟨n+1,n⟩ = 1`.  This is the largest column with a nonzero Eulerian
number in row `n+1` (a permutation of `{1,…,n+1}` has at most `n` descents). -/
theorem eulerian_top (n : ℕ) : eulerian (n + 1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [eulerian_succ_succ, eulerian_succ_self, ih]
    omega

/-! ## The second column: `⟨n,1⟩ = 2ⁿ − n − 1` -/

/-- The **second column** of the Eulerian triangle is `2ⁿ − n − 1` (OEIS A000295). -/
theorem eulerian_col_one (n : ℕ) : (eulerian n 1 : ℤ) = 2 ^ n - n - 1 := by
  induction n with
  | zero => norm_num [eulerian]
  | succ n ih =>
    have hrec : eulerian (n + 1) 1 = 2 * eulerian n 1 + n := by
      rw [show eulerian (n + 1) 1 = 2 * eulerian n 1 + n * eulerian n 0 from rfl,
        show eulerian n 0 = 1 from eulerian_col_zero n, mul_one]
    have hcast : (eulerian (n + 1) 1 : ℤ) = 2 * (eulerian n 1 : ℤ) + n := by
      rw [hrec]; push_cast; ring
    rw [hcast, ih]; push_cast [pow_succ]; ring

/-! ## The third column: `⟨n,2⟩ = 3ⁿ − (n+1)·2ⁿ + C(n+1,2)` -/

/-- The **third column** of the Eulerian triangle, stated as `2·⟨n,2⟩` to clear the `/2` in
`C(n+1,2)`: `2·⟨n,2⟩ = 2·3ⁿ − (n+1)·2ⁿ⁺¹ + n·(n+1)` (so `⟨n,2⟩ = 3ⁿ − (n+1)·2ⁿ + C(n+1,2)`,
OEIS A000460). -/
theorem eulerian_col_two (n : ℕ) :
    2 * (eulerian n 2 : ℤ) = 2 * 3 ^ n - (n + 1) * 2 ^ (n + 1) + n * (n + 1) := by
  induction n with
  | zero => norm_num [eulerian]
  | succ n ih =>
    -- Eulerian recurrence for column 2: `⟨n+1,2⟩ = 3·⟨n,2⟩ + (n−1)·⟨n,1⟩`.
    have hrec : (2 * (eulerian (n + 1) 2 : ℤ))
        = 3 * (2 * (eulerian n 2 : ℤ)) + 2 * ((n - 1 : ℕ) : ℤ) * (eulerian n 1 : ℤ) := by
      rw [show eulerian (n + 1) 2 = 3 * eulerian n 2 + (n - 1) * eulerian n 1 from rfl]
      push_cast; ring
    -- Reconcile the truncated `(n − 1 : ℕ)` with `(n − 1 : ℤ)`: harmless because `⟨0,1⟩ = 0`.
    have key : 2 * ((n - 1 : ℕ) : ℤ) * (eulerian n 1 : ℤ)
        = 2 * ((n : ℤ) - 1) * (2 ^ n - n - 1) := by
      rw [eulerian_col_one n]
      rcases n with _ | m
      · norm_num
      · push_cast [Nat.succ_sub_one]; ring
    rw [hrec, ih, key]; push_cast [pow_succ]; ring

end GeometricSeriesOQ07OQ01OQ01OQ01OQ01
