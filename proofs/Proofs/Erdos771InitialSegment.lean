/-
# Erdős Problem #771 — the initial-segment construction and the exact avoiding size at the total

Research: erdos-771

The companion `Erdos771Problem.lean` pins down `maxAvoidingSize n m` (the largest size of an
`m`-avoiding subset of `{1,…,n}`) in two regimes:

* the **small-target** regime `1 ≤ m ≤ n`, where `maxAvoidingSize n m = n - ⌈m/2⌉`
  (`maxAvoidingSize_eq_sub_ceil_half`), proved from a *pairing* obstruction; and
* the **large-target** plateau, where `maxAvoidingSize n m = n` exactly when `m = 0` or
  `m` exceeds the total `∑_{a=1}^n a = n(n+1)/2` (`maxAvoidingSize_eq_n_iff`).

The pairing formula `n - ⌈m/2⌉` genuinely *fails* once `m > n` (e.g. `maxAvoidingSize 3 5 = 2`,
not `3 - ⌈5/2⌉ = 0`), so the intermediate band `n < m ≤ n(n+1)/2` needs a different tool.  This
file supplies the **low-element (initial-segment) construction**, which is the right lower-bound
witness there and — unlike the "prime multiples" and "large elements `> m`" constructions already
in the family — controls the *whole* subset-sum set by its total:

> The initial segment `{1,…,j}` has every subset sum `≤ 1+⋯+j = j(j+1)/2`.  So if `j(j+1)/2 < m`
> then `{1,…,j}` avoids `m` outright.

Results (all `0` sorries, `0` axioms):

* `avoid_of_sum_lt` — any set whose *total* is below `m` avoids `m` (every subset sum is `≤` the total).
* `initial_segment_avoid` / `maxAvoidingSize_ge_initial` — the initial-segment lower bound,
  valid for **all** `m`: if `j ≤ n` and `∑_{a=1}^j a < m` then `j ≤ maxAvoidingSize n m`.
* `maxAvoidingSize_ge_of_triangle_lt` — its closed (triangular) form: `j·(j+1) < 2m` suffices.
* `sum_Icc_n` — the Gauss total `∑_{a=1}^n a = n(n+1)/2` in `Nat` division form.
* `maxAvoidingSize_sum` / `maxAvoidingSize_triangular` — **the exact boundary value**:
  `maxAvoidingSize n (n(n+1)/2) = n - 1` for `n ≥ 1`.  This is the last value before the full-box
  plateau of `maxAvoidingSize_eq_n_iff`: at `m` one above the total the answer is `n`; at `m`
  exactly the total it drops to `n - 1` (drop the top element `n` — the remaining `{1,…,n-1}` totals
  `n(n+1)/2 − n < m`).

Everything reduces to the verified lemmas of `Erdos771Problem.lean`
(`maxAvoidingSize_ge_iff`, `maxAvoidingSize_eq_n_iff`, `two_mul_sum_Icc_n`), so the file is
`propext`/`Classical.choice`/`Quot.sound`-only.
-/
import Mathlib
import Proofs.Erdos771Problem

open Finset

namespace Erdos771

/-! ### Sets bounded by their total avoid `m` -/

/-- **A set whose total is below `m` avoids `m`.**  Every positive subset sum equals `∑ A`
for some `A ⊆ S`, and `∑ A ≤ ∑ S < m`, so `m` is never a subset sum.  This controls the
*entire* subset-sum set through a single inequality on the total — the mechanism behind the
initial-segment construction, complementing `avoid_of_forall_lt` (which instead bounds each
element from below). -/
theorem avoid_of_sum_lt {S : Finset ℕ} {m : ℕ} (h : (∑ a ∈ S, a) < m) :
    AvoidSum S m := by
  intro hmem
  rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
  obtain ⟨⟨A, hA, hAsum⟩, _hpos⟩ := hmem
  rw [Finset.mem_powerset] at hA
  have hle : (∑ a ∈ A, a) ≤ ∑ a ∈ S, a := Finset.sum_le_sum_of_subset hA
  rw [hAsum] at hle
  omega

/-! ### The initial-segment (low-element) construction -/

/-- **The initial segment `{1,…,j}` avoids `m` when its total is below `m`.**  Immediate from
`avoid_of_sum_lt`, recorded because `{1,…,j}` is the extremal low-element construction. -/
theorem initial_segment_avoid (j m : ℕ) (h : (∑ a ∈ Icc_n j, a) < m) :
    AvoidSum (Icc_n j) m :=
  avoid_of_sum_lt h

/-- **The initial-segment lower bound**, valid for every target `m`.  If `j ≤ n` and the total
`∑_{a=1}^j a` is below `m`, then `{1,…,j}` is an `m`-avoiding subset of `{1,…,n}` of size `j`, so
`j ≤ maxAvoidingSize n m`.  Unlike the pairing formula `n - ⌈m/2⌉` (which needs `m ≤ n`) this
lower bound applies across the whole intermediate band `n < m ≤ n(n+1)/2`. -/
theorem maxAvoidingSize_ge_initial (n m j : ℕ) (hj : j ≤ n)
    (h : (∑ a ∈ Icc_n j, a) < m) : j ≤ maxAvoidingSize n m := by
  refine (maxAvoidingSize_ge_iff n m j).mp
    ⟨Icc_n j, ?_, ?_, initial_segment_avoid j m h⟩
  · unfold Icc_n; exact Finset.Icc_subset_Icc (le_refl 1) hj
  · rw [Icc_n, Nat.card_Icc]; omega

/-- **Closed (triangular) form of the initial-segment lower bound.**  Since `2·∑_{a=1}^j a =
j(j+1)`, the hypothesis `∑_{a=1}^j a < m` is exactly `j·(j+1) < 2m`.  So whenever `j ≤ n` and
`j(j+1) < 2m`, we get `j ≤ maxAvoidingSize n m`. -/
theorem maxAvoidingSize_ge_of_triangle_lt (n m j : ℕ) (hj : j ≤ n)
    (h : j * (j + 1) < 2 * m) : j ≤ maxAvoidingSize n m := by
  apply maxAvoidingSize_ge_initial n m j hj
  have h2 := two_mul_sum_Icc_n j
  omega

/-! ### The Gauss total and the exact avoiding size at the boundary -/

/-- **The Gauss total** `∑_{a=1}^n a = n(n+1)/2`, in `Nat`-division form, from the doubled
identity `two_mul_sum_Icc_n`. -/
theorem sum_Icc_n (n : ℕ) : (∑ a ∈ Icc_n n, a) = n * (n + 1) / 2 := by
  have := two_mul_sum_Icc_n n
  omega

/-- **The exact avoiding size at the total sum.**  For `n ≥ 1`,
`maxAvoidingSize n (∑_{a=1}^n a) = n - 1`.  This is the last value before the full-box plateau:
`maxAvoidingSize_eq_n_iff` gives `= n` precisely for `m` strictly above the total, so at `m`
equal to the total the answer must be `< n`; and the initial segment `{1,…,n-1}` (total
`∑_{a=1}^n a − n <` the total) witnesses `≥ n-1`.  Hence exactly `n - 1`. -/
theorem maxAvoidingSize_sum (n : ℕ) (hn : 1 ≤ n) :
    maxAvoidingSize n (∑ a ∈ Icc_n n, a) = n - 1 := by
  have hins : Icc_n n = insert n (Icc_n (n - 1)) := by
    unfold Icc_n; ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hnm : n ∉ Icc_n (n - 1) := by
    unfold Icc_n; simp only [Finset.mem_Icc]; omega
  have hsum : (∑ a ∈ Icc_n n, a) = n + ∑ a ∈ Icc_n (n - 1), a := by
    rw [hins, Finset.sum_insert hnm]
  have hne : maxAvoidingSize n (∑ a ∈ Icc_n n, a) ≠ n := by
    rw [ne_eq, maxAvoidingSize_eq_n_iff]; push_neg
    exact ⟨by omega, by omega⟩
  have hle := maxAvoidingSize_le n (∑ a ∈ Icc_n n, a)
  have hge : n - 1 ≤ maxAvoidingSize n (∑ a ∈ Icc_n n, a) :=
    maxAvoidingSize_ge_initial n (∑ a ∈ Icc_n n, a) (n - 1) (by omega) (by omega)
  omega

/-- **Closed-form boundary value.**  `maxAvoidingSize n (n(n+1)/2) = n - 1` for `n ≥ 1` — the
`sum_Icc_n` rewrite of `maxAvoidingSize_sum`. -/
theorem maxAvoidingSize_triangular (n : ℕ) (hn : 1 ≤ n) :
    maxAvoidingSize n (n * (n + 1) / 2) = n - 1 := by
  rw [← sum_Icc_n]
  exact maxAvoidingSize_sum n hn

end Erdos771
