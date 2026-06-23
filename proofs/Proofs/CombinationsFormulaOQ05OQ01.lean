import Mathlib

/-
# Telescoping the Alternating Row Sum: the Partial Sums of Pascal's Triangle

## Open Question OQ-05-OQ-01

The parent file `CombinationsFormulaOQ05` proves the *full*-row cancellation
`∑_{k=0}^{n} (-1)^k C(n,k) = 0` (for `n ≥ 1`) and reads off the even/odd split.
That identity is the endpoint of a sharper, telescoping phenomenon: the
**partial** alternating sums collapse to a single binomial coefficient,

  ∑_{k=0}^{j} (-1)^k · C(n, k) = (-1)^j · C(n-1, j) .

This is the finite-difference / telescoping refinement requested by OQ-05-OQ-01.

1. `partial_alternating_sum_choose_succ` — the base form on `m+1`, proved by a
   one-line induction on `j` using Pascal's rule (`Nat.choose_succ_succ`).

2. `partial_alternating_sum_choose` — the headline identity, stated with `n-1`
   for `n ≥ 1`.

3. `alternating_sum_choose_eq_zero` — the parent's full-row cancellation
   recovered as the `j = n` instance: the partial sum lands on
   `(-1)^n · C(n-1, n) = 0`, because `n > n-1`.

4. `partial_alternating_sum_ne_zero` — the structural consequence: for every
   `j < n` the partial sum is **nonzero**. The alternating row sum therefore
   never cancels early — the single cancellation to `0` happens only when the
   last term `k = n` is included. This is exactly what distinguishes the
   telescoping identity from the bare endpoint statement.

## Mathematical Context

Writing `S_n(j) := ∑_{k≤j} (-1)^k C(n,k)`, Pascal's rule
`C(n,k) = C(n-1,k-1) + C(n-1,k)` makes the alternating sum telescope:
the `+C(n-1,k)` of one term cancels the `-C(n-1,k)` produced by the next, so
only the last surviving boundary term `(-1)^j C(n-1,j)` remains. Setting
`j = n` kills even that term, giving the classical vanishing. This is the
discrete analogue of `∫_0^x f' = f(x) - f(0)` for the forward-difference
operator on the row `k ↦ C(n,k)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ05OQ01

open Finset

/-- **Base form.** The partial alternating sum of row `m+1` of Pascal's triangle
    telescopes to a single binomial coefficient of row `m`:
        `∑_{k=0}^{j} (-1)^k C(m+1, k) = (-1)^j C(m, j)`.
    Proved by induction on `j` with Pascal's rule. -/
theorem partial_alternating_sum_choose_succ (m j : ℕ) :
    ∑ k ∈ Finset.range (j + 1), ((-1) ^ k * ((m + 1).choose k) : ℤ)
      = (-1) ^ j * (m.choose j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have hp : (((m + 1).choose (j + 1) : ℤ)) = m.choose j + m.choose (j + 1) := by
      exact_mod_cast Nat.choose_succ_succ m j
    rw [hp]
    ring

/-- **Telescoping partial alternating sum** (headline identity). For `n ≥ 1`,
        `∑_{k=0}^{j} (-1)^k C(n, k) = (-1)^j C(n-1, j)`. -/
theorem partial_alternating_sum_choose {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    ∑ k ∈ Finset.range (j + 1), ((-1) ^ k * (n.choose k) : ℤ)
      = (-1) ^ j * ((n - 1).choose j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa using partial_alternating_sum_choose_succ m j

/-- **Full-row cancellation recovered.** The parent's vanishing alternating row
    sum is the `j = n` instance of the telescoping identity: the partial sum
    reaches `(-1)^n · C(n-1, n) = 0` because `n > n-1`. -/
theorem alternating_sum_choose_eq_zero {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ Finset.range (n + 1), ((-1) ^ k * (n.choose k) : ℤ) = 0 := by
  rw [partial_alternating_sum_choose hn n, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- **No early cancellation.** For every `j < n` the partial alternating sum is
    nonzero (it equals `±C(n-1, j)` with `0 < C(n-1, j)`). The alternating row
    sum cancels to `0` only when the final term `k = n` is included. -/
theorem partial_alternating_sum_ne_zero {n : ℕ} (hn : n ≠ 0) {j : ℕ} (hj : j < n) :
    ∑ k ∈ Finset.range (j + 1), ((-1) ^ k * (n.choose k) : ℤ) ≠ 0 := by
  rw [partial_alternating_sum_choose hn j]
  apply mul_ne_zero
  · exact pow_ne_zero j (by norm_num)
  · have hpos : 0 < (n - 1).choose j := Nat.choose_pos (by omega)
    exact_mod_cast hpos.ne'

/-- Sanity check (row 4, `j = 2`): `1 - 4 + 6 = 3 = (-1)^2 · C(3,2) = 3`. -/
example :
    ∑ k ∈ Finset.range 3, ((-1) ^ k * (Nat.choose 4 k) : ℤ) = 3 := by
  decide

end CombinationsFormulaOQ05OQ01
