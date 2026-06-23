import Mathlib
import Proofs.CombinationsFormulaOQ07

/-
# The Weighted Sum of Squares of Binomial Coefficients

## Open Question OQ-07-OQ-03

The central identity of OQ-07 sums the *squares* of a Pascal row:

  C(2n, n) = ∑_{k=0}^{n} C(n, k)² .

This file weights that sum by `k`.  The result is the elegant closed form

  2 · ∑_{k=0}^{n} k · C(n, k)² = n · C(2n, n),                     (★)

equivalently, for `n ≥ 1`,

  ∑_{k=0}^{n} k · C(n, k)² = n · C(2n − 1, n − 1).

Mathlib provides the unweighted row sum (`Nat.sum_range_choose`), the
alternating row sum (`Nat.alternating_sum_range_choose`), and Vandermonde's
convolution (`Nat.add_choose_eq`), but **not** this first-moment identity.

## The reflection proof

The proof of (★) needs no induction, no generating functions, and no
factorial bookkeeping — only the reflection symmetry `k ↦ n − k`.  Writing
`S = ∑_{k} k · C(n, k)²`, the substitution `k ↦ n − k` together with the
symmetry `C(n, n − k) = C(n, k)` gives

  S = ∑_{k} (n − k) · C(n, k)² .

Adding the two expressions for `S` collapses the weight to a constant:

  2S = ∑_{k} (k + (n − k)) · C(n, k)² = n · ∑_{k} C(n, k)² = n · C(2n, n),

the last step being exactly the parent identity `central_binom_eq_sum_sq`.

## Mathematical Context

Reading `C(n, k)² / C(2n, n)` as a probability distribution on `{0, …, n}`
(the hypergeometric distribution arising from the Vandermonde split of a
`2n`-set into two halves), identity (★) says its **mean is `n / 2`** — the
distribution is symmetric about its centre.  The same reflection argument that
proves (★) is the combinatorial reason for that symmetry.

## Results

1. `sum_weighted_sq_reflect` — the reflection symmetry
   `∑ k · C(n, k)² = ∑ (n − k) · C(n, k)²`, the conceptual core.
2. `two_mul_sum_weighted_sq` — the closed form `2 · ∑ k · C(n,k)² = n · C(2n, n)`.
3. `central_binom_two_mul_pred` — the halving `C(2n, n) = 2 · C(2n−1, n−1)`
   (for `n ≥ 1`), the bridge to the classical statement.
4. `sum_weighted_sq` — the classical form `∑ k · C(n,k)² = n · C(2n−1, n−1)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ03

open Finset

/-- **Reflection symmetry.** Substituting `k ↦ n − k` and using
    `C(n, n − k) = C(n, k)` shows the `k`-weighted and `(n−k)`-weighted sums of
    squares agree. This is the heart of the closed form below. -/
theorem sum_weighted_sq_reflect (n : ℕ) :
    ∑ k ∈ range (n + 1), k * (n.choose k) ^ 2
      = ∑ k ∈ range (n + 1), (n - k) * (n.choose k) ^ 2 := by
  rw [← Finset.sum_range_reflect (fun k => (n - k) * (n.choose k) ^ 2) (n + 1)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  have h1 : n + 1 - 1 - i = n - i := by omega
  rw [h1, Nat.choose_symm hi]
  congr 1
  omega

/-- **Weighted central binomial sum of squares.**
    `2 · ∑_{k=0}^{n} k · C(n, k)² = n · C(2n, n)`.
    The factor of `2` packages the reflection symmetry and keeps the statement
    free of natural-number subtraction. -/
theorem two_mul_sum_weighted_sq (n : ℕ) :
    2 * ∑ k ∈ range (n + 1), k * (n.choose k) ^ 2 = n * (2 * n).choose n := by
  have key : ∀ k ∈ range (n + 1),
      k * (n.choose k) ^ 2 + (n - k) * (n.choose k) ^ 2 = n * (n.choose k) ^ 2 := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [← Nat.add_mul]
    congr 1
    omega
  calc 2 * ∑ k ∈ range (n + 1), k * (n.choose k) ^ 2
      = (∑ k ∈ range (n + 1), k * (n.choose k) ^ 2)
          + ∑ k ∈ range (n + 1), k * (n.choose k) ^ 2 := by rw [two_mul]
    _ = (∑ k ∈ range (n + 1), k * (n.choose k) ^ 2)
          + ∑ k ∈ range (n + 1), (n - k) * (n.choose k) ^ 2 := by
          rw [← sum_weighted_sq_reflect]
    _ = ∑ k ∈ range (n + 1),
          (k * (n.choose k) ^ 2 + (n - k) * (n.choose k) ^ 2) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ k ∈ range (n + 1), n * (n.choose k) ^ 2 := Finset.sum_congr rfl key
    _ = n * ∑ k ∈ range (n + 1), (n.choose k) ^ 2 := by rw [Finset.mul_sum]
    _ = n * (2 * n).choose n := by
          rw [← CombinationsFormulaOQ07.central_binom_eq_sum_sq]

/-- **Halving the central binomial coefficient.** For `n ≥ 1`,
    `C(2n, n) = 2 · C(2n − 1, n − 1)`, since Pascal's rule splits `C(2n, n)`
    into two symmetric halves `C(2n−1, n−1) = C(2n−1, n)`. -/
theorem central_binom_two_mul_pred (n : ℕ) (hn : 1 ≤ n) :
    (2 * n).choose n = 2 * (2 * n - 1).choose (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e3 : m + 1 - 1 = m := by omega
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    have h := Nat.choose_symm (show m ≤ 2 * m + 1 by omega)
    rwa [show 2 * m + 1 - m = m + 1 by omega] at h
  rw [e2, e3, e1, Nat.choose_succ_succ, hsymm]
  ring

/-- **Weighted sum of squares (classical form).** For `n ≥ 1`,
    `∑_{k=0}^{n} k · C(n, k)² = n · C(2n − 1, n − 1)`. -/
theorem sum_weighted_sq (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), k * (n.choose k) ^ 2 = n * (2 * n - 1).choose (n - 1) := by
  have h2 := two_mul_sum_weighted_sq n
  rw [central_binom_two_mul_pred n hn] at h2
  have h3 : 2 * (∑ k ∈ range (n + 1), k * (n.choose k) ^ 2)
      = 2 * (n * (2 * n - 1).choose (n - 1)) := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3

/-- Sanity check: `∑_{k=0}^{3} k·C(3,k)² = 0 + 9 + 18 + 3 = 30 = 3·C(5,2) = 3·10`. -/
example : ∑ k ∈ range 4, k * ((3 : ℕ).choose k) ^ 2 = 30 := by decide

/-- Sanity check of the closed form at `n = 3`: `30 = 3 · C(5, 2)`. -/
example : ∑ k ∈ range 4, k * ((3 : ℕ).choose k) ^ 2 = 3 * (2 * 3 - 1).choose (3 - 1) := by
  decide

end CombinationsFormulaOQ07OQ03
