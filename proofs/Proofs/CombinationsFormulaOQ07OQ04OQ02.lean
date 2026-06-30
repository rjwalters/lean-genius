import Mathlib
import Proofs.CombinationsFormulaOQ07
import Proofs.CombinationsFormulaOQ07OQ03
import Proofs.CombinationsFormulaOQ07OQ04

/-
# The Variance of the Squared-Binomial (Vandermonde) Distribution

## Open Question OQ-07-OQ-04-OQ-02

Reading `C(n, k)² / C(2n, n)` as a probability distribution on `{0, …, n}` — the
law of the size of one half of a Vandermonde split of a `2n`-set into two `n`-sets —
the parent file (OQ-07-OQ-04) computed its raw first and second moments,

  ∑ k · C(n,k)²  = n · C(2n−1, n−1),        ∑ k² · C(n,k)²  = n² · C(2n−2, n−1),

and observed (but did not prove) that together they pin the **mean** at `n / 2` and the
**variance** at `n² / (4(2n − 1))`.  This file formalises that variance claim.

To stay inside the integers we record the variance in its *cleared, centred* form.
Writing the deviation as `2k − n` (twice the deviation `k − n/2` from the mean, so that
it is an integer), the centred second moment satisfies the single closed identity

  (2n − 1) · ∑_{k=0}^{n} (2k − n)² · C(n,k)²  =  n² · C(2n, n).                     (★)

Dividing by `4 · (2n−1) · C(2n, n)` turns the left-hand side into
`∑ (k − n/2)² · C(n,k)²/C(2n,n) = Var`, recovering `Var = n² / (4(2n − 1))` exactly.

## The proof

Expanding `(2k − n)² = 4k² − 4nk + n²` and summing term by term reduces (★) to the
three raw moments already in the gallery:

  ∑ (2k−n)²·C(n,k)² = 4·∑ k²C² − 4n·∑ kC² + n²·∑ C²
                    = 4·n²·C(2n−2,n−1) − 4n·n·C(2n−1,n−1) + n²·C(2n,n).

The remaining identity is pure binomial bookkeeping.  Two relations from the parent
files close it:

  * the **halving** `C(2n, n) = 2 · C(2n−1, n−1)`   (`central_binom_two_mul_pred`), and
  * the **recurrence** `n · C(2n, n) = 2(2n−1) · C(2n−2, n−1)`  (`central_binom_recurrence`).

With `a = C(2n−1, n−1)`, `b = C(2n−2, n−1)`, `c = C(2n, n)` these read `c = 2a` and
`n·c = 2(2n−1)·b`; substituting collapses the centred moment to `n²·c`, so (★) is a
single `linear_combination` of the two relations.

## Results

1. `centred_second_moment` — the cleared variance identity (★)
   `(2n − 1) · ∑ (2k − n)² · C(n,k)² = n² · C(2n, n)`.
2. `variance_eq` — the rational variance in lowest terms,
   `(∑ (k − n/2)² · C(n,k)²) / C(2n, n) = n² / (4(2n − 1))`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ02

open Finset

/-- **The cleared variance identity** `(★)`.  For `n ≥ 1`,

      (2n − 1) · ∑_{k=0}^{n} (2k − n)² · C(n,k)²  =  n² · C(2n, n).

    Expand `(2k−n)²` into the three raw moments (sum of squares, first and second
    weighted moments) already proved in this OQ family, then close with the halving
    and recurrence relations for the central binomial coefficient. -/
theorem centred_second_moment (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℤ) - 1) *
        ∑ k ∈ range (n + 1), (2 * (k : ℤ) - n) ^ 2 * ((n.choose k : ℤ)) ^ 2
      = (n : ℤ) ^ 2 * ((2 * n).choose n : ℤ) := by
  -- Expand the centred square term by term into the three raw moments.
  have hexpand :
      ∑ k ∈ range (n + 1), (2 * (k : ℤ) - n) ^ 2 * ((n.choose k : ℤ)) ^ 2
        = 4 * (∑ k ∈ range (n + 1), (k : ℤ) ^ 2 * ((n.choose k : ℤ)) ^ 2)
          - 4 * n * (∑ k ∈ range (n + 1), (k : ℤ) * ((n.choose k : ℤ)) ^ 2)
          + n ^ 2 * (∑ k ∈ range (n + 1), ((n.choose k : ℤ)) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  -- Cast the three raw-moment closed forms to ℤ.
  have hS0 : ∑ k ∈ range (n + 1), ((n.choose k : ℤ)) ^ 2 = ((2 * n).choose n : ℤ) := by
    have h := CombinationsFormulaOQ07.central_binom_eq_sum_sq n
    exact_mod_cast h.symm
  have hS1 : ∑ k ∈ range (n + 1), (k : ℤ) * ((n.choose k : ℤ)) ^ 2
      = (n : ℤ) * (((2 * n - 1).choose (n - 1) : ℕ) : ℤ) := by
    exact_mod_cast CombinationsFormulaOQ07OQ03.sum_weighted_sq n hn
  have hS2 : ∑ k ∈ range (n + 1), (k : ℤ) ^ 2 * ((n.choose k : ℤ)) ^ 2
      = (n : ℤ) ^ 2 * (((2 * (n - 1)).choose (n - 1) : ℕ) : ℤ) := by
    exact_mod_cast CombinationsFormulaOQ07OQ04.sum_sq_weighted_sq n
  -- The two central-binomial relations, cast to ℤ.
  have hR1 : ((2 * n).choose n : ℤ) = 2 * (((2 * n - 1).choose (n - 1) : ℕ) : ℤ) := by
    exact_mod_cast CombinationsFormulaOQ07OQ03.central_binom_two_mul_pred n hn
  have hR2 : (n : ℤ) * ((2 * n).choose n : ℤ)
      = 2 * (2 * (n : ℤ) - 1) * (((2 * (n - 1)).choose (n - 1) : ℕ) : ℤ) := by
    have e : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := by omega
    have h := CombinationsFormulaOQ07OQ04.central_binom_recurrence n hn
    calc (n : ℤ) * ((2 * n).choose n : ℤ)
        = ((n * (2 * n).choose n : ℕ) : ℤ) := by push_cast; ring
      _ = ((2 * (2 * n - 1) * (2 * (n - 1)).choose (n - 1) : ℕ) : ℤ) := by rw [h]
      _ = 2 * ((2 * n - 1 : ℕ) : ℤ) * (((2 * (n - 1)).choose (n - 1) : ℕ) : ℤ) := by
            push_cast; ring
      _ = 2 * (2 * (n : ℤ) - 1) * (((2 * (n - 1)).choose (n - 1) : ℕ) : ℤ) := by rw [e]
  rw [hexpand, hS2, hS1, hS0]
  linear_combination (2 * (n : ℤ) ^ 2 * (2 * (n : ℤ) - 1)) * hR1 + (-2 * (n : ℤ) ^ 2) * hR2

/-- **The variance in lowest terms.** Dividing the cleared identity `(★)` by
    `4 · (2n − 1) · C(2n, n)` gives the variance of the distribution
    `k ↦ C(n,k)² / C(2n, n)`:

      (∑_{k=0}^{n} (k − n/2)² · C(n,k)²) / C(2n, n)  =  n² / (4(2n − 1)).

    Stated over `ℚ`, with `(k − n/2)² = (2k − n)² / 4`. -/
theorem variance_eq (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ range (n + 1), ((k : ℚ) - n / 2) ^ 2 * ((n.choose k : ℚ)) ^ 2)
        / ((2 * n).choose n : ℚ)
      = (n : ℚ) ^ 2 / (4 * (2 * (n : ℚ) - 1)) := by
  have hc : ((2 * n).choose n : ℚ) ≠ 0 := by
    have : 0 < (2 * n).choose n := Nat.choose_pos (by omega)
    positivity
  have h2n1 : (2 * (n : ℚ) - 1) ≠ 0 := by
    have : (1 : ℚ) ≤ n := by exact_mod_cast hn
    nlinarith
  -- Bring the centred identity (★) into ℚ.
  have hkey : (2 * (n : ℚ) - 1) *
      ∑ k ∈ range (n + 1), (2 * (k : ℚ) - n) ^ 2 * ((n.choose k : ℚ)) ^ 2
        = (n : ℚ) ^ 2 * ((2 * n).choose n : ℚ) := by
    have h := centred_second_moment n hn
    have hcast := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hcast
    convert hcast using 2
  -- Rewrite (k − n/2)² = (2k − n)²/4 inside the sum.
  have hsum : ∑ k ∈ range (n + 1), ((k : ℚ) - n / 2) ^ 2 * ((n.choose k : ℚ)) ^ 2
      = (∑ k ∈ range (n + 1), (2 * (k : ℚ) - n) ^ 2 * ((n.choose k : ℚ)) ^ 2) / 4 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsum]
  field_simp
  nlinarith [hkey]

/-- Sanity check of `(★)` at `n = 3`:
    `5 · ∑ (2k−3)²·C(3,k)² = 5·36 = 180 = 9·20 = 3²·C(6,3)`. -/
example :
    (2 * (3 : ℤ) - 1) *
        ∑ k ∈ range 4, (2 * (k : ℤ) - 3) ^ 2 * (((3 : ℕ).choose k : ℤ)) ^ 2
      = (3 : ℤ) ^ 2 * ((2 * 3).choose 3 : ℤ) := by decide

/-- Sanity check at `n = 2`: `3 · (4 + 0 + 4) = 24 = 4·6 = 2²·C(4,2)`. -/
example :
    (2 * (2 : ℤ) - 1) *
        ∑ k ∈ range 3, (2 * (k : ℤ) - 2) ^ 2 * (((2 : ℕ).choose k : ℤ)) ^ 2
      = (2 : ℤ) ^ 2 * ((2 * 2).choose 2 : ℤ) := by decide

end CombinationsFormulaOQ07OQ04OQ02
