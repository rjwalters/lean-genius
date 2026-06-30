/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-01-oq-01:
# The mean and variance of the descent statistic from the Eulerian numbers

The combinatorial **Eulerian number** `⟨n,k⟩` (`eulerian n k`, built by the grandparent entry
`geometric-series-oq-07-oq-01-oq-01-oq-01`) counts the permutations of `{1,…,n}` with exactly `k`
descents.  The parent `…-oq-01` established the **row sum** `∑ₖ ⟨n,k⟩ = n!` (every permutation
has between `0` and `n−1` descents) and the sibling `…-oq-05` the **palindromy**
`⟨n,k⟩ = ⟨n,n−1−k⟩`.  Together these say the row `(⟨n,0⟩,…,⟨n,n−1⟩)` is the *distribution of the
number of descents* of a uniformly random permutation of `{1,…,n}`.

This entry computes the first two **moments** of that distribution — statements about the *shape*
of the Eulerian row, not exact entry values, and so genuinely distinct from the identities already
in the family:

* `eulerian_first_moment`  : `2·∑ₖ k·⟨n,k⟩ = (n−1)·n!`           (mean number of descents `(n−1)/2`);
* `eulerian_second_moment` : `12·∑ₖ k²·⟨n,k⟩ = n!·(3n²−5n+4)`    (for `n ≥ 2`);
* `eulerian_variance`      : `12·(M₂·n! − M₁²) = (n+1)·n!²`       (variance of descents `(n+1)/12`).

For example, row `3` is `1,4,1`: `∑ k·⟨3,k⟩ = 0+4+2 = 6 = (3−1)·3!/2`, so the mean is `1`; and
`∑ k²·⟨3,k⟩ = 0+4+4 = 8`, giving `E[X²] = 8/6 = 4/3` and variance `4/3 − 1 = 1/3 = (3+1)/12`.

## Method

The **mean** is read straight off the palindromy: reflecting `k ↦ n−1−k`
(`Finset.sum_range_reflect`) pairs `k·⟨n,k⟩` with `(n−1−k)·⟨n,k⟩`, so twice the first moment is
`∑ₖ (n−1)·⟨n,k⟩ = (n−1)·n!`.

The **second moment** needs more than symmetry.  The engine is a single **moment-transfer lemma**
(`moment_transfer`): for any integer weight `w`,

  `∑_{k} w(k)·⟨n+1,k⟩ = ∑_{i} (w(i)·(i+1) + w(i+1)·(n−i))·⟨n,i⟩`,

obtained from the triangle recurrence `⟨n+1,k+1⟩ = (k+2)·⟨n,k+1⟩ + (n−k)·⟨n,k⟩` by peeling the
`k=0` term and reindexing the shifted sum.  Specialising `w(k) = k²` and simplifying the
coefficient `i²(i+1)+(i+1)²(n−i) = (n−1)i² + (2n−1)i + n` turns it into the moment recurrence
`M₂(n+1) = (n−1)·M₂(n) + (2n−1)·M₁(n) + n·M₀(n)`, which closes the closed form by induction on
`n ≥ 2` (feeding in `M₀ = n!` and the mean `M₁`).  The **variance** is then pure algebra.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ01
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ05

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ01

open Nat Finset GeometricSeriesOQ07OQ01OQ01OQ01 GeometricSeriesOQ07OQ01OQ01OQ01OQ01
  GeometricSeriesOQ07OQ01OQ01OQ01OQ05

/-! ## The zeroth moment (row sum) -/

/-- The `p = 0` "moment": the row sum `∑ₖ ⟨n,k⟩ = n!`, cast to `ℤ`. -/
theorem eulerian_M0 (n : ℕ) : ∑ k ∈ range (n + 1), (eulerian n k : ℤ) = (n ! : ℤ) := by
  have h := eulerian_row_sum n
  exact_mod_cast h

/-! ## The moment-transfer lemma -/

/-- **Moment transfer.**  For an arbitrary integer weight `w`, the weighted row-`(n+1)` sum is a
weighted row-`n` sum: `∑_{k} w(k)·⟨n+1,k⟩ = ∑_{i} (w(i)·(i+1) + w(i+1)·(n−i))·⟨n,i⟩`.  Proved by
peeling the `k = 0` term, expanding the triangle recurrence, and reindexing the shifted sum
`∑_j w(j+1)·(j+2)·⟨n,j+1⟩` back over `⟨n,i⟩`. -/
theorem moment_transfer (w : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 2), w k * (eulerian (n + 1) k : ℤ)
      = ∑ i ∈ range (n + 1),
          (w i * ((i : ℤ) + 1) + w (i + 1) * ((n : ℤ) - i)) * (eulerian n i : ℤ) := by
  -- Peel the `k = 0` term off the left sum (`⟨n+1,0⟩ = 1`).
  have hL : ∑ k ∈ range (n + 2), w k * (eulerian (n + 1) k : ℤ)
      = (∑ j ∈ range (n + 1), w (j + 1) * (eulerian (n + 1) (j + 1) : ℤ)) + w 0 := by
    rw [Finset.sum_range_succ', eulerian_succ_zero]
    push_cast; ring
  -- Expand the triangle recurrence inside the shifted sum.
  have hL2 : ∑ j ∈ range (n + 1), w (j + 1) * (eulerian (n + 1) (j + 1) : ℤ)
      = (∑ j ∈ range (n + 1), w (j + 1) * ((j : ℤ) + 2) * (eulerian n (j + 1) : ℤ))
        + (∑ j ∈ range (n + 1), w (j + 1) * ((n : ℤ) - j) * (eulerian n j : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [eulerian_succ_succ]
    push_cast [Nat.cast_sub (by omega : j ≤ n)]
    ring
  -- Reindex the first shifted sum `∑_j w(j+1)·(j+2)·⟨n,j+1⟩` back over `⟨n,i⟩`.
  have hA : ∑ j ∈ range (n + 1), w (j + 1) * ((j : ℤ) + 2) * (eulerian n (j + 1) : ℤ)
      = (∑ i ∈ range (n + 1), w i * ((i : ℤ) + 1) * (eulerian n i : ℤ)) - w 0 := by
    -- Align the bodies of the two `range n` sums (`↑(i+1)+1 = ↑i+2`).
    have hbody : ∀ i ∈ range n,
        w (i + 1) * (((i + 1 : ℕ) : ℤ) + 1) * (eulerian n (i + 1) : ℤ)
          = w (i + 1) * ((i : ℤ) + 2) * (eulerian n (i + 1) : ℤ) := by
      intro i _; push_cast; ring
    -- Peel the boundary terms: the `i = 0` term of the right sum is `w 0`, and the
    -- `j = n` term of the left sum vanishes (`⟨n,n+1⟩ = 0`).
    rw [Finset.sum_range_succ' (fun i => w i * ((i : ℤ) + 1) * (eulerian n i : ℤ)) n,
        eulerian_col_zero,
        Finset.sum_range_succ
          (fun j => w (j + 1) * ((j : ℤ) + 2) * (eulerian n (j + 1) : ℤ)) n,
        eulerian_eq_zero_of_lt (Nat.lt_succ_self n),
        Finset.sum_congr rfl hbody]
    push_cast; ring
  -- Assemble.
  have target : ∑ i ∈ range (n + 1),
        (w i * ((i : ℤ) + 1) + w (i + 1) * ((n : ℤ) - i)) * (eulerian n i : ℤ)
      = (∑ i ∈ range (n + 1), w i * ((i : ℤ) + 1) * (eulerian n i : ℤ))
        + ∑ i ∈ range (n + 1), w (i + 1) * ((n : ℤ) - i) * (eulerian n i : ℤ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hL, hL2, hA, target]
  ring

/-! ## The first moment: the mean number of descents is `(n−1)/2` -/

/-- **First moment of the descent statistic.**  `2·∑ₖ k·⟨n,k⟩ = (n−1)·n!` for `n ≥ 1`: the
expected number of descents of a uniformly random permutation of `{1,…,n}` is `(n−1)/2`.  Proved
from palindromy — reflecting `k ↦ n−1−k` pairs `k·⟨n,k⟩` with `(n−1−k)·⟨n,k⟩`. -/
theorem eulerian_first_moment (n : ℕ) (hn : 1 ≤ n) :
    2 * ∑ k ∈ range (n + 1), (k : ℤ) * (eulerian n k : ℤ) = ((n : ℤ) - 1) * (n ! : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- The top term `k = m+1` vanishes, so the moment is a sum over `range (m+1)`.
  have hdrop : ∑ k ∈ range (m + 1 + 1), (k : ℤ) * (eulerian (m + 1) k : ℤ)
      = ∑ k ∈ range (m + 1), (k : ℤ) * (eulerian (m + 1) k : ℤ) := by
    rw [Finset.sum_range_succ, eulerian_succ_self]
    simp
  -- The row sum over `range (m+1)`.
  have hrow : ∑ k ∈ range (m + 1), (eulerian (m + 1) k : ℤ) = ((m + 1)! : ℤ) := by
    have h := eulerian_M0 (m + 1)
    rwa [Finset.sum_range_succ, eulerian_succ_self, Nat.cast_zero, add_zero] at h
  -- Reflection identity for the weighted summand.
  have hrefl :
      ∑ k ∈ range (m + 1), ((m + 1 - 1 - k : ℕ) : ℤ) * (eulerian (m + 1) (m + 1 - 1 - k) : ℤ)
        = ∑ k ∈ range (m + 1), (k : ℤ) * (eulerian (m + 1) k : ℤ) :=
    Finset.sum_range_reflect (fun k => (k : ℤ) * (eulerian (m + 1) k : ℤ)) (m + 1)
  -- Twice the moment = `m · rowsum` via the reflection.
  have hsum2 : (∑ k ∈ range (m + 1), (k : ℤ) * (eulerian (m + 1) k : ℤ))
        + (∑ k ∈ range (m + 1), (k : ℤ) * (eulerian (m + 1) k : ℤ))
      = ∑ k ∈ range (m + 1), (m : ℤ) * (eulerian (m + 1) k : ℤ) := by
    conv_lhs => lhs; rw [← hrefl]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hpal : eulerian (m + 1) (m + 1 - 1 - k) = eulerian (m + 1) k :=
      (eulerian_palindrome' (by omega : 1 ≤ m + 1) (by omega : k < m + 1)).symm
    rw [hpal]
    have hcast : ((m + 1 - 1 - k : ℕ) : ℤ) = (m : ℤ) - (k : ℤ) := by
      have h0 : (m + 1 - 1 - k : ℕ) = m - k := by omega
      rw [h0, Nat.cast_sub (by omega : k ≤ m)]
    rw [hcast]; ring
  rw [hdrop, two_mul, hsum2, ← Finset.mul_sum, hrow]
  push_cast; ring

/-! ## The second moment via the moment recurrence -/

/-- The second-moment recurrence, read off `moment_transfer` with weight `w(k) = k²`:
`M₂(n+1) = (n−1)·M₂(n) + (2n−1)·M₁(n) + n·M₀(n)`. -/
theorem eulerian_M2_succ (n : ℕ) :
    ∑ k ∈ range (n + 2), (k : ℤ) ^ 2 * (eulerian (n + 1) k : ℤ)
      = ((n : ℤ) - 1) * (∑ k ∈ range (n + 1), (k : ℤ) ^ 2 * (eulerian n k : ℤ))
        + (2 * (n : ℤ) - 1) * (∑ k ∈ range (n + 1), (k : ℤ) * (eulerian n k : ℤ))
        + (n : ℤ) * (∑ k ∈ range (n + 1), (eulerian n k : ℤ)) := by
  rw [moment_transfer (fun k => (k : ℤ) ^ 2) n]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- **Second moment of the descent statistic.**  `12·∑ₖ k²·⟨n,k⟩ = n!·(3n²−5n+4)` for `n ≥ 2`.
Induction on `n` from the base row `n = 2`, stepping with `eulerian_M2_succ` and feeding in the
row sum `M₀ = n!` and the first moment `M₁`. -/
theorem eulerian_second_moment (n : ℕ) (hn : 2 ≤ n) :
    12 * ∑ k ∈ range (n + 1), (k : ℤ) ^ 2 * (eulerian n k : ℤ)
      = (n ! : ℤ) * (3 * (n : ℤ) ^ 2 - 5 * n + 4) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hM0 : ∑ k ∈ range (n + 1), (eulerian n k : ℤ) = (n ! : ℤ) := eulerian_M0 n
    have hM1 : 2 * ∑ k ∈ range (n + 1), (k : ℤ) * (eulerian n k : ℤ) = ((n : ℤ) - 1) * (n ! : ℤ) :=
      eulerian_first_moment n (by omega)
    rw [eulerian_M2_succ, hM0, Nat.factorial_succ]
    push_cast
    linear_combination ((n : ℤ) - 1) * ih + 6 * (2 * (n : ℤ) - 1) * hM1

/-! ## The variance of the descent statistic is `(n+1)/12` -/

/-- **Variance of the descent statistic.**  Writing `M₁ = ∑ₖ k·⟨n,k⟩` and `M₂ = ∑ₖ k²·⟨n,k⟩`, the
variance `M₂/n! − (M₁/n!)²` of the number of descents equals `(n+1)/12` for `n ≥ 2`.  Stated cleared
of denominators over `ℤ`: `12·(M₂·n! − M₁²) = (n+1)·n!²`.  Combines the first and second moments. -/
theorem eulerian_variance (n : ℕ) (hn : 2 ≤ n) :
    12 * ((∑ k ∈ range (n + 1), (k : ℤ) ^ 2 * (eulerian n k : ℤ)) * (n ! : ℤ)
            - (∑ k ∈ range (n + 1), (k : ℤ) * (eulerian n k : ℤ)) ^ 2)
      = ((n : ℤ) + 1) * (n ! : ℤ) ^ 2 := by
  have hA := eulerian_second_moment n hn
  have hB := eulerian_first_moment n (by omega)
  linear_combination (n ! : ℤ) * hA
    - 3 * (2 * (∑ k ∈ range (n + 1), (k : ℤ) * (eulerian n k : ℤ)) + ((n : ℤ) - 1) * (n ! : ℤ)) * hB

/-! ## Corroboration on concrete rows -/

-- Mean of descents: row 3 `1,4,1` has `∑ k·⟨3,k⟩ = 6 = (3−1)·3!/2`.
example : 2 * ∑ k ∈ range 4, (k : ℤ) * (eulerian 3 k : ℤ) = ((3 : ℤ) - 1) * (3 ! : ℤ) := by decide
-- Second moment: row 3 has `∑ k²·⟨3,k⟩ = 8`, and `12·8 = 3!·(3·9−15+4) = 6·16`.
example : 12 * ∑ k ∈ range 4, (k : ℤ) ^ 2 * (eulerian 3 k : ℤ)
    = (3 ! : ℤ) * (3 * (3 : ℤ) ^ 2 - 5 * 3 + 4) := by decide
-- Variance of row 4 (`1,11,11,1`): `12·(M₂·4! − M₁²) = (4+1)·(4!)²`.
example : 12 * ((∑ k ∈ range 5, (k : ℤ) ^ 2 * (eulerian 4 k : ℤ)) * (4 ! : ℤ)
      - (∑ k ∈ range 5, (k : ℤ) * (eulerian 4 k : ℤ)) ^ 2)
    = ((4 : ℤ) + 1) * (4 ! : ℤ) ^ 2 := by decide

end GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ01
