/-
  General Newton–Girard Recurrence for arbitrary k

  Open Question (amgm-inequality-oq-02-oq-01-oq-02-oq-01-oq-01-oq-01):
  The parent proof established the Newton–Girard recurrence only for the
  fixed degrees k = 4 and k = 5 (and the grandparent handled k = 1, 2, 3),
  each by hand-expanding the antidiagonal of the corresponding degree.

  This file proves the GENERAL recurrence for ARBITRARY k ≥ 1, in the
  classical Newton–Girard shape

      pₖ = ∑_{i=1}^{k-1} (-1)^(i+1) · eᵢ · pₖ₋ᵢ  +  (-1)^(k+1) · k · eₖ

  i.e. (writing it out)

      pₖ = e₁·pₖ₋₁ − e₂·pₖ₋₂ + e₃·pₖ₋₃ − ⋯ + (-1)^(k+1)·k·eₖ.

  A single theorem here subsumes the parent's `psum_four_eq`, `psum_five_eq`
  and the grandparent's k = 1, 2, 3 corollaries (and every other degree),
  replacing the per-degree antidiagonal book-keeping by one reindexing of the
  filtered antidiagonal occurring in Mathlib's
  `MvPolynomial.psum_eq_mul_esymm_sub_sum`:

      pₖ = (-1)^(k+1)·k·eₖ − ∑_{0<a<k} (-1)^a · eₐ · pₖ₋ₐ.

  The only work is to rewrite the filtered antidiagonal sum
  `∑ a ∈ antidiagonal k, a.1 ∈ Ioo 0 k` as a sum over the interval
  `Ico 1 k` of the index `i = a.1` (with `a.2 = k - i`), and to fold the
  outer minus sign into the alternating sign `(-1)^(i+1)`.

  We also record the dual form (solving for `k · eₖ`) and verify, as a
  sanity check, that specialising to k = 4 recovers the parent's statement
  verbatim.

  Status: PROVED — general k via antidiagonal reindexing + ring
  Axioms: 0, Sorries: 0
  Tags: algebra, symmetric-functions, newton-girard, power-sums, mv-polynomial
-/

import Mathlib

namespace AmgmInequalityOQ02OQ01OQ02OQ01OQ01OQ01

open MvPolynomial Finset BigOperators Set

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

-- ============================================================
-- General Newton–Girard recurrence (arbitrary k ≥ 1)
-- ============================================================

/-- **General Newton–Girard recurrence.** For every `k ≥ 1` the `k`-th power
sum is determined by the lower power sums and the elementary symmetric
polynomials through

  `pₖ = ∑_{i=1}^{k-1} (-1)^(i+1) · eᵢ · pₖ₋ᵢ  +  (-1)^(k+1) · k · eₖ`.

This is the classical Newton–Girard identity, valid over any `CommRing` and
any finite collection of variables.  It subsumes the per-degree corollaries
(k = 1, 2, 3, 4, 5, …) obtained in the ancestor entries.

The proof reindexes the filtered antidiagonal sum that appears in Mathlib's
`MvPolynomial.psum_eq_mul_esymm_sub_sum` as a sum over `Finset.Ico 1 k`. -/
theorem psum_recurrence (k : ℕ) (hk : 0 < k) :
    psum σ R k =
      (∑ i ∈ Finset.Ico 1 k,
        (-1 : MvPolynomial σ R) ^ (i + 1) * esymm σ R i * psum σ R (k - i))
      + (-1 : MvPolynomial σ R) ^ (k + 1) * (k : MvPolynomial σ R) * esymm σ R k := by
  -- The filter `i ∈ Ioo 0 k` over `range (k+1)` is exactly `Ico 1 k`.
  have hfilt :
      (Finset.range (k + 1)).filter (fun i => i ∈ Set.Ioo 0 k) = Finset.Ico 1 k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Set.mem_Ioo]
    omega
  -- Reindex the Mathlib filtered-antidiagonal sum (index `a`) to the interval
  -- `Ico 1 k` (index `i = a.1`, with `a.2 = k - i`).
  have hS :
      (∑ a ∈ (Finset.antidiagonal k).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 k),
          (-1 : MvPolynomial σ R) ^ a.fst * esymm σ R a.1 * psum σ R a.2)
        = ∑ i ∈ Finset.Ico 1 k,
            (-1 : MvPolynomial σ R) ^ i * esymm σ R i * psum σ R (k - i) := by
    rw [← hfilt, Finset.sum_filter, Finset.sum_filter,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
          (fun a : ℕ × ℕ =>
            if a.1 ∈ Set.Ioo 0 k then
              (-1 : MvPolynomial σ R) ^ a.fst * esymm σ R a.1 * psum σ R a.2
            else 0) k]
  -- Apply Mathlib's identity and substitute the reindexed sum.
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R k hk, hS]
  -- The alternating-sign sum and the `(-1)^i` sum are negatives of each other.
  have hTU :
      (∑ i ∈ Finset.Ico 1 k,
          (-1 : MvPolynomial σ R) ^ (i + 1) * esymm σ R i * psum σ R (k - i))
        + (∑ i ∈ Finset.Ico 1 k,
            (-1 : MvPolynomial σ R) ^ i * esymm σ R i * psum σ R (k - i)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [pow_succ]
    ring
  linear_combination -hTU

-- ============================================================
-- Dual form: solving for k · eₖ
-- ============================================================

/-- **Dual Newton–Girard recurrence.** Rearranging `psum_recurrence` to isolate
the top elementary symmetric polynomial:

  `(-1)^(k+1) · k · eₖ = pₖ − ∑_{i=1}^{k-1} (-1)^(i+1) · eᵢ · pₖ₋ᵢ`.

Multiplying through by `(-1)^(k+1)` (a unit) expresses `k · eₖ` purely in terms
of power sums and lower elementary symmetric polynomials. -/
theorem mul_esymm_recurrence (k : ℕ) (hk : 0 < k) :
    (-1 : MvPolynomial σ R) ^ (k + 1) * (k : MvPolynomial σ R) * esymm σ R k =
      psum σ R k
        - ∑ i ∈ Finset.Ico 1 k,
            (-1 : MvPolynomial σ R) ^ (i + 1) * esymm σ R i * psum σ R (k - i) := by
  rw [psum_recurrence σ R k hk]
  ring

-- ============================================================
-- Subsumption check: recover the parent's k = 4 corollary
-- ============================================================

/-- Specialising the general recurrence to `k = 4` reproduces the parent
entry's `psum_four_eq` verbatim, confirming that the single general theorem
subsumes the hand-expanded fixed-degree corollaries. -/
example :
    psum σ R 4 = esymm σ R 1 * psum σ R 3 - esymm σ R 2 * psum σ R 2 +
                esymm σ R 3 * psum σ R 1 - 4 * esymm σ R 4 := by
  have h : Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [psum_recurrence σ R 4 (by norm_num), h,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  norm_num
  ring

/-- Specialising the general recurrence to `k = 5` reproduces the parent
entry's `psum_five_eq` verbatim. -/
example :
    psum σ R 5 = esymm σ R 1 * psum σ R 4 - esymm σ R 2 * psum σ R 3 +
                esymm σ R 3 * psum σ R 2 - esymm σ R 4 * psum σ R 1 +
                5 * esymm σ R 5 := by
  have h : Finset.Ico 1 5 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [psum_recurrence σ R 5 (by norm_num), h,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
  ring

end AmgmInequalityOQ02OQ01OQ02OQ01OQ01OQ01
