import Proofs.CombinationsFormulaOQ03
import Mathlib.Tactic

/-
# The q-Binomial Theorem (Gauss's q-Analog of the Binomial Theorem)

## What This Proves
Gauss's finite q-binomial theorem: the product of the linear factors
`(1 + q^i x)` for `i = 0, …, n-1` expands as a q-weighted sum of the
Gaussian binomial coefficients,

    ∏_{i=0}^{n-1} (1 + q^i · x) = ∑_{k=0}^{n} [n choose k]_q · q^{C(k,2)} · x^k,

where `C(k,2) = k(k-1)/2 = Nat.choose k 2` is the k-th triangular number.
This is the fundamental identity of the theory of q-hypergeometric series and
the q-analog of the classical binomial theorem `(1 + x)^n = ∑ C(n,k) x^k`
(recovered here by setting `q = 1`).

## Approach
- Reuse the q-binomial framework from `CombinationsFormulaOQ03` (namespace
  `QBinomialCoefficients`): the definition `qBinom`, the two q-Pascal
  recurrences, the vanishing lemma, and the `q = 1` specialization.
- Prove the main identity by induction on `n`. The inductive step multiplies
  the level-`n` expansion by `(1 + q^n x)`, re-indexes, and matches
  coefficients using the *second* q-Pascal recurrence
  `[n+1,k+1]_q = q^{n-k}·[n,k]_q + [n,k+1]_q`
  together with the triangular-number identity `C(k+1,2) = k + C(k,2)`.
- Derive corollaries: the signed form `∏ (1 - q^i x)` (substitute `x ↦ -x`)
  and the classical binomial theorem (`q = 1`).

## Status
- [x] q-binomial theorem `∏ (1 + q^i x) = ∑ [n,k]_q q^{C(k,2)} x^k`
- [x] Signed variant `∏ (1 - q^i x) = ∑ (-1)^k [n,k]_q q^{C(k,2)} x^k`
- [x] Classical binomial theorem recovered at `q = 1`
- [x] Concrete verification at `n = 2`

## Provenance
Answers `combinations-formula-oq-03-oq-02`: the q-analog of the binomial theorem
as a polynomial identity, foundational identity of q-hypergeometric series.
The parent entry (`combinations-formula-oq-03`) built the `qBinom` machinery but
stopped short of this generating-function identity.
-/

namespace QBinomialCoefficients

open Finset

variable {R : Type*} [CommRing R]

-- ============================================================
-- The q-Binomial Theorem
-- ============================================================

/-- **Gauss's q-Binomial Theorem** (finite form).

    `∏_{i=0}^{n-1} (1 + q^i · x) = ∑_{k=0}^{n} [n choose k]_q · q^{C(k,2)} · x^k`.

    The exponent `C(k,2) = Nat.choose k 2 = k(k-1)/2` is the k-th triangular
    number. At `q = 1` every `q^{C(k,2)}` collapses to `1` and each `[n,k]_1`
    becomes `C(n,k)`, recovering the ordinary binomial theorem. -/
theorem qBinom_gauss (q x : R) : ∀ n : ℕ,
    ∏ i ∈ Finset.range n, (1 + q ^ i * x)
      = ∑ k ∈ Finset.range (n + 1), qBinom q n k * q ^ (Nat.choose k 2) * x ^ k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    -- Coefficient recurrence: the (k+1)-st level-(n+1) term splits into a
    -- `q^n x`-shifted level-n term plus the level-n term of the same index.
    have hkey : ∀ k, k ≤ n →
        qBinom q (n + 1) (k + 1) * q ^ (Nat.choose (k + 1) 2) * x ^ (k + 1)
          = q ^ n * x * (qBinom q n k * q ^ (Nat.choose k 2) * x ^ k)
            + qBinom q n (k + 1) * q ^ (Nat.choose (k + 1) 2) * x ^ (k + 1) := by
      intro k hk
      have hc : Nat.choose (k + 1) 2 = k + Nat.choose k 2 := by
        rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]
      have hexp : q ^ (n - k) * q ^ (Nat.choose (k + 1) 2)
          = q ^ n * q ^ (Nat.choose k 2) := by
        rw [← pow_add, ← pow_add, hc]; congr 1; omega
      rw [qBinom_pascal' q n k (by omega)]
      linear_combination (qBinom q n k * x ^ (k + 1)) * hexp
    -- The `k = n+1` term of the level-n family vanishes (index exceeds `n`).
    have hlast : qBinom q n (n + 1) * q ^ (Nat.choose (n + 1) 2) * x ^ (n + 1) = 0 := by
      rw [qBinom_eq_zero_of_lt q n (n + 1) (by omega)]; ring
    -- `1` equals the `k = 0` level-n term, used to re-fold the shifted sum.
    have hg0 : qBinom q n 0 * q ^ (Nat.choose 0 2) * x ^ 0 = 1 := by simp
    -- Shift identity: ∑_{k<n+1} g(k+1) + 1 = ∑_{k<n+1} g(k).
    have hshift :
        (∑ k ∈ Finset.range (n + 1),
            qBinom q n (k + 1) * q ^ (Nat.choose (k + 1) 2) * x ^ (k + 1)) + 1
          = ∑ k ∈ Finset.range (n + 1), qBinom q n k * q ^ (Nat.choose k 2) * x ^ k := by
      rw [← hg0,
          ← Finset.sum_range_succ' (fun k => qBinom q n k * q ^ (Nat.choose k 2) * x ^ k) (n + 1),
          Finset.sum_range_succ (fun k => qBinom q n k * q ^ (Nat.choose k 2) * x ^ k) (n + 1),
          hlast, add_zero]
    -- Main computation.
    rw [Finset.prod_range_succ, ih,
        Finset.sum_range_succ' (fun k => qBinom q (n + 1) k * q ^ (Nat.choose k 2) * x ^ k) (n + 1),
        Finset.sum_congr rfl
          (fun k hk => hkey k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))),
        Finset.sum_add_distrib, ← Finset.mul_sum]
    -- Goal: (∑ g) * (1 + q^n x) = (q^n x * ∑ g + ∑ g(k+1)) + G 0
    have hG0 : qBinom q (n + 1) 0 * q ^ (Nat.choose 0 2) * x ^ 0 = 1 := by simp
    rw [hG0, add_assoc, hshift]
    ring

-- ============================================================
-- Corollaries
-- ============================================================

/-- **Signed q-Binomial Theorem**: substituting `x ↦ -x` gives the alternating
    product `∏ (1 - q^i x)` expanded with signs `(-1)^k`. -/
theorem qBinom_gauss_neg (q x : R) (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 - q ^ i * x)
      = ∑ k ∈ Finset.range (n + 1),
          (-1) ^ k * qBinom q n k * q ^ (Nat.choose k 2) * x ^ k := by
  have h := qBinom_gauss q (-x) n
  rw [Finset.prod_congr rfl
        (fun i _ => by ring :
          ∀ i ∈ Finset.range n, 1 + q ^ i * (-x) = 1 - q ^ i * x)] at h
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (-x) = (-1 : R) * x by ring, mul_pow]
  ring

/-- **Classical Binomial Theorem, recovered at `q = 1`**:
    `(1 + x)^n = ∑_{k=0}^{n} C(n,k) · x^k`.
    This exhibits the q-binomial theorem as a genuine generalization. -/
theorem binom_theorem_of_qBinom (x : R) (n : ℕ) :
    (1 + x) ^ n = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : R) * x ^ k := by
  have h := qBinom_gauss (1 : R) x n
  simp only [one_pow, one_mul, mul_one, qBinom_at_one] at h
  rw [Finset.prod_const, Finset.card_range] at h
  exact h

-- ============================================================
-- Concrete verification
-- ============================================================

/-- At `n = 2`: `(1 + x)(1 + q x) = 1 + (1 + q) x + q x^2`. -/
example (q x : R) :
    ∏ i ∈ Finset.range 2, (1 + q ^ i * x) = 1 + (1 + q) * x + q * x ^ 2 := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
  ring

/-- The n = 2 expansion matches the q-binomial theorem's right-hand side. -/
example (q x : R) :
    (∑ k ∈ Finset.range 3, qBinom q 2 k * q ^ (Nat.choose k 2) * x ^ k)
      = 1 + (1 + q) * x + q * x ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
  simp [qBinom]

end QBinomialCoefficients
