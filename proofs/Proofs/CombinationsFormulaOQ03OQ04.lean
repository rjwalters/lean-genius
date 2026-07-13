import Proofs.CombinationsFormulaOQ03

/-
# Self-Reciprocity (Palindromy) of Gaussian q-Binomial Coefficients

## What This Proves
The Gaussian binomial coefficient [n choose k]_q, viewed as a polynomial in q,
is **palindromic** (self-reciprocal) of degree k·(n-k). Over a field, this is the
clean algebraic identity

    [n choose k]_q = q^{k(n-k)} · [n choose k]_{1/q}   (for q ≠ 0).

Reading off coefficients, this says the coefficient sequence of [n,k]_q reads the
same forwards and backwards: a_j = a_{k(n-k)-j}. This palindromy is the *symmetric*
half of Sylvester's theorem (1878): the coefficient sequence of [n,k]_q is a
symmetric **unimodal** sequence. Unimodality (the harder half, first proved
rigorously by Proctor 1982 via sl₂ representation theory) remains open in this
gallery; this file establishes the symmetry precursor rigorously and axiom-free.

## Approach
The parent file `CombinationsFormulaOQ03` defines [n,k]_q over an arbitrary
commutative ring via the q-Pascal recurrence and proves *both* Pascal identities:

  (P1)  [n+1,k+1]_q = [n,k]_q + q^{k+1}·[n,k+1]_q          (`qBinom_pascal`)
  (P2)  [n+1,k+1]_q = q^{n-k}·[n,k]_q + [n,k+1]_q          (`qBinom_pascal'`)

Palindromy follows by induction on n: expand the left side [n+1,k+1]_q via (P2)
and the reflected right side [n+1,k+1]_{1/q} via (P1); the induction hypothesis
then makes the two sides agree term-by-term after collecting powers of q. The key
cancellation is q^{(k+1)(n-k)}·(1/q)^{k+1} = q^{(k+1)(n-k-1)}, valid since q ≠ 0.

## Status
- [x] Self-reciprocity / palindromy: [n,k]_q = q^{k(n-k)}·[n,k]_{1/q}  (main)
- [x] Reflected form: q^{k(n-k)}·[n,k]_{1/q} = [n,k]_q
- [x] Involutivity sanity check of the reflection
- [x] `k = 1` unimodality milestone: coefficients of `[n,1]_q` are the all-ones
      vector `(1,…,1)` over `ℤ`, proved palindromic AND unimodal
- [ ] OPEN: coefficient unimodality for general `k` (Sylvester/Proctor)

## Honesty Note
The palindromy/symmetry results are for *all* `k`. Unimodality — the substantive
content of the open question — is proved here ONLY for `k = 1` (the flat all-ones
coefficient sequence), as an explicit first milestone. Full unimodality for
general `k` requires either an sl₂-action argument or an explicit injection
between coefficient levels and is NOT formalized here.
-/

namespace QBinomialCoefficients

open Nat

variable {R : Type*} [Field R]

/-- **Self-reciprocity (palindromy) of the Gaussian binomial coefficient.**

For a nonzero `q` in a field, the q-binomial coefficient satisfies

    [n choose k]_q = q^{k(n-k)} · [n choose k]_{q⁻¹}.

Equivalently, as a polynomial in `q` of degree `k(n-k)`, `[n,k]_q` is palindromic:
its coefficient sequence reads the same forwards and backwards. This is the
symmetric half of Sylvester's unimodality theorem.

The proof is by induction on `n`. The `k = 0`, `k > n`, and `k = n` (diagonal)
boundary cases are direct. In the generic interior case `k < n` we expand the left
side by the second q-Pascal identity `qBinom_pascal'` and the reflected right side
by the first q-Pascal identity `qBinom_pascal`, then apply the induction hypothesis
at `(n, k)` and `(n, k+1)`; the powers of `q` line up after the cancellation
`q^{(k+1)(n-k)} · (q⁻¹)^{k+1} = q^{(k+1)(n-k-1)}`. -/
theorem qBinom_reciprocal (q : R) (hq : q ≠ 0) :
    ∀ (n k : ℕ), qBinom q n k = q ^ (k * (n - k)) * qBinom q⁻¹ n k
  | _, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    rcases le_or_lt (k + 1) n with hkn | hkn
    · -- k + 1 ≤ n, i.e. k < n : generic interior case
      have hsplit : n - k = (n - k - 1) + 1 := by omega
      -- Expand LHS via the SECOND q-Pascal identity (P2)
      rw [qBinom_pascal' q n k (by omega)]
      -- Expand the reflected RHS via the FIRST q-Pascal identity (P1)
      rw [show n + 1 - (k + 1) = n - k from by omega, qBinom_pascal q⁻¹ n k]
      -- Apply the induction hypothesis to rewrite [n,k]_q and [n,k+1]_q
      rw [qBinom_reciprocal q hq n k, qBinom_reciprocal q hq n (k + 1),
          show n - (k + 1) = n - k - 1 from by omega]
      -- Abbreviate the two reflected atoms
      set A := qBinom q⁻¹ n k with hA
      set B := qBinom q⁻¹ n (k + 1) with hB
      -- Coefficient of A: q^{n-k} · q^{k(n-k)} = q^{(k+1)(n-k)}
      have hexpA : (n - k) + k * (n - k) = (k + 1) * (n - k) := by ring
      have eA : q ^ (n - k) * (q ^ (k * (n - k)) * A) = q ^ ((k + 1) * (n - k)) * A := by
        rw [← mul_assoc, ← pow_add, hexpA]
      -- Coefficient of B: q^{(k+1)(n-k-1)} = q^{(k+1)(n-k)} · (q⁻¹)^{k+1}
      have hexpB : (k + 1) * (n - k) = (k + 1) * (n - k - 1) + (k + 1) := by
        conv_lhs => rw [hsplit]
        ring
      have eB : q ^ ((k + 1) * (n - k - 1)) * B
          = q ^ ((k + 1) * (n - k)) * (q⁻¹ ^ (k + 1) * B) := by
        rw [hexpB, pow_add, inv_pow, mul_assoc,
            mul_inv_cancel_left₀ (pow_ne_zero (k + 1) hq)]
      rw [eA, eB]; ring
    · -- k + 1 > n : either the diagonal k = n or above it
      rcases eq_or_ne n k with heq | hne
      · -- n = k : diagonal, both q-binomials equal 1
        rw [heq]; simp
      · -- n < k : both q-binomials vanish
        rw [qBinom_eq_zero_of_lt q (n + 1) (k + 1) (by omega),
            qBinom_eq_zero_of_lt q⁻¹ (n + 1) (k + 1) (by omega), mul_zero]

/-- **Reflected form of self-reciprocity.** Applying `q^{k(n-k)}` to the
`q⁻¹`-binomial recovers the `q`-binomial. This is `qBinom_reciprocal` read from
right to left, packaged for convenience. -/
theorem qBinom_reflect (q : R) (hq : q ≠ 0) (n k : ℕ) :
    q ^ (k * (n - k)) * qBinom q⁻¹ n k = qBinom q n k :=
  (qBinom_reciprocal q hq n k).symm

/-- **Involutivity sanity check.** Applying reciprocity twice returns the original:
`[n,k]_q = q^{k(n-k)} · (q⁻¹)^{k(n-k)} · [n,k]_q`, and the two power factors cancel.
This confirms the reflection `q ↦ q⁻¹` composed with the `q^{k(n-k)}` twist is an
involution on the q-binomial, as a palindrome reflection must be. -/
theorem qBinom_reciprocal_involutive (q : R) (hq : q ≠ 0) (n k : ℕ) :
    qBinom q n k = q ^ (k * (n - k)) * ((q⁻¹) ^ (k * (n - k)) * qBinom q n k) := by
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow, one_mul]

/-! ### The k = 1 case of Sylvester's unimodality theorem

Palindromy (proved above) is only the *symmetric* half of Sylvester's theorem;
the substantive half is **unimodality** of the coefficient sequence, which is the
open question. Below we discharge the first requested milestone: the `k = 1` case.

The Gaussian binomial `[n,1]_q` is the `q`-number `[n]_q = 1 + q + ⋯ + q^{n-1}`,
whose coefficient sequence is the all-ones vector `(1,1,…,1)` of length `n`. That
sequence is (trivially) both palindromic and unimodal, giving the `k = 1` case of
Sylvester's theorem at the level of actual polynomial coefficients over `ℤ`. -/

/-- **Geometric-sum form of the q-number.** `[n]_q = ∑_{i<n} q^i`. This exhibits
`[n]_q`, equivalently `[n,1]_q = qBinom q n 1`, as an explicit polynomial whose
coefficients we can read off. Proved over an arbitrary commutative ring. -/
theorem qNumber_eq_geom_sum {S : Type*} [CommRing S] (q : S) :
    ∀ n : ℕ, qNumber q n = ∑ i ∈ Finset.range n, q ^ i
  | 0 => by simp
  | n + 1 => by
      rw [qNumber_succ, qNumber_eq_geom_sum q n, Finset.mul_sum,
          Finset.sum_range_succ', pow_zero]
      have hstep : ∑ i ∈ Finset.range n, q * q ^ i
          = ∑ i ∈ Finset.range n, q ^ (i + 1) :=
        Finset.sum_congr rfl fun i _ => (pow_succ' q i).symm
      rw [hstep]; ring

/-- **Explicit coefficients of the `k = 1` Gaussian binomial over `ℤ`.**
Realizing `q` as the indeterminate `X`, the `j`-th coefficient of `[n,1]_q` is
`1` for `j < n` and `0` otherwise — the all-ones coefficient sequence of length
`n`. This is the concrete polynomial-coefficient statement that the abstract
`q`-number reasoning bridges to. -/
theorem qBinom_one_coeff (n j : ℕ) :
    (qBinom (Polynomial.X : Polynomial ℤ) n 1).coeff j = if j < n then 1 else 0 := by
  rw [qBinom_one_right, qNumber_eq_geom_sum, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- **Palindromy of the `k = 1` coefficient sequence.** For `1 ≤ n`, the length-`n`
coefficient vector of `[n,1]_q` reads the same forwards and backwards about the
degree `k(n-k) = n-1`: `a_j = a_{(n-1)-j}` for every `j ≤ n-1`. This is the
`k = 1` instance of the palindromy proved abstractly above, now at the level of
`ℤ`-coefficients. -/
theorem qBinom_one_coeff_symm (n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n - 1) :
    (qBinom (Polynomial.X : Polynomial ℤ) n 1).coeff j
      = (qBinom (Polynomial.X : Polynomial ℤ) n 1).coeff (n - 1 - j) := by
  rw [qBinom_one_coeff, qBinom_one_coeff, if_pos (by omega), if_pos (by omega)]

/-- A sequence `a : ℕ → ℤ` is **unimodal** when it rises weakly to some peak index
`m` and falls weakly thereafter: `a` is nondecreasing on `[0,m]` and nonincreasing
on `[m,∞)`. This is the coefficient-sequence notion appearing in Sylvester's
theorem on the Gaussian binomial coefficients. -/
def UnimodalSeq (a : ℕ → ℤ) : Prop :=
  ∃ m : ℕ, (∀ i j, i ≤ j → j ≤ m → a i ≤ a j) ∧ (∀ i j, m ≤ i → i ≤ j → a j ≤ a i)

/-- **Unimodality of the `k = 1` Gaussian binomial (first Sylvester milestone).**
The coefficient sequence of `[n,1]_q` — the all-ones vector `(1,…,1)` of length
`n` — is unimodal, with peak taken at the top degree `n-1`. Together with
`qBinom_one_coeff_symm` this establishes the `k = 1` case of Sylvester's theorem
(symmetric *and* unimodal) at the level of actual `ℤ`-polynomial coefficients.
Unimodality for general `k` (Sylvester 1878 / Proctor 1982 via sl₂) remains open. -/
theorem qBinom_one_unimodal (n : ℕ) :
    UnimodalSeq (fun j => (qBinom (Polynomial.X : Polynomial ℤ) n 1).coeff j) := by
  refine ⟨n - 1, ?_, ?_⟩ <;> intro i j h1 h2 <;>
    simp only [qBinom_one_coeff] <;> split_ifs <;> omega

end QBinomialCoefficients
