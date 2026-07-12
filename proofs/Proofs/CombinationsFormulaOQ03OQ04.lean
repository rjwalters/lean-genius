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
- [ ] OPEN: coefficient unimodality (Sylvester/Proctor) — not attempted here

## Honesty Note
This is the palindromy/symmetry ingredient only. It does NOT prove unimodality,
which is the substantive content of the open question. Full unimodality requires
either an sl₂-action argument or an explicit injection between coefficient levels
and is not formalized here.
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

end QBinomialCoefficients
