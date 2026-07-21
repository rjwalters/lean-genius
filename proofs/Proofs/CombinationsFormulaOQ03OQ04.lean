import Proofs.CombinationsFormulaOQ03
import Mathlib

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
- [x] Structural facts of the Gaussian *polynomial* `qBinom X n k` over `ℤ[X]`:
      monicity, `natDegree = k(n-k)`, constant term `= 1`, nonnegative coefficients,
      and hence both extreme coefficients pinned to `1`
- [x] A `Unimodal` predicate for integer sequences + API (`noValley` connecting it to
      the target "no `aᵢ₋₁ > aᵢ < aᵢ₊₁`", `unimodal_of_nonincreasing`, `unimodal_const`)
- [x] Coefficient unimodality, `k ≤ 1` base cases (`qBinomCoeff_unimodal_{zero,one}`):
      `[n,0]_q = 1` gives `1,0,0,…` and `[n,1]_q = [n]_q` gives `1,…,1,0,…`, both
      non-increasing hence unimodal; via the `k = 1` coefficient bridge `qBinom_X_coeff_one_seq`
- [x] Coefficient unimodality, `k = 2` case (`qBinomCoeff_unimodal_two`) — the first genuine
      rise-then-fall bump: degree `2(n-2)` is even, first half is the ramp `⌊j/2⌋+1`
      (`qBinom_X_two_coeff_le`, from the recurrence `qBinom_X_two_coeff_succ`), and unimodality
      follows from the reusable criterion `unimodal_of_even_palindrome_first_half_mono`
- [ ] OPEN: coefficient unimodality for general `k ≥ 3` (Sylvester/Proctor) — the substantive crux

## Honesty Note
This is the palindromy/symmetry ingredient plus the structural scaffolding
(degree, monicity, coefficient nonnegativity, pinned extreme coefficients) AND the first
unimodality content: the `Unimodal` predicate/API, the `k ≤ 1` base cases, and the `k = 2`
case (the first genuinely rise-then-fall coefficient array). It does NOT prove unimodality
for general `k ≥ 3`, which is the substantive content of the open question: that requires
either an sl₂-action argument or O'Hara's combinatorial decomposition, not attempted here.

## Gaussian polynomial layer (over `ℤ[X]`)
The palindromy above lives over a field (it uses `q⁻¹`). To reason about the actual
*coefficient array* of `[n,k]_q` we specialise the ambient ring to `ℤ[X]` with `q = X`,
so `qBinom X n k : ℤ[X]` is the Gaussian polynomial. By induction on the q-Pascal
recurrence `qBinom X (n+1)(k+1) = qBinom X n k + X^{k+1}·qBinom X n (k+1)` we prove it is
monic of degree `k(n-k)` with constant term `1` and nonnegative coefficients. In the
recurrence the `X^{k+1}`-shifted summand strictly dominates in degree (since `n-k ≥ 1`),
which supplies both the degree and the leading coefficient. Together with the palindromy
`qBinom_reciprocal`, the pinned extreme coefficients are the structural precursor of the
symmetric-unimodal shape asserted by Sylvester's theorem.
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
    rcases (show k + 1 ≤ n ∨ n < k + 1 from by omega) with hkn | hkn
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

/-! ## The Gaussian polynomial over `ℤ[X]`: degree, monicity, coefficients

Specialising the ambient ring to `ℤ[X]` with `q = X` turns `qBinom X n k` into the
Gaussian polynomial whose coefficient sequence is the object of Sylvester's unimodality
theorem. The results below establish its structural invariants directly from the q-Pascal
recurrence, needing no field hypothesis (they hold over `ℤ`, an ordered ring, so that
"nonnegative coefficients" is meaningful). -/

open Polynomial in
/-- **Monicity and degree of the Gaussian polynomial.** For `k ≤ n`, the polynomial
`qBinom X n k : ℤ[X]` is monic of `natDegree = k·(n-k)`.

Proof by induction on the q-Pascal recurrence
`qBinom X (n+1)(k+1) = qBinom X n k + X^{k+1}·qBinom X n (k+1)`. On the diagonal (`k = n`)
and the left edge (`k = 0`) the polynomial is `1`. In the interior (`k < n`, so `n-k ≥ 1`)
the shifted summand `X^{k+1}·qBinom X n (k+1)` has degree `(k+1) + (k+1)(n-k-1) = (k+1)(n-k)`,
strictly exceeding `deg (qBinom X n k) = k(n-k)`, so it supplies both the degree and the
(monic) leading term of the sum. -/
theorem qBinom_X_monic_natDegree :
    ∀ (n k : ℕ), k ≤ n →
      (qBinom (X : ℤ[X]) n k).Monic ∧
      (qBinom (X : ℤ[X]) n k).natDegree = k * (n - k)
  | n, 0, _ => by
      rw [qBinom_zero_right]; exact ⟨monic_one, by simp⟩
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
      rcases eq_or_lt_of_le h with heq | hlt
      · have hkn : k = n := by omega
        subst hkn
        rw [qBinom_self]; exact ⟨monic_one, by simp⟩
      · have hk1n : k + 1 ≤ n := by omega
        have hkn : k ≤ n := by omega
        have hnk1 : 1 ≤ n - k := by omega
        obtain ⟨mA, dA⟩ := qBinom_X_monic_natDegree n k hkn
        obtain ⟨mB, dB⟩ := qBinom_X_monic_natDegree n (k + 1) hk1n
        rw [qBinom_pascal]
        set A := qBinom (X : ℤ[X]) n k with hAdef
        set B := qBinom (X : ℤ[X]) n (k + 1) with hBdef
        have hBne : B ≠ 0 := mB.ne_zero
        have hXpow : (X : ℤ[X]) ^ (k + 1) ≠ 0 := pow_ne_zero _ X_ne_zero
        have mP : ((X : ℤ[X]) ^ (k + 1) * B).Monic := (monic_X_pow (k + 1)).mul mB
        obtain ⟨t, ht⟩ : ∃ t, n - k = t + 1 := ⟨n - k - 1, by omega⟩
        have hnk1' : n - (k + 1) = t := by omega
        have dP : ((X : ℤ[X]) ^ (k + 1) * B).natDegree = (k + 1) * (n - k) := by
          rw [natDegree_mul hXpow hBne, natDegree_X_pow, dB, hnk1', ht]; ring
        have hdeglt : A.natDegree < ((X : ℤ[X]) ^ (k + 1) * B).natDegree := by
          rw [dA, dP, ht]; nlinarith
        have hdA : A.degree < ((X : ℤ[X]) ^ (k + 1) * B).degree := degree_lt_degree hdeglt
        refine ⟨?_, ?_⟩
        · rw [add_comm]
          exact mP.add_of_left hdA
        · rw [add_comm,
            natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hdA), dP]
          congr 1
          omega

open Polynomial in
/-- **Constant term is `1`.** For `k ≤ n`, `(qBinom X n k).coeff 0 = 1`. Induction on the
q-Pascal recurrence: the `X^{k+1}`-shifted summand contributes nothing to the constant term
(`k+1 ≥ 1`), leaving the inductive value `1`. -/
theorem qBinom_X_coeff_zero :
    ∀ (n k : ℕ), k ≤ n → (qBinom (X : ℤ[X]) n k).coeff 0 = 1
  | n, 0, _ => by rw [qBinom_zero_right]; simp
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
      rcases eq_or_lt_of_le h with heq | hlt
      · have hkn : k = n := by omega
        subst hkn; rw [qBinom_self]; simp
      · have hkn : k ≤ n := by omega
        rw [qBinom_pascal, coeff_add, mul_comm, coeff_mul_X_pow']
        simp only [Nat.le_zero, Nat.add_one_ne_zero, if_false]
        rw [qBinom_X_coeff_zero n k hkn]; ring

open Polynomial in
/-- **Coefficients are nonnegative.** Every coefficient of `qBinom X n k : ℤ[X]` is `≥ 0`.
Induction on the q-Pascal recurrence: the sum of a polynomial with nonnegative coefficients
and an `X^{k+1}`-shift of one is again coefficientwise nonnegative. -/
theorem qBinom_X_coeff_nonneg :
    ∀ (n k j : ℕ), 0 ≤ (qBinom (X : ℤ[X]) n k).coeff j
  | n, 0, j => by
      rw [qBinom_zero_right]
      rcases eq_or_ne j 0 with rfl | hj
      · simp
      · simp [coeff_one, hj]
  | 0, k + 1, j => by simp
  | n + 1, k + 1, j => by
      rw [qBinom_pascal, coeff_add, mul_comm, coeff_mul_X_pow']
      have h1 := qBinom_X_coeff_nonneg n k j
      have h2 : 0 ≤ (if k + 1 ≤ j then (qBinom (X : ℤ[X]) n (k + 1)).coeff (j - (k + 1)) else 0) := by
        split_ifs with h
        · exact qBinom_X_coeff_nonneg n (k + 1) _
        · exact le_refl 0
      linarith

open Polynomial in
/-- Convenience: the Gaussian polynomial is monic. -/
theorem qBinom_X_monic {n k : ℕ} (h : k ≤ n) : (qBinom (X : ℤ[X]) n k).Monic :=
  (qBinom_X_monic_natDegree n k h).1

open Polynomial in
/-- Convenience: `natDegree (qBinom X n k) = k · (n - k)`. -/
theorem qBinom_X_natDegree {n k : ℕ} (h : k ≤ n) :
    (qBinom (X : ℤ[X]) n k).natDegree = k * (n - k) :=
  (qBinom_X_monic_natDegree n k h).2

open Polynomial in
/-- The top coefficient (at degree `k(n-k)`) is `1`: it is the leading coefficient of the
monic Gaussian polynomial. -/
theorem qBinom_X_coeff_top {n k : ℕ} (h : k ≤ n) :
    (qBinom (X : ℤ[X]) n k).coeff (k * (n - k)) = 1 := by
  have hmon := qBinom_X_monic h
  rw [← qBinom_X_natDegree h]
  exact hmon

open Polynomial in
/-- **Extreme coefficients are pinned to `1`.** For `k ≤ n` both the constant term and the
top coefficient (degree `k(n-k)`) of the Gaussian polynomial equal `1`. Combined with the
coefficient nonnegativity `qBinom_X_coeff_nonneg` and the palindromy `qBinom_reciprocal`,
this pins the two ends of the symmetric coefficient array of `[n,k]_q` — the structural
precursor to Sylvester's unimodality theorem. -/
theorem qBinom_X_extreme_coeffs {n k : ℕ} (h : k ≤ n) :
    (qBinom (X : ℤ[X]) n k).coeff 0 = 1 ∧
    (qBinom (X : ℤ[X]) n k).coeff (k * (n - k)) = 1 :=
  ⟨qBinom_X_coeff_zero n k h, qBinom_X_coeff_top h⟩

/-! ### Coefficient palindromy over `ℤ[X]`

The self-reciprocity `qBinom_reciprocal` lives over a *field* (it divides by `q`).  Its
coefficient-level shadow — that the coefficient array of the Gaussian polynomial reads the same
forwards and backwards — is an integral statement, cleanly captured by `Polynomial.reflect`:
`reflect (k(n-k)) (qBinom X n k) = qBinom X n k`.  We prove it directly over `ℤ[X]`, with no field
hypothesis, by induction on the `q`-Pascal recurrence.  The mechanism mirrors the field proof:
reflecting the **first** Pascal expansion `qBinom X n k + X^{k+1}·qBinom X n (k+1)` term-by-term
(`reflect_add`, `reflect_mul`) turns it into `X^{n-k}·qBinom X n k + qBinom X n (k+1)`, which is
exactly the **second** Pascal expansion `qBinom_pascal'` of the same polynomial.  This is the
rigorous "symmetric" half of Sylvester's symmetric-unimodal theorem; the unimodal half stays open. -/

open Polynomial in
/-- **Coefficient palindromy of the Gaussian polynomial.**  For `k ≤ n`, `qBinom X n k : ℤ[X]` is
its own reflection at its degree `k(n-k)`:

    reflect (k * (n - k)) (qBinom X n k) = qBinom X n k.

Equivalently its coefficient sequence is a palindrome.  This is the integral, coefficient-level
form of the field identity `qBinom_reciprocal`.  Induction on the `q`-Pascal recurrence: reflecting
the first Pascal expansion `A + X^{k+1}·B` gives `X^{n-k}·A + B`, the second Pascal expansion
(`qBinom_pascal'`) of the same polynomial. -/
theorem qBinom_X_reflect :
    ∀ (n k : ℕ), k ≤ n →
      reflect (k * (n - k)) (qBinom (X : ℤ[X]) n k) = qBinom (X : ℤ[X]) n k
  | n, 0, _ => by
      simp only [Nat.zero_mul, qBinom_zero_right]
      rw [show (1 : ℤ[X]) = C 1 * X ^ 0 by simp, reflect_C_mul_X_pow]; simp
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
      rw [show (n + 1) - (k + 1) = n - k from by omega]
      rcases eq_or_lt_of_le h with heq | hlt
      · -- diagonal `k = n`: the polynomial is `1`, degree `0`
        have hkn : k = n := by omega
        subst hkn
        rw [show k - k = 0 from Nat.sub_self k, Nat.mul_zero, qBinom_self]
        rw [show (1 : ℤ[X]) = C 1 * X ^ 0 by simp, reflect_C_mul_X_pow]; simp
      · -- interior `k < n`
        have hk1n : k + 1 ≤ n := by omega
        have hkn : k ≤ n := by omega
        obtain ⟨_, dA⟩ := qBinom_X_monic_natDegree n k hkn
        obtain ⟨_, dB⟩ := qBinom_X_monic_natDegree n (k + 1) hk1n
        have ihA := qBinom_X_reflect n k hkn
        have ihB := qBinom_X_reflect n (k + 1) hk1n
        rw [show n - (k + 1) = n - k - 1 from by omega] at dB ihB
        -- reflect of the first summand `A`: `reflect (k+1)(n-k) A = X^{n-k} · A`
        have hPA : reflect ((k + 1) * (n - k)) (qBinom (X : ℤ[X]) n k)
            = X ^ (n - k) * qBinom (X : ℤ[X]) n k := by
          have hm := reflect_mul (1 : ℤ[X]) (qBinom (X : ℤ[X]) n k)
            (show (1 : ℤ[X]).natDegree ≤ n - k by simp)
            (show (qBinom (X : ℤ[X]) n k).natDegree ≤ k * (n - k) from le_of_eq dA)
          rw [one_mul, ihA] at hm
          rw [show (k + 1) * (n - k) = (n - k) + k * (n - k) from by ring, hm]
          congr 1
          rw [show (1 : ℤ[X]) = X ^ 0 from (pow_zero X).symm, reflect_monomial,
            revAt_le (Nat.zero_le _), Nat.sub_zero]
        -- reflect of the second summand `X^{k+1}·B`: `reflect (k+1)(n-k) (X^{k+1}·B) = B`
        have hPB : reflect ((k + 1) * (n - k))
            ((X : ℤ[X]) ^ (k + 1) * qBinom (X : ℤ[X]) n (k + 1))
            = qBinom (X : ℤ[X]) n (k + 1) := by
          have hm := reflect_mul ((X : ℤ[X]) ^ (k + 1)) (qBinom (X : ℤ[X]) n (k + 1))
            (show ((X : ℤ[X]) ^ (k + 1)).natDegree ≤ k + 1 by rw [natDegree_X_pow])
            (show (qBinom (X : ℤ[X]) n (k + 1)).natDegree ≤ (k + 1) * (n - k - 1)
              from le_of_eq dB)
          rw [ihB] at hm
          rw [show (k + 1) * (n - k) = (k + 1) + (k + 1) * (n - k - 1) from by
                obtain ⟨t, ht⟩ : ∃ t, n - k = t + 1 := ⟨n - k - 1, by omega⟩
                rw [ht, Nat.add_sub_cancel]; ring, hm]
          rw [reflect_monomial, revAt_le (le_refl _), Nat.sub_self, pow_zero, one_mul]
        -- assemble: reflect (first Pascal) = second Pascal
        conv_lhs => rw [qBinom_pascal]
        rw [reflect_add, hPA, hPB, qBinom_pascal' (X : ℤ[X]) n k (by omega)]

open Polynomial in
/-- **Coefficient palindromy, read off coefficients.**  For `k ≤ n`,
`(qBinom X n k).coeff j = (qBinom X n k).coeff (revAt (k(n-k)) j)` for every `j`.  Immediate from
`qBinom_X_reflect` via `coeff_reflect`.  (`revAt (k(n-k)) j = k(n-k) − j` for `j ≤ k(n-k)`, and
`= j` past the degree, where both sides vanish.) -/
theorem qBinom_X_coeff_symm {n k : ℕ} (h : k ≤ n) (j : ℕ) :
    (qBinom (X : ℤ[X]) n k).coeff j
      = (qBinom (X : ℤ[X]) n k).coeff (revAt (k * (n - k)) j) := by
  nth_rewrite 1 [← qBinom_X_reflect n k h]
  rw [coeff_reflect]

open Polynomial in
/-- **Coefficient palindromy in subtraction form.**  For `k ≤ n` and `j ≤ k(n-k)`,
`(qBinom X n k).coeff j = (qBinom X n k).coeff (k(n-k) − j)` — the symmetric coefficient array
`a_j = a_{k(n-k)−j}` of Sylvester's theorem, made concrete over `ℤ[X]`. -/
theorem qBinom_X_coeff_symm' {n k : ℕ} (h : k ≤ n) {j : ℕ} (hj : j ≤ k * (n - k)) :
    (qBinom (X : ℤ[X]) n k).coeff j
      = (qBinom (X : ℤ[X]) n k).coeff (k * (n - k) - j) := by
  rw [qBinom_X_coeff_symm h j, revAt_le hj]

/-! ### Base change: specializing the Gaussian polynomial

The `q`-binomial is assembled purely from the ring operations of the `q`-Pascal recurrence,
so it commutes with any ring homomorphism (`qBinom_map`).  Two instances tie the polynomial
layer above back to scalars: evaluating `qBinom X n k ∈ ℤ[X]` at a point `c` recovers the
scalar `q`-binomial `qBinom c n k` (`qBinom_X_eval`), and at `c = 1` it degenerates to the
ordinary binomial coefficient `C(n,k)` (`qBinom_X_eval_one`) — equivalently, the coefficients
of the Gaussian polynomial sum to `C(n,k)`, the `q = 1` shadow at the root of the whole
`combinations-formula` lineage. -/

/-- **`qBinom` commutes with ring homomorphisms.** For a ring hom `f : A →+* B` and `q : A`,
`f ([n choose k]_q) = [n choose k]_{f q}`.  The `q`-binomial is built solely from `+`, `*`,
`^` via the `q`-Pascal recurrence, so any ring hom carries it through; this is the uniform
base-change statement of which the scalar specialization `qBinom_at_one` and the polynomial
evaluation `qBinom_X_eval` are instances. -/
theorem qBinom_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : A) :
    ∀ n k : ℕ, f (qBinom q n k) = qBinom (f q) n k
  | _, 0 => by rw [qBinom_zero_right, qBinom_zero_right, map_one]
  | 0, _ + 1 => by rw [qBinom_zero_succ, qBinom_zero_succ, map_zero]
  | n + 1, k + 1 => by
    rw [qBinom_pascal, map_add, map_mul, map_pow,
        qBinom_map f q n k, qBinom_map f q n (k + 1), qBinom_pascal]

open Polynomial in
/-- **Evaluation of the Gaussian polynomial recovers the scalar `q`-binomial.**
`([n choose k]_X).eval c = [n choose k]_c` for every `c : ℤ`.  Evaluation at `c` is the ring
hom `evalRingHom c`, so `qBinom_map` turns it into `qBinom (eval c X) n k = qBinom c n k` —
the bridge between the polynomial layer of this file and the scalar `q`-binomials of the
parent. -/
theorem qBinom_X_eval (c : ℤ) (n k : ℕ) :
    (qBinom (X : ℤ[X]) n k).eval c = qBinom c n k := by
  have h := qBinom_map (evalRingHom c) (X : ℤ[X]) n k
  rwa [coe_evalRingHom, eval_X] at h

open Polynomial in
/-- **The Gaussian polynomial degenerates to the ordinary binomial at `q = 1`.**
`([n choose k]_X).eval 1 = C(n,k)`, combining `qBinom_X_eval` at `c = 1` with the scalar
specialization `qBinom_at_one`.  Since a polynomial's value at `1` is the sum of its
coefficients, this says the coefficient sequence of the palindromic Gaussian polynomial
`qBinom X n k` sums to the ordinary combination count `C(n,k)` — the `q = 1` degeneration at
the root of the `combinations-formula` lineage. -/
theorem qBinom_X_eval_one (n k : ℕ) :
    (qBinom (X : ℤ[X]) n k).eval 1 = (Nat.choose n k : ℤ) := by
  rw [qBinom_X_eval, qBinom_at_one]

/-! ### Unimodality: the `Unimodal` predicate and the `k ≤ 1` base cases

The palindromy above is the *symmetric* half of Sylvester's theorem; the *unimodal* half —
that the coefficient array rises weakly to a single peak then falls — is the substantive open
content.  Mathlib has no `Unimodal` predicate for integer sequences, so we introduce one with a
small API and settle the base cases `k = 0` and `k = 1` (Approach C: small-`k` closed forms
first), where the coefficient sequence is explicit.  Both are in fact non-increasing.  The
general `k` case (O'Hara / `𝔰𝔩₂`) stays open. -/

/-- **Unimodal integer sequence.**  `f : ℕ → ℤ` is unimodal when there is a peak index `p`
    below which `f` is weakly increasing and from which `f` is weakly decreasing — the
    standard "rises to a single peak, then falls" shape.  For the finitely-supported
    coefficient sequence of a polynomial this is exactly Sylvester's claim. -/
def Unimodal (f : ℕ → ℤ) : Prop :=
  ∃ p : ℕ, (∀ i, i < p → f i ≤ f (i + 1)) ∧ (∀ i, p ≤ i → f (i + 1) ≤ f i)

/-- **No interior strict valley.**  A unimodal sequence never strictly dips and strictly
    recovers: there is no `i` with `f (i+1) < f i` *and* `f (i+1) < f (i+2)`.  This is the
    problem's stated target form — no index at which `aᵢ₋₁ > aᵢ < aᵢ₊₁`. -/
theorem Unimodal.noValley {f : ℕ → ℤ} (h : Unimodal f) (i : ℕ) :
    ¬ (f (i + 1) < f i ∧ f (i + 1) < f (i + 2)) := by
  obtain ⟨p, hup, hdown⟩ := h
  rintro ⟨h1, h2⟩
  rcases lt_or_ge i p with hi | hi
  · exact absurd (hup i hi) (not_le.mpr h1)
  · exact absurd (hdown (i + 1) (by omega)) (not_le.mpr h2)

/-- A weakly non-increasing sequence is unimodal, with peak at `0`. -/
theorem unimodal_of_nonincreasing {f : ℕ → ℤ} (h : ∀ i, f (i + 1) ≤ f i) :
    Unimodal f :=
  ⟨0, fun _ hi => absurd hi (by omega), fun i _ => h i⟩

/-- A constant sequence is unimodal. -/
theorem unimodal_const (c : ℤ) : Unimodal (fun _ => c) :=
  unimodal_of_nonincreasing (fun _ => le_refl c)

/-- **Palindromic sequences that rise to the midpoint are unimodal (any degree).**
A nonnegative sequence `f` supported on `[0, d]`, palindromic there (`f j = f (d - j)`
for `j ≤ d`), and weakly increasing across the first half (`f j ≤ f (j+1)` whenever
`2j + 2 ≤ d`), is unimodal with peak at `⌊d/2⌋`.  The falling half is recovered from the
rising half by reflecting each interior descending step through the palindrome symmetry;
the single central step of an **odd**-degree array (`d = 2i+1`, where the two middle
coefficients `f i, f (i+1)` are forced equal by palindromy) is discharged directly, and
nonnegativity closes the boundary step past the support (`f (d+1) = 0 ≤ f d`).  This
generalises `unimodal_of_even_palindrome_first_half_mono` to **odd** degrees, and is the
reusable reduction lemma for Sylvester's theorem: for any symmetric coefficient array,
unimodality follows from weak monotonicity of its first half alone. -/
theorem unimodal_of_palindrome_first_half_mono {f : ℕ → ℤ} (d : ℕ)
    (hnonneg : ∀ j, 0 ≤ f j)
    (hsupp : ∀ j, d < j → f j = 0)
    (hpal : ∀ j, j ≤ d → f j = f (d - j))
    (hmono : ∀ j, 2 * j + 2 ≤ d → f j ≤ f (j + 1)) :
    Unimodal f := by
  refine ⟨d / 2, fun i hi => hmono i (by omega), ?_⟩
  intro i hi
  rcases lt_or_ge i d with hlt | hge
  · -- `⌊d/2⌋ ≤ i < d`: reflect the descending step into the rising half
    have h1 : f (i + 1) = f (d - (i + 1)) := hpal (i + 1) (by omega)
    have h2 : f i = f (d - i) := hpal i (by omega)
    rw [h1, h2]
    rcases lt_or_ge d (2 * (d - i - 1) + 2) with hc | hc
    · -- exact centre of an odd array (`d = 2i+1`): the two middle coeffs are equal
      have heq : f i = f (i + 1) := by
        have hp := hpal i (by omega)
        rwa [show d - i = i + 1 from by omega] at hp
      rw [show d - (i + 1) = i from by omega, show d - i = i + 1 from by omega]
      exact le_of_eq heq
    · -- interior descending step ↦ ascending step `f (d-i-1) ≤ f (d-i)`
      have hstep := hmono (d - i - 1) (by omega)
      rw [show d - i - 1 + 1 = d - i from by omega] at hstep
      rw [show d - (i + 1) = d - i - 1 from by omega]
      exact hstep
  · -- `i ≥ d`: past the support, `f (i+1) = 0 ≤ f i`
    have hs1 : f (i + 1) = 0 := hsupp (i + 1) (by omega)
    rw [hs1]; exact hnonneg i

/-- **Even-degree palindromic sequences that rise to the midpoint are unimodal.**
A nonnegative sequence `f` supported on `[0, 2m]`, palindromic there
(`f j = f (2m - j)`), and weakly increasing on the first half (`f j ≤ f (j+1)` for
`j < m`), is unimodal with peak at `m`.  The even-degree specialisation of
`unimodal_of_palindrome_first_half_mono` (`d = 2m`, where `2j+2 ≤ 2m ⇔ j < m`); it is
used below for `k = 2`, where the degree `2(n-2)` is even and the first half is the
explicit ramp `⌊j/2⌋+1`. -/
theorem unimodal_of_even_palindrome_first_half_mono {f : ℕ → ℤ} (m : ℕ)
    (hnonneg : ∀ j, 0 ≤ f j)
    (hsupp : ∀ j, 2 * m < j → f j = 0)
    (hpal : ∀ j, j ≤ 2 * m → f j = f (2 * m - j))
    (hmono : ∀ j, j < m → f j ≤ f (j + 1)) :
    Unimodal f :=
  unimodal_of_palindrome_first_half_mono (2 * m) hnonneg hsupp hpal
    (fun j hj => hmono j (by omega))

/-- **Direct geometric-sum form of the q-number.**  `[n]_q = ∑_{i<n} qⁱ`.  The parent file
    only provides the `(q-1)`-multiplied identity `qNumber_geometric`; this un-multiplied sum
    is what lets us read off polynomial coefficients.  Proof by the defining recurrence
    `[n+1]_q = 1 + q·[n]_q`. -/
theorem qNumber_eq_sum {S : Type*} [CommRing S] (q : S) :
    ∀ n : ℕ, qNumber q n = ∑ i ∈ Finset.range n, q ^ i
  | 0 => by simp
  | n + 1 => by
    rw [qNumber_succ, qNumber_eq_sum q n, Finset.mul_sum, Finset.sum_range_succ',
        pow_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)

open Polynomial in
/-- **Coefficient sequence of `[n choose 1]_q = [n]_q`.**  As `qBinom X n 1 : ℤ[X]` the
    `j`-th coefficient is `1` for `j < n` and `0` otherwise (the indicator of the length-`n`
    prefix) — the `k = 1` coefficient-extraction bridge.  Uses the direct geometric-sum form
    `qNumber_eq_sum` and `coeff_X_pow`. -/
theorem qBinom_X_coeff_one_seq (n j : ℕ) :
    (qBinom (X : ℤ[X]) n 1).coeff j = if j < n then 1 else 0 := by
  rw [qBinom_one_right, qNumber_eq_sum, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq (Finset.range n) j (fun _ => (1 : ℤ))]
  simp [Finset.mem_range]

open Polynomial in
/-- **Sylvester unimodality, `k = 0` case.**  The coefficient sequence of
    `[n choose 0]_q = 1` (namely `1, 0, 0, …`) is unimodal.  Non-increasing: the value at
    `i+1` is `0` (constant polynomial), dominated by the nonnegative value at `i`
    (`qBinom_X_coeff_nonneg`). -/
theorem qBinomCoeff_unimodal_zero (n : ℕ) :
    Unimodal (fun j => (qBinom (X : ℤ[X]) n 0).coeff j) := by
  apply unimodal_of_nonincreasing
  intro i
  have h1 : (qBinom (X : ℤ[X]) n 0).coeff (i + 1) = 0 := by
    rw [qBinom_zero_right, coeff_one]; simp
  rw [h1]
  exact qBinom_X_coeff_nonneg n 0 i

open Polynomial in
/-- **Sylvester unimodality, `k = 1` case.**  The coefficient sequence of
    `[n choose 1]_q = [n]_q` (namely `n` leading ones then zeros, `1, …, 1, 0, 0, …`) is
    unimodal — indeed non-increasing, so the peak sits at `0`. -/
theorem qBinomCoeff_unimodal_one (n : ℕ) :
    Unimodal (fun j => (qBinom (X : ℤ[X]) n 1).coeff j) := by
  apply unimodal_of_nonincreasing
  intro i
  rw [qBinom_X_coeff_one_seq n (i + 1), qBinom_X_coeff_one_seq n i]
  split_ifs <;> omega

/-! ### Unimodality: the `k = 2` case (first genuine rise-then-fall bump)

For `k = 2` the coefficient array of `[n choose 2]_q` is the first that genuinely rises
*and* falls (`k ≤ 1` was non-increasing).  With `n = m + 2` the degree is the even number
`2m`, and the *first half* of the array is the explicit arithmetic ramp

  `(qBinom X (m+2) 2).coeff j = ⌊j/2⌋ + 1`   for `0 ≤ j ≤ m`,

which is manifestly non-decreasing.  Feeding that ramp plus the already-established
coefficient palindromy (`qBinom_X_coeff_symm'`) and nonnegativity (`qBinom_X_coeff_nonneg`)
into `unimodal_of_even_palindrome_first_half_mono` yields unimodality for all `n`.  This
settles Sylvester's theorem for `k = 2` (Approach C: small-`k` closed forms first); the
general `k` case (O'Hara / `𝔰𝔩₂`) stays open. -/

open Polynomial in
/-- **The `k = 2` coefficient recurrence.**  From the `q`-Pascal identity
`[n+1,2]_q = [n,1]_q + q²·[n,2]_q` (`qBinom_pascal` at `k = 1`, with `[n,1]_q = [n]_q`) the
coefficient array of `[n+1 choose 2]_q` is the length-`n` indicator prefix shifted onto the
`q²`-scaled previous array:

  `(qBinom X (n+1) 2).coeff j = [j < n] + [2 ≤ j] · (qBinom X n 2).coeff (j-2)`. -/
theorem qBinom_X_two_coeff_succ (n j : ℕ) :
    (qBinom (X : ℤ[X]) (n + 1) 2).coeff j
      = (if j < n then (1 : ℤ) else 0)
        + (if 2 ≤ j then (qBinom (X : ℤ[X]) n 2).coeff (j - 2) else 0) := by
  have hp : qBinom (X : ℤ[X]) (n + 1) 2
      = qBinom (X : ℤ[X]) n 1 + X ^ 2 * qBinom (X : ℤ[X]) n 2 :=
    qBinom_pascal (X : ℤ[X]) n 1
  rw [hp, coeff_add, mul_comm, coeff_mul_X_pow', qBinom_X_coeff_one_seq]

open Polynomial in
/-- **First-half closed form for `k = 2`: the ramp `⌊j/2⌋+1`.**  For `n = m + 2` and every
`j ≤ m` (the left half of the symmetric array, up to and including the peak),

  `(qBinom X (m+2) 2).coeff j = ⌊j/2⌋ + 1`.

Proof by induction on `m` via the recurrence `qBinom_X_two_coeff_succ`: at `j`, the indicator
`[j < m+2]` fires (since `j ≤ m+1 < m+2`) contributing `1`, and for `j ≥ 2` the shifted term is
the inductive value `⌊(j-2)/2⌋ + 1` at `j-2 ≤ m`; `⌊(j-2)/2⌋ + 1 = ⌊j/2⌋` closes it. -/
theorem qBinom_X_two_coeff_le :
    ∀ (m j : ℕ), j ≤ m →
      (qBinom (X : ℤ[X]) (m + 2) 2).coeff j = ((j / 2 : ℕ) : ℤ) + 1
  | 0, j, hj => by
      have hj0 : j = 0 := by omega
      subst hj0
      have h22 : qBinom (X : ℤ[X]) 2 2 = 1 := qBinom_self (X : ℤ[X]) 2
      rw [show (0 : ℕ) + 2 = 2 from rfl, h22]
      simp
  | m + 1, j, hj => by
      rw [show m + 1 + 2 = (m + 2) + 1 from by omega, qBinom_X_two_coeff_succ,
          if_pos (show j < m + 2 from by omega)]
      rcases lt_or_ge j 2 with hj2 | hj2
      · rw [if_neg (show ¬ 2 ≤ j from by omega)]
        have hd : (j / 2 : ℕ) = 0 := by omega
        rw [hd]; simp
      · rw [if_pos (show 2 ≤ j from by omega),
            qBinom_X_two_coeff_le m (j - 2) (by omega)]
        have hd : (j - 2) / 2 + 1 = j / 2 := by omega
        have hdz : ((j - 2) / 2 : ℤ) + 1 = ((j / 2 : ℕ) : ℤ) := by exact_mod_cast hd
        push_cast at hdz ⊢
        linarith

open Polynomial in
/-- **Sylvester unimodality, `k = 2` case.**  The coefficient sequence of `[n choose 2]_q`
is unimodal for every `n` — the first genuinely rise-then-fall instance of Sylvester's
theorem.  For `n < 2` the polynomial is `0` (a constant sequence); for `n = m + 2` the
degree `2m` is even, the first half is the non-decreasing ramp `⌊j/2⌋+1`
(`qBinom_X_two_coeff_le`), and unimodality follows from the palindrome-plus-rising-half
criterion `unimodal_of_even_palindrome_first_half_mono` together with coefficient
palindromy and nonnegativity. -/
theorem qBinomCoeff_unimodal_two (n : ℕ) :
    Unimodal (fun j => (qBinom (X : ℤ[X]) n 2).coeff j) := by
  rcases lt_or_ge n 2 with hn | hn
  · -- `n < 2`: `[n,2]_q = 0`, a constant (hence unimodal) sequence
    have hz : qBinom (X : ℤ[X]) n 2 = 0 := qBinom_eq_zero_of_lt (X : ℤ[X]) n 2 (by omega)
    simpa [hz] using unimodal_const (0 : ℤ)
  · -- `n = m + 2`: even palindrome with non-decreasing first-half ramp
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    apply unimodal_of_even_palindrome_first_half_mono m
    · -- nonnegativity
      intro j; exact qBinom_X_coeff_nonneg (m + 2) 2 j
    · -- support: `coeff` vanishes past the degree `2m`
      intro j hj
      apply coeff_eq_zero_of_natDegree_lt
      rw [qBinom_X_natDegree (show 2 ≤ m + 2 from by omega)]
      omega
    · -- palindromy `coeff j = coeff (2m - j)`
      intro j hj
      have hsymm := qBinom_X_coeff_symm' (n := m + 2) (k := 2)
        (show (2 : ℕ) ≤ m + 2 from by omega) (j := j) (by omega)
      rw [show 2 * m = 2 * (m + 2 - 2) from by omega]
      exact hsymm
    · -- first half non-decreasing, via the ramp `⌊j/2⌋+1`
      intro j hj
      show (qBinom (X : ℤ[X]) (m + 2) 2).coeff j
        ≤ (qBinom (X : ℤ[X]) (m + 2) 2).coeff (j + 1)
      rw [qBinom_X_two_coeff_le m j (by omega),
          qBinom_X_two_coeff_le m (j + 1) (by omega)]
      have hdiv : (j / 2 : ℕ) ≤ (j + 1) / 2 := Nat.div_le_div_right (Nat.le_succ j)
      have : ((j / 2 : ℕ) : ℤ) ≤ (((j + 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hdiv
      linarith

/-! ### The general reduction: unimodality ⇐ first-half monotonicity (all `n, k`)

Sylvester's theorem for a *fixed* `k` now reduces to a single inequality: the coefficient
array of `[n choose k]_q` is symmetric (`qBinom_X_coeff_symm'`), nonnegative
(`qBinom_X_coeff_nonneg`), and supported on `[0, k(n-k)]` (`qBinom_X_natDegree`), so its
unimodality follows from the general palindrome criterion the *moment* one knows the array
is weakly increasing across its first half.  The lemma below packages the three structural
facts, leaving future `k`-cases to supply only `coeff j ≤ coeff (j+1)` for `2j+2 ≤ k(n-k)`.
This is exactly the shape in which `k = 2` (`qBinomCoeff_unimodal_two`) was proved, and the
`k = 0, 1` cases (non-increasing arrays) are the degenerate instance with an empty first
half. -/

open Polynomial in
/-- **Sylvester's theorem reduces to first-half monotonicity.**  For `k ≤ n`, if the
coefficient sequence of `[n choose k]_q` is weakly increasing across its first half —
`(qBinom X n k).coeff j ≤ (qBinom X n k).coeff (j+1)` whenever `2j + 2 ≤ k(n-k)` — then the
whole sequence is unimodal.  The falling half, the central step, and the tail past the
degree are all supplied by `unimodal_of_palindrome_first_half_mono` from the already-proved
nonnegativity, degree, and palindromy of the Gaussian polynomial.  This is the reusable
reduction: any future proof of Sylvester unimodality for a given `k` need only establish the
first-half inequality. -/
theorem qBinomCoeff_unimodal_of_first_half_mono {n k : ℕ} (h : k ≤ n)
    (hmono : ∀ j, 2 * j + 2 ≤ k * (n - k) →
      (qBinom (X : ℤ[X]) n k).coeff j ≤ (qBinom (X : ℤ[X]) n k).coeff (j + 1)) :
    Unimodal (fun j => (qBinom (X : ℤ[X]) n k).coeff j) := by
  apply unimodal_of_palindrome_first_half_mono (k * (n - k))
  · intro j; exact qBinom_X_coeff_nonneg n k j
  · intro j hj
    apply coeff_eq_zero_of_natDegree_lt
    rw [qBinom_X_natDegree h]; omega
  · intro j hj; exact qBinom_X_coeff_symm' h hj
  · exact hmono

/-! ### Toward `k = 3`: the coefficient recurrence and box-free prefix monotonicity

The general reduction `qBinomCoeff_unimodal_of_first_half_mono` leaves, for each fixed
`k`, exactly the first-half inequality `coeff j ≤ coeff (j+1)` for `2j + 2 ≤ k(n-k)`.  For
`k = 2` the whole first half admits the `n`-independent closed form `⌊j/2⌋+1` because the
box constraint "each part `≤ n-2`" never binds there (`qBinom_X_two_coeff_le`).  For
`k = 3` this breaks: with box `3 × N` (`N = n - 3`, degree `3N`) the constraint binds once
`j > N`, while the first half runs to `j ≈ 3N/2 > N`.  So the first half splits into

* a **box-free prefix** `j ≤ N`, where coefficients equal the unbounded `≤ 3`-part
  partition counts, and
* a **box-binding tail** `N < j ≤ ⌊(3N - 2)/2⌋` — the genuinely hard Sylvester range that
  needs `𝔰𝔩₂`-representation theory (Proctor 1982) or O'Hara's decomposition (1990).

This section supplies the `k = 3` coefficient recurrence and settles the box-free prefix:
the coefficient sequence of `[N+3, 3]_q` is weakly increasing on `j + 1 ≤ N`.  The tail
stays open.

**Why the elementary induction stops at the prefix.**  A naive induction on `n` across the
*whole* first half fails: once `j` passes the `[n,2]` peak the `q`-Pascal increment
`(qBinom X n 2).coeff (j+1) − (qBinom X n 2).coeff j` turns negative, so the shifted
`[n,3]` term would have to *strictly* compensate — precisely the quantitative control an
`𝔰𝔩₂`/O'Hara argument provides and this recurrence does not.  On the prefix `j + 1 ≤ N`
both increments are `≥ 0`, so the induction closes there and only there. -/

open Polynomial in
/-- **The `k = 3` coefficient recurrence.**  From the `q`-Pascal identity
`[n+1,3]_q = [n,2]_q + q³·[n,3]_q` (`qBinom_pascal` at `k = 2`), the coefficient array of
`[n+1 choose 3]_q` is the `[n,2]_q` array plus the `q³`-shifted `[n,3]_q` array:

  `(qBinom X (n+1) 3).coeff j = (qBinom X n 2).coeff j + [3 ≤ j]·(qBinom X n 3).coeff (j-3)`.

The `k = 3` analogue of `qBinom_X_two_coeff_succ`; the reusable engine for any
coefficient-level `k = 3` argument. -/
theorem qBinom_X_three_coeff_succ (n j : ℕ) :
    (qBinom (X : ℤ[X]) (n + 1) 3).coeff j
      = (qBinom (X : ℤ[X]) n 2).coeff j
        + (if 3 ≤ j then (qBinom (X : ℤ[X]) n 3).coeff (j - 3) else 0) := by
  have hp : qBinom (X : ℤ[X]) (n + 1) 3
      = qBinom (X : ℤ[X]) n 2 + X ^ 3 * qBinom (X : ℤ[X]) n 3 :=
    qBinom_pascal (X : ℤ[X]) n 2
  rw [hp, coeff_add, mul_comm, coeff_mul_X_pow']

open Polynomial in
/-- **Box-free prefix monotonicity for `k = 3`.**  With box `3 × N` (`n = N + 3`), the
coefficient sequence of `[N+3 choose 3]_q` is weakly increasing across the prefix
`j + 1 ≤ N`, the range where the constraint "each part `≤ N`" does not yet bind.  Proof by
induction on `N` via `qBinom_X_three_coeff_succ`: the `[n,2]` increment is `≥ 0` on this
prefix (the `k = 2` ramp `⌊j/2⌋+1`, `qBinom_X_two_coeff_le`) and the shifted `[n,3]`
increment is `≥ 0` by the induction hypothesis (or, for `j < 3`, trivially — the left `if`
vanishes and the right coefficient is nonnegative, `qBinom_X_coeff_nonneg`).

This is the *easy* portion of Sylvester's first-half inequality for `k = 3` — the first
`k = 3` monotonicity result formalised.  The box-binding tail `N < j ≤ ⌊(3N - 2)/2⌋`,
where the target's substantive open content lives, is **not** covered here. -/
theorem qBinom_X_three_coeff_prefix_mono :
    ∀ (N j : ℕ), j + 1 ≤ N →
      (qBinom (X : ℤ[X]) (N + 3) 3).coeff j
        ≤ (qBinom (X : ℤ[X]) (N + 3) 3).coeff (j + 1)
  | 0, j, hj => by omega
  | N + 1, j, hj => by
      rw [show N + 1 + 3 = (N + 3) + 1 from by omega,
          qBinom_X_three_coeff_succ (N + 3) j, qBinom_X_three_coeff_succ (N + 3) (j + 1)]
      -- `k = 2` increment ≥ 0 on the prefix, via the ramp `⌊j/2⌋+1`
      have e0 : (qBinom (X : ℤ[X]) (N + 3) 2).coeff j = ((j / 2 : ℕ) : ℤ) + 1 :=
        qBinom_X_two_coeff_le (N + 1) j (by omega)
      have e1 : (qBinom (X : ℤ[X]) (N + 3) 2).coeff (j + 1) = (((j + 1) / 2 : ℕ) : ℤ) + 1 :=
        qBinom_X_two_coeff_le (N + 1) (j + 1) (by omega)
      have hA : (qBinom (X : ℤ[X]) (N + 3) 2).coeff j
          ≤ (qBinom (X : ℤ[X]) (N + 3) 2).coeff (j + 1) := by
        rw [e0, e1]
        have hdiv : (j / 2 : ℕ) ≤ (j + 1) / 2 := Nat.div_le_div_right (Nat.le_succ j)
        have : ((j / 2 : ℕ) : ℤ) ≤ (((j + 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hdiv
        linarith
      -- shifted `k = 3` increment ≥ 0
      have hB : (if 3 ≤ j then (qBinom (X : ℤ[X]) (N + 3) 3).coeff (j - 3) else (0 : ℤ))
          ≤ (if 3 ≤ j + 1 then (qBinom (X : ℤ[X]) (N + 3) 3).coeff (j + 1 - 3) else 0) := by
        rcases lt_or_ge j 3 with hj3 | hj3
        · -- `j < 3`: left `if` is `0`, right side is nonnegative
          rw [if_neg (by omega : ¬ 3 ≤ j)]
          split_ifs
          · exact qBinom_X_coeff_nonneg (N + 3) 3 _
          · exact le_refl 0
        · -- `j ≥ 3`: both `if`s fire; induction hypothesis at index `j - 3`
          rw [if_pos hj3, if_pos (by omega : 3 ≤ j + 1),
              show j + 1 - 3 = (j - 3) + 1 from by omega]
          exact qBinom_X_three_coeff_prefix_mono N (j - 3) (by omega)
      linarith

end QBinomialCoefficients

