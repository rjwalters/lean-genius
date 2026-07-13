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
- [ ] OPEN: coefficient unimodality (Sylvester/Proctor) — not attempted here

## Honesty Note
This is the palindromy/symmetry ingredient plus the structural scaffolding
(degree, monicity, coefficient nonnegativity, pinned extreme coefficients). It does
NOT prove unimodality, which is the substantive content of the open question. Full
unimodality requires either an sl₂-action argument or an explicit injection between
coefficient levels and is not formalized here.

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

end QBinomialCoefficients
