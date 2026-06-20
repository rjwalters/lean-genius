/-
Jordan Block Infrastructure: Nilpotent Shift and the Single Jordan Block
(cayley-hamilton-minpoly-oq-02-oq-02-oq-02)

Open Question from cayley-hamilton-minpoly-oq-02-oq-02:
"Formalize Jordan normal form over algebraically closed fields."

Full Jordan normal form (every matrix over an algebraically closed field is
similar to a direct sum of Jordan blocks) is a substantial formalization that
Mathlib does not yet provide. Mathlib *does* provide the two deep ingredients:

  * `Mathlib.LinearAlgebra.JordanChevalley` — the Jordan–Chevalley–Dunford
    decomposition `f = s + n` (semisimple + nilpotent, both polynomials in `f`).
  * Generalized eigenspaces span the whole space over an algebraically closed
    field (`Module.End.iSup_genEigenspace_eq_top`).

What is still missing is the *building block itself*: a clean, reusable Jordan
block `J_n(μ)` together with its spectral invariants. This file supplies that
piece, generalizing the specific 4×4 nilpotent computation in
`CayleyHamiltonMinpolyOQ02OQ02.lean` to an arbitrary size `n`.

## What is proved here (0 axioms, 0 sorries)

Let `N = shift n` be the `n × n` nilpotent shift (ones on the superdiagonal),
i.e. the nilpotent Jordan block `J_n(0)`, and let `J_n(μ) = μ•I + N`.

  * `shift_pow_apply`   : the closed form `(Nᵏ) i j = [j = i + k]` (Iverson).
  * `shift_pow_eq_zero` : `Nⁿ = 0`        (nilpotency).
  * `shift_pow_pred_ne_zero` : `Nⁿ⁻¹ ≠ 0` (the nilpotency order is *exactly* n).
  * `minpoly_shift`     : `minpoly K (J_n(0)) = Xⁿ`.
  * `minpoly_jordanBlock` : `minpoly K (J_n(μ)) = (X - C μ)ⁿ`.

The minimal-polynomial results are what make a Jordan block "the" model for a
single elementary divisor: each block contributes exactly the elementary
divisor `(X - μ)ⁿ`. Assembling blocks into a normal form (and proving the
similarity classification) remains open and is noted at the end of the file.

References:
- Hoffman & Kunze, "Linear Algebra" (1971), Chapter 7
- Horn & Johnson, "Matrix Analysis" (2013), §3.1, §3.2
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

open Matrix Polynomial

namespace JordanBlock

variable {K : Type*} [Field K] [DecidableEq K]

-- ============================================================
-- PART 1: The Nilpotent Shift (Jordan block for eigenvalue 0)
-- ============================================================

/-- The `n × n` nilpotent shift matrix: ones on the superdiagonal, zeros
    elsewhere. This is the Jordan block `J_n(0)`:
    `[[0,1,0,…],[0,0,1,…],…,[0,…,0,1],[0,…,0,0]]`. -/
def shift (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

@[simp] theorem shift_apply (n : ℕ) (i j : Fin n) :
    (shift n : Matrix (Fin n) (Fin n) K) i j =
      if (j : ℕ) = (i : ℕ) + 1 then 1 else 0 := rfl

/-- Closed form for the powers of the shift matrix:
    `(Nᵏ) i j = 1` exactly when `j = i + k` (and `0` otherwise). Because the
    column index `j` lives in `Fin n`, the entry is automatically `0` once
    `i + k ≥ n`, which is the source of nilpotency. -/
theorem shift_pow_apply (n k : ℕ) (i j : Fin n) :
    ((shift n : Matrix (Fin n) (Fin n) K) ^ k) i j =
      if (j : ℕ) = (i : ℕ) + k then 1 else 0 := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Nat.add_zero]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro hc; exact h (Fin.ext hc.symm)
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    by_cases hjk : (j : ℕ) = (i : ℕ) + (k + 1)
    · rw [if_pos hjk]
      have hik : (i : ℕ) + k < n := by have hj := j.isLt; omega
      rw [Finset.sum_eq_single_of_mem (⟨(i : ℕ) + k, hik⟩ : Fin n) (Finset.mem_univ _)]
      · rw [ih i (⟨(i : ℕ) + k, hik⟩ : Fin n)]
        rw [if_pos (rfl : ((⟨(i : ℕ) + k, hik⟩ : Fin n) : ℕ) = (i : ℕ) + k)]
        rw [one_mul, shift_apply]
        rw [if_pos (show (j : ℕ) = (i : ℕ) + k + 1 by omega)]
      · intro b _ hb
        rw [ih i b, if_neg, zero_mul]
        intro hcon
        exact hb (Fin.ext hcon)
    · rw [if_neg hjk]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) = (i : ℕ) + k
      · rw [ih i l, if_pos hl, one_mul, shift_apply]
        rw [if_neg (by intro hcon; apply hjk; omega)]
      · rw [ih i l, if_neg hl, zero_mul]

/-- `Nⁿ = 0`: the shift matrix is nilpotent. Every entry `(Nⁿ) i j` would
    require `j = i + n`, impossible since `j < n ≤ i + n`. -/
theorem shift_pow_eq_zero (n : ℕ) :
    (shift n : Matrix (Fin n) (Fin n) K) ^ n = 0 := by
  ext i j
  rw [shift_pow_apply, Matrix.zero_apply, if_neg]
  intro h
  have := j.isLt
  omega

/-- `Nⁿ⁻¹ ≠ 0`: the nilpotency order is *exactly* `n`. The entry in row `0`,
    column `n-1` equals `1`, witnessing `j = i + (n-1)` with `i = 0`. -/
theorem shift_pow_pred_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (shift n : Matrix (Fin n) (Fin n) K) ^ (n - 1) ≠ 0 := by
  intro h
  have key := shift_pow_apply (K := K) n (n - 1)
    (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
  rw [h, Matrix.zero_apply] at key
  simp at key

-- ============================================================
-- PART 2: Minimal polynomial of the nilpotent block is Xⁿ
-- ============================================================

/-- The minimal polynomial of the nilpotent Jordan block `J_n(0) = shift n`
    is `Xⁿ` (for `n ≥ 1`).

    `Xⁿ` annihilates `N` (since `Nⁿ = 0`), so `minpoly ∣ Xⁿ`; as `X` is prime
    this forces `minpoly = Xʲ` for some `j ≤ n`. If `j < n` then `Nʲ = 0`,
    hence `Nⁿ⁻¹ = Nⁿ⁻¹⁻ʲ · Nʲ = 0`, contradicting `shift_pow_pred_ne_zero`.
    Therefore `j = n`. -/
theorem minpoly_shift (n : ℕ) (hn : 1 ≤ n) :
    minpoly K (shift n : Matrix (Fin n) (Fin n) K) = X ^ n := by
  have h_int := Matrix.isIntegral (R := K) (shift n)
  have h_ann : (Polynomial.aeval (shift n : Matrix (Fin n) (Fin n) K)) (X ^ n : K[X]) = 0 := by
    rw [map_pow, aeval_X, shift_pow_eq_zero]
  have h_dvd : minpoly K (shift n : Matrix (Fin n) (Fin n) K) ∣ X ^ n :=
    minpoly.dvd K _ h_ann
  have h_monic := minpoly.monic h_int
  have hX_prime : Prime (X : K[X]) := Polynomial.prime_X
  rw [dvd_prime_pow hX_prime] at h_dvd
  obtain ⟨j, hj_le, hassoc⟩ := h_dvd
  have heq : minpoly K (shift n : Matrix (Fin n) (Fin n) K) = X ^ j :=
    eq_of_monic_of_associated h_monic (monic_X_pow j) hassoc
  have hj_eq : j = n := by
    rcases lt_or_eq_of_le hj_le with hlt | heqn
    · exfalso
      have hsj : (shift n : Matrix (Fin n) (Fin n) K) ^ j = 0 := by
        have hae := minpoly.aeval K (shift n : Matrix (Fin n) (Fin n) K)
        rw [heq, map_pow, aeval_X] at hae
        exact hae
      have hpred : (shift n : Matrix (Fin n) (Fin n) K) ^ (n - 1) = 0 := by
        calc (shift n : Matrix (Fin n) (Fin n) K) ^ (n - 1)
            = (shift n) ^ (n - 1 - j) * (shift n) ^ j := by
                rw [← pow_add]; congr 1; omega
          _ = (shift n) ^ (n - 1 - j) * 0 := by rw [hsj]
          _ = 0 := mul_zero _
      exact shift_pow_pred_ne_zero n hn hpred
    · exact heqn
  rw [heq, hj_eq]

-- ============================================================
-- PART 3: The general Jordan block J_n(μ) = μ•I + N
-- ============================================================

/-- The Jordan block `J_n(μ)`: eigenvalue `μ` on the diagonal, ones on the
    superdiagonal. Defined as `μ•I + N`, where `μ•I` is realized through the
    algebra map so that `aeval (J_n μ) (C μ) = μ•I` holds definitionally. -/
def jordanBlock (n : ℕ) (μ : K) : Matrix (Fin n) (Fin n) K :=
  algebraMap K (Matrix (Fin n) (Fin n) K) μ + shift n

/-- Evaluating `X - C μ` at the Jordan block recovers the nilpotent part:
    `aeval (J_n μ) (X - C μ) = N`. -/
theorem aeval_jordanBlock_X_sub_C (n : ℕ) (μ : K) :
    (Polynomial.aeval (jordanBlock n μ)) (X - C μ) = shift n := by
  rw [map_sub, aeval_X, aeval_C, jordanBlock]
  abel

/-- `(X - C μ)ⁿ` annihilates `J_n(μ)`, since it evaluates to `Nⁿ = 0`. -/
theorem jordanBlock_sub_pow_eq_zero (n : ℕ) (μ : K) :
    (Polynomial.aeval (jordanBlock n μ)) ((X - C μ) ^ n) = 0 := by
  rw [map_pow, aeval_jordanBlock_X_sub_C, shift_pow_eq_zero]

/-- **The minimal polynomial of the Jordan block** `J_n(μ)` is `(X - C μ)ⁿ`
    (for `n ≥ 1`).

    Same divisor argument as `minpoly_shift`, now with the prime `X - C μ` in
    place of `X`: `minpoly ∣ (X - C μ)ⁿ` forces `minpoly = (X - C μ)ʲ`, and
    `aeval (J_n μ) ((X - C μ)ʲ) = Nʲ`, so `j < n` would give `Nⁿ⁻¹ = 0`,
    contradicting `shift_pow_pred_ne_zero`. Hence `j = n`.

    This is the key fact behind Jordan normal form: a single block contributes
    exactly the elementary divisor `(X - μ)ⁿ`. -/
theorem minpoly_jordanBlock (n : ℕ) (hn : 1 ≤ n) (μ : K) :
    minpoly K (jordanBlock n μ) = (X - C μ) ^ n := by
  have h_int := Matrix.isIntegral (R := K) (jordanBlock n μ)
  have h_ann : (Polynomial.aeval (jordanBlock n μ)) ((X - C μ) ^ n) = 0 :=
    jordanBlock_sub_pow_eq_zero n μ
  have h_dvd : minpoly K (jordanBlock n μ) ∣ (X - C μ) ^ n := minpoly.dvd K _ h_ann
  have h_monic := minpoly.monic h_int
  have hP_prime : Prime (X - C μ : K[X]) := prime_X_sub_C μ
  rw [dvd_prime_pow hP_prime] at h_dvd
  obtain ⟨j, hj_le, hassoc⟩ := h_dvd
  have hmonic_pow : (((X - C μ) ^ j : K[X])).Monic := (monic_X_sub_C μ).pow j
  have heq : minpoly K (jordanBlock n μ) = (X - C μ) ^ j :=
    eq_of_monic_of_associated h_monic hmonic_pow hassoc
  have hj_eq : j = n := by
    rcases lt_or_eq_of_le hj_le with hlt | heqn
    · exfalso
      have hsj : (shift n : Matrix (Fin n) (Fin n) K) ^ j = 0 := by
        have hae := minpoly.aeval K (jordanBlock n μ)
        rw [heq, map_pow, aeval_jordanBlock_X_sub_C] at hae
        exact hae
      have hpred : (shift n : Matrix (Fin n) (Fin n) K) ^ (n - 1) = 0 := by
        calc (shift n : Matrix (Fin n) (Fin n) K) ^ (n - 1)
            = (shift n) ^ (n - 1 - j) * (shift n) ^ j := by
                rw [← pow_add]; congr 1; omega
          _ = (shift n) ^ (n - 1 - j) * 0 := by rw [hsj]
          _ = 0 := mul_zero _
      exact shift_pow_pred_ne_zero n hn hpred
    · exact heqn
  rw [heq, hj_eq]

-- ============================================================
-- PART 4: Summary and Open Work
-- ============================================================

/-
## Summary

This file provides the *single Jordan block* as a first-class object with its
spectral invariants fully verified (0 axioms, 0 sorries):

  * `shift n` is the nilpotent Jordan block `J_n(0)`; its powers have the
    closed form `(Nᵏ) i j = [j = i + k]`, giving `Nⁿ = 0` and `Nⁿ⁻¹ ≠ 0`.
  * `minpoly_shift`        : `minpoly (J_n 0) = Xⁿ`.
  * `jordanBlock n μ = μ•I + N` is the general block `J_n(μ)`.
  * `minpoly_jordanBlock`  : `minpoly (J_n μ) = (X - C μ)ⁿ`.

So each Jordan block contributes exactly the elementary divisor `(X - μ)ⁿ`,
which is precisely the role it plays in the rational/Jordan canonical form.

This generalizes the bespoke 4×4 nilpotent computation in
`CayleyHamiltonMinpolyOQ02OQ02.lean` (where `minpoly = X²` was established for
two specific 4×4 nilpotents) to a Jordan block of arbitrary size and arbitrary
eigenvalue.

## Open Work (toward full Jordan normal form)

1. Characteristic polynomial of a block: `charpoly (J_n μ) = (X - C μ)ⁿ`
   (the block is upper-triangular with constant diagonal `μ`).
2. Block-diagonal assembly: for `M = blockDiagonal (J_{n₁}(μ₁), …)`,
   `charpoly = ∏ (X - C μₖ)^{nₖ}` and `minpoly = lcm` of the block minpolys.
3. Existence: every matrix over an algebraically closed field is similar to a
   block-diagonal sum of Jordan blocks (uses `Module.End.iSup_genEigenspace_eq_top`
   plus a cyclic decomposition of each nilpotent generalized-eigenspace part —
   the latter is the genuinely missing ingredient in Mathlib).
4. Uniqueness / classification: two matrices are similar iff they have the same
   list of elementary divisors (Jordan type). The converse failure is already
   formalized in `CayleyHamiltonMinpolyOQ02OQ02.lean`.
-/

end JordanBlock
