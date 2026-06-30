import Mathlib

/-
# De Moivre OQ-02 OQ-02 OQ-01: Linearization of the Chebyshev U·U Product

## Open Question

The companion file `DeMoivreOQ02OQ02` proves a U·U *product-to-difference*
identity scaled by `(1 - x²)`:
  2(1 − x²)·U_m·U_n = T_{m−n} − T_{m+n+2}.

Can the product `U_m · U_n` itself be written purely in terms of second-kind
Chebyshev polynomials, with no `T` and no `(1 − x²)` factor?

## Answer: YES — the linearization (product-to-sum) formula

For every `m : ℤ` and `n : ℕ`,
  U_m · U_n = ∑_{k=0}^{n} U_{m + n − 2k}
            = U_{m+n} + U_{m+n−2} + ⋯ + U_{m−n}        (as polynomials in R[X]).

This is the second-kind analogue of the first-kind product-to-sum
  2·T_m·T_n = T_{m+n} + T_{m−n}
but is genuinely a *sum of `min(m,n)+1` terms* rather than two terms.

## Proof Strategy

Let `S(m,n) := ∑_{k=0}^{n} U_{m+n−2k}`.  Two facts give the result:

1. **Sum recurrence** (pure index bookkeeping, no products):
     2·X·S(m, n+1) = S(m, n+2) + S(m, n).
   Distribute `2X` into the sum using `2·X·U_k = U_{k+1} + U_{k−1}`, then realign
   the two telescoped ranges; the boundary terms (both `U_{m−n−2}`) cancel.

2. **Two-step induction on n**, mirroring `U_{n+2} = 2·X·U_{n+1} − U_n`.
   Base `n = 0, 1` are direct; the step uses (1) at index `n+1`.

## Build status

BUILD-PENDING (not yet machine-checked). The proof is written with 0 axioms and
0 sorries, but it has never been successfully compiled: the flip-to-verified build
(#24866) was terminated during the Mathlib cache download, before this file was ever
elaborated. Verify with `docker-build.sh Proofs.DeMoivreOQ02OQ02OQ01` once the build
backend is available, then flip status to verified/original.
Numerically cross-checked by hand (not machine): `U_2·U_2 = U_4+U_2+U_0`,
`U_3·U_1 = U_4+U_2`. Likely-fragile spot to watch on first real build: the boundary
`congr 1` in `Ssum_rec`'s `hB` (the `↑(n+1)` vs `↑n+1` cast on the peeled term).
-/

open Polynomial Polynomial.Chebyshev

namespace DeMoivreOQ02OQ02OQ01

variable {R : Type*} [CommRing R]

/-- The linearization sum `S(m,n) = ∑_{k=0}^{n} U_{m+n−2k}`. -/
noncomputable def Ssum (m : ℤ) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1), U R (m + (n : ℤ) - 2 * (k : ℤ))

/-- `2·X·U_k = U_{k+1} + U_{k-1}`: rearrangement of the U recurrence. -/
private lemma two_X_U (k : ℤ) :
    (2 : R[X]) * X * U R k = U R (k + 1) + U R (k - 1) := by
  have h := U_add_two (R := R) (k - 1)
  simp only [show k - 1 + 1 = k from by ring, show k - 1 + 2 = k + 1 from by ring] at h
  linear_combination -h

/-- Expand `2·X·S(m, n+1)` into a single sum of `U`-pairs over `range (n+2)`. -/
private lemma Ssum_succ_expand (m : ℤ) (n : ℕ) :
    (2 : R[X]) * X * Ssum m (n + 1)
      = ∑ k ∈ Finset.range (n + 2),
          (U R (m + (n : ℤ) + 2 - 2 * (k : ℤ)) + U R (m + (n : ℤ) - 2 * (k : ℤ))) := by
  rw [Ssum, Finset.mul_sum]
  apply Finset.sum_congr (by norm_num)
  intro k _
  rw [two_X_U]
  rw [show m + ((n + 1 : ℕ) : ℤ) - 2 * (k : ℤ) + 1 = m + (n : ℤ) + 2 - 2 * (k : ℤ) from by push_cast; ring,
      show m + ((n + 1 : ℕ) : ℤ) - 2 * (k : ℤ) - 1 = m + (n : ℤ) - 2 * (k : ℤ) from by push_cast; ring]

/-- **Sum recurrence**: `2·X·S(m, n+1) = S(m, n+2) + S(m, n)`.

Pure index manipulation — no Chebyshev products appear. -/
lemma Ssum_rec (m : ℤ) (n : ℕ) :
    (2 : R[X]) * X * Ssum m (n + 1) = Ssum m (n + 2) + Ssum m n := by
  rw [Ssum_succ_expand, Finset.sum_add_distrib]
  -- LHS = (∑_{range(n+2)} A) + (∑_{range(n+2)} B)
  --   A k = U_{m+n+2-2k},  B k = U_{m+n-2k}
  -- Expand the RHS sums, then peel boundary terms with sum_range_succ.
  have hA : Ssum (R := R) m (n + 2)
      = (∑ k ∈ Finset.range (n + 2), U R (m + (n : ℤ) + 2 - 2 * (k : ℤ)))
        + U R (m + (n : ℤ) + 2 - 2 * ((n : ℤ) + 2)) := by
    rw [Ssum, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl; intro k _; congr 1; push_cast; ring
    · congr 1; push_cast; ring
  have hB : (∑ k ∈ Finset.range (n + 2), U R (m + (n : ℤ) - 2 * (k : ℤ)))
      = Ssum (R := R) m n + U R (m + (n : ℤ) - 2 * ((n : ℤ) + 1)) := by
    rw [Ssum, show n + 2 = (n + 1) + 1 from rfl, Finset.sum_range_succ]
    congr 1
  rw [hA, hB]
  -- Boundary terms coincide: A_{n+2} = U_{m-n-2} = B_{n+1}.
  rw [show m + (n : ℤ) + 2 - 2 * ((n : ℤ) + 2) = m + (n : ℤ) - 2 * ((n : ℤ) + 1) from by ring]
  ring

/-- Base value: `S(m, 0) = U_m`. -/
private lemma Ssum_zero (m : ℤ) : Ssum (R := R) m 0 = U R m := by
  rw [Ssum, Finset.sum_range_one]
  congr 1; push_cast; ring

/-- Base value: `S(m, 1) = U_{m+1} + U_{m-1}`. -/
private lemma Ssum_one (m : ℤ) :
    Ssum (R := R) m 1 = U R (m + 1) + U R (m - 1) := by
  rw [Ssum, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show m + ((1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) = m + 1 from by push_cast; ring,
      show m + ((1 : ℕ) : ℤ) - 2 * ((1 : ℕ) : ℤ) = m - 1 from by push_cast; ring]

/-- **Main linearization identity** (polynomial form):
  `U_m · U_n = ∑_{k=0}^{n} U_{m+n−2k}`  in `R[X]`, for `m : ℤ`, `n : ℕ`.

Proved by two-step induction matching the U recurrence. -/
theorem U_mul_U (m : ℤ) (n : ℕ) :
    U R m * U R n = Ssum m n := by
  -- Strengthen to a paired statement to feed the two-step recurrence.
  suffices h : ∀ j : ℕ,
      (U R m * U R (j : ℤ) = Ssum m j) ∧
      (U R m * U R ((j : ℤ) + 1) = Ssum m (j + 1)) from (h n).1
  intro j
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [Ssum_zero, Nat.cast_zero, U_zero, mul_one]
    · rw [show ((0 : ℕ) : ℤ) + 1 = 1 from by norm_num, Ssum_one, U_one]
      linear_combination two_X_U (R := R) m
  | succ i ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨by simpa using h1, ?_⟩
    -- Goal: U_m * U_{(i+1)+1} = S(m, i+2).
    have hrec := U_add_two (R := R) (i : ℤ)   -- U_{i+2} = 2X·U_{i+1} − U_i
    have hS := Ssum_rec (R := R) m i          -- 2X·S(m,i+1) = S(m,i+2) + S(m,i)
    rw [show ((i + 1 : ℕ) : ℤ) + 1 = (i : ℤ) + 2 from by push_cast; ring,
        show (i + 1 : ℕ) + 1 = i + 2 from rfl, hrec]
    -- U_m * (2X·U_{i+1} − U_i) = 2X·S(m,i+1) − S(m,i) = S(m,i+2)
    have e1 : U R m * ((2 : R[X]) * X * U R ((i : ℤ) + 1) - U R (i : ℤ))
        = (2 : R[X]) * X * (U R m * U R ((i : ℤ) + 1)) - U R m * U R (i : ℤ) := by ring
    rw [e1, h1, h0]
    linear_combination hS

end DeMoivreOQ02OQ02OQ01
