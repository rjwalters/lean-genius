import Mathlib

/-!
# The single Jordan block: nilpotent shift and minimal polynomial

`minpoly-charpoly-oq-01-oq-01` — child of the Jordan-Normal-Form infrastructure
problem `minpoly-charpoly-oq-01` (`Proofs.MinpolyCharpolyOQ01`), whose roadmap
scopes this entry as the *load-bearing spectral API of a single Jordan block*:
the nilpotent-shift power law, its exact nilpotency index, and the minimal
polynomial of a Jordan block.

Mathlib (v4.26.0) has **no** `jordanBlock` matrix and no theorem computing the
minimal polynomial of a Jordan block, so everything here is built from scratch.
The file is deliberately self-contained (it restates the `jordanBlock`
definition rather than importing the parent) so that it verifies independently
of the parent file's build state.

## Main results

* `jordanBlock` — the `d × d` upper Jordan block `λ·I + N` where `N` is the
  strict upper-shift (super-diagonal `1`s).
* `shift_pow_apply` — the closed form for the powers of the shift `N = jordanBlock R 0 d`:
  `(N ^ k) i j = 1` iff `j = i + k` (as naturals), else `0`.  The single fact
  from which both the nilpotency and its sharpness follow.
* `shift_pow_dim_eq_zero` — `N ^ d = 0`  (the shift is nilpotent of index `≤ d`).
* `shift_pow_pred_ne_zero` — `N ^ (d-1) ≠ 0` for `d ≥ 1` over a nontrivial ring
  (the nilpotency index is **exactly** `d`).
* `isNilpotent_shift` — `IsNilpotent N`.
* `jordanBlock_sub_smul_one` — `jordanBlock R λ d - λ • 1 = N` (Jordan–Chevalley
  split of a single block: `A - λI` is the shift).
* `sub_smul_one_pow_dim_eq_zero` — `(A - λ • 1) ^ d = 0`.
* `minpoly_jordanBlock` — over a field, `minpoly K (jordanBlock K λ d) = (X - C λ) ^ d`
  for `d ≥ 1`.  The Jordan block is non-derogatory: its minimal polynomial
  equals its characteristic polynomial.

The minimal-polynomial computation is the mathematically substantive result: the
upper bound `minpoly ∣ (X - C λ)^d` comes from `(A - λI)^d = 0`, primality of
`X - C λ` pins `minpoly = (X - C λ)^m`, and the sharpness `N^(d-1) ≠ 0` forces
`m = d`.
-/

open Matrix Polynomial

namespace MinpolyCharpolyOQ01OQ01

/-- The upper Jordan block `λ · I + N_d`: the `d × d` matrix with `λ` on the
diagonal, `1` on the super-diagonal (positions `(i, i+1)`), and `0` elsewhere.
Restated locally from `Proofs.MinpolyCharpolyOQ01` to keep this file
self-contained. -/
noncomputable def jordanBlock (R : Type*) [CommRing R] (lam : R) (d : Nat) :
    Matrix (Fin d) (Fin d) R :=
  fun i j =>
    if i = j then lam
    else if (j : Nat) = (i : Nat) + 1 then 1 else 0

/-- Entrywise description of the **nilpotent shift** `N = jordanBlock R 0 d`:
the entry `(i, j)` is `1` exactly on the super-diagonal `j = i + 1` and `0`
everywhere else (the diagonal is `0` because the eigenvalue is `0`). -/
theorem shift_apply (R : Type*) [CommRing R] (d : Nat) (i j : Fin d) :
    jordanBlock R 0 d i j = if (j : Nat) = (i : Nat) + 1 then (1 : R) else 0 := by
  unfold jordanBlock
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]

/-- **Power law for the shift.** `(jordanBlock R 0 d) ^ k` has a `1` in position
`(i, j)` precisely when `j = i + k` (as natural numbers), and `0` elsewhere.
Every power just moves the band of `1`s one step further up the diagonal, which
is the engine behind both nilpotency (`k = d` pushes the band off the matrix)
and its sharpness (`k = d - 1` keeps a single `1` in the top-right corner). -/
theorem shift_pow_apply (R : Type*) [CommRing R] (d : Nat) :
    ∀ (k : Nat) (i j : Fin d),
      (jordanBlock R 0 d ^ k) i j = if (j : Nat) = (i : Nat) + k then (1 : R) else 0 := by
  intro k
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply, Nat.add_zero]
    by_cases h : (j : Nat) = (i : Nat)
    · rw [if_pos (Fin.ext h.symm), if_pos h]
    · rw [if_neg (fun he => h (Fin.ext_iff.mp he).symm), if_neg h]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    by_cases hj0 : (j : Nat) = 0
    · rw [if_neg (by omega)]
      apply Finset.sum_eq_zero
      intro l _
      rw [shift_apply, if_neg (by omega), mul_zero]
    · have hmd : (j : Nat) - 1 < d := by have := j.isLt; omega
      set l₀ : Fin d := ⟨(j : Nat) - 1, hmd⟩ with hl0
      rw [Finset.sum_eq_single_of_mem l₀ (Finset.mem_univ l₀)]
      · rw [ih i l₀, shift_apply]
        have hjl : (j : Nat) = ((l₀ : Nat) + 1) := by simp only [hl0]; omega
        rw [if_pos hjl, mul_one]
        by_cases hc : (l₀ : Nat) = (i : Nat) + k
        · rw [if_pos hc, if_pos (by simp only [hl0] at hc ⊢; omega)]
        · rw [if_neg hc, if_neg (by simp only [hl0] at hc ⊢; omega)]
      · intro b _ hb
        rw [shift_apply, if_neg, mul_zero]
        intro hcontra
        exact hb (Fin.ext (by simp only [hl0]; omega))

/-- **The shift is nilpotent of index at most `d`:** `(jordanBlock R 0 d) ^ d = 0`.
By `shift_pow_apply` the `d`-th power would put its band of `1`s on positions
`j = i + d`, but `j < d ≤ i + d`, so every entry vanishes. -/
theorem shift_pow_dim_eq_zero (R : Type*) [CommRing R] (d : Nat) :
    jordanBlock R 0 d ^ d = 0 := by
  ext i j
  rw [shift_pow_apply, Matrix.zero_apply, if_neg]
  have := j.isLt; omega

/-- **`IsNilpotent` witness** for the shift. -/
theorem isNilpotent_shift (R : Type*) [CommRing R] (d : Nat) :
    IsNilpotent (jordanBlock R 0 d) :=
  ⟨d, shift_pow_dim_eq_zero R d⟩

/-- **Sharpness of the nilpotency index:** over a nontrivial ring and for
`d ≥ 1`, `(jordanBlock R 0 d) ^ (d-1) ≠ 0`.  Its `(0, d-1)` entry is `1` (the
band of `1`s from `shift_pow_apply` sits in the top-right corner), so the power
is nonzero.  Combined with `shift_pow_dim_eq_zero` this shows the nilpotency
index is *exactly* `d`. -/
theorem shift_pow_pred_ne_zero (R : Type*) [CommRing R] [Nontrivial R] (d : Nat)
    (hd : 1 ≤ d) :
    jordanBlock R 0 d ^ (d - 1) ≠ 0 := by
  intro h
  have hd0 : 0 < d := hd
  have hentry : (jordanBlock R 0 d ^ (d - 1)) ⟨0, hd0⟩ ⟨d - 1, by omega⟩ = (1 : R) := by
    rw [shift_pow_apply, if_pos]
    simp
  rw [h, Matrix.zero_apply] at hentry
  exact one_ne_zero hentry.symm

/-- **Jordan–Chevalley split of a single block:** `jordanBlock R λ d - λ • 1`
is the pure nilpotent shift `jordanBlock R 0 d`.  Equivalently `A - λI = N`. -/
theorem jordanBlock_sub_smul_one (R : Type*) [CommRing R] (lam : R) (d : Nat) :
    jordanBlock R lam d - lam • (1 : Matrix (Fin d) (Fin d) R) = jordanBlock R 0 d := by
  ext i j
  simp only [jordanBlock, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hij : i = j
  · simp [hij]
  · by_cases hs : (j : Nat) = (i : Nat) + 1 <;> simp [hij, hs]

/-- `(jordanBlock R λ d - λ • 1) ^ d = 0`: the `d`-th power of `A - λI` vanishes,
because `A - λI` is the nilpotent shift. -/
theorem sub_smul_one_pow_dim_eq_zero (R : Type*) [CommRing R] (lam : R) (d : Nat) :
    (jordanBlock R lam d - lam • (1 : Matrix (Fin d) (Fin d) R)) ^ d = 0 := by
  rw [jordanBlock_sub_smul_one]
  exact shift_pow_dim_eq_zero R d

/-- **Minimal polynomial of a single Jordan block.** Over a field `K` and for
`d ≥ 1`,
`minpoly K (jordanBlock K λ d) = (X - C λ) ^ d`.
The Jordan block is non-derogatory: its minimal polynomial equals its
characteristic polynomial `(X - C λ)^d`.

Proof outline:
* `(A - λI)^d = 0` gives `aeval A ((X - C λ)^d) = 0`, so `minpoly ∣ (X - C λ)^d`.
* `X - C λ` is prime, so `dvd_prime_pow` pins `minpoly = (X - C λ)^m` with `m ≤ d`
  (both monic ⇒ the `Associated` is an equality).
* `minpoly` annihilates `A`, so `(A - λI)^m = N^m = 0`.  If `m < d` then
  `N^(d-1) = N^m · N^(d-1-m) = 0`, contradicting `shift_pow_pred_ne_zero`.
  Hence `m = d`. -/
theorem minpoly_jordanBlock (K : Type*) [Field K] (lam : K) (d : Nat) (hd : 1 ≤ d) :
    minpoly K (jordanBlock K lam d) = (X - C lam) ^ d := by
  set A := jordanBlock K lam d with hA
  -- `(X - C λ)^d` annihilates `A`.
  have hann : (aeval A) ((X - C lam) ^ d) = 0 := by
    rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      hA, jordanBlock_sub_smul_one]
    exact shift_pow_dim_eq_zero K d
  -- Hence `minpoly ∣ (X - C λ)^d`.
  have hdvd : minpoly K A ∣ (X - C lam) ^ d := minpoly.dvd K A hann
  -- `X - C λ` is prime, so the divisor is `(X - C λ)^m` for some `m ≤ d`.
  obtain ⟨m, hmd, hassoc⟩ := (dvd_prime_pow (prime_X_sub_C lam) d).mp hdvd
  have hmonic : (minpoly K A).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral A)
  have hmonic_pow : ((X - C lam) ^ m).Monic := (monic_X_sub_C lam).pow m
  have hmp : minpoly K A = (X - C lam) ^ m :=
    Polynomial.eq_of_monic_of_associated hmonic hmonic_pow hassoc
  -- `minpoly` annihilates `A`, so `N ^ m = 0`.
  have hNm : (jordanBlock K 0 d) ^ m = 0 := by
    have := minpoly.aeval K A
    rw [hmp, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      hA, jordanBlock_sub_smul_one] at this
    exact this
  -- Sharpness forces `m = d`.
  have hmeq : m = d := by
    by_contra hne
    have hmlt : m < d := lt_of_le_of_ne hmd hne
    apply shift_pow_pred_ne_zero K d hd
    have hsplit : d - 1 = m + (d - 1 - m) := by omega
    rw [hsplit, pow_add, hNm, zero_mul]
  rw [hmp, hmeq]

end MinpolyCharpolyOQ01OQ01
