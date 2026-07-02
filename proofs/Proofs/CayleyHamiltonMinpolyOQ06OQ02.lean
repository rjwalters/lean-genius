import Mathlib

/-
# OQ-06 → OQ-02: Minimal-polynomial degree = size of the largest Jordan block

The parent entry `CayleyHamiltonMinpolyOQ06` shows conjugation preserves the minimal
polynomial (similar matrices are minpoly-invariant).  Its open question asks to
**relate the degree of the minimal polynomial to the size of the largest Jordan
block**.

Over an algebraically closed field the Jordan normal form of an operator is a direct
sum of Jordan blocks `J_{s}(λ)`, and the classical theorem states

  `minpoly = ∏_{λ} (X − λ)^{m(λ)}`,   `m(λ) = size of the largest Jordan block at λ`,

so `deg (minpoly) = ∑_λ m(λ)`.  Mathlib (v4.26.0) has **no** Jordan normal form and no
`jordanBlock` matrix, so the full multi-eigenvalue statement is out of reach without
building that theory (>1000 lines).  What *is* both provable and coordinate-free is the
**single-eigenvalue heart** of the statement, which is exactly the content that ties the
minimal polynomial to a *single* Jordan block size:

> If `x − λ` is nilpotent with nilpotency class `m`, then
> **`minpoly K x = (X − C λ)^m`**, hence **`deg (minpoly K x) = m`**.

For a single Jordan block `J_s(λ)` the difference `J_s(λ) − λ·I` is the nilpotent shift
of nilpotency class `s`, so `m = s`: the degree of the minimal polynomial is *exactly*
the block size.  Taking `λ = 0` gives the pure-nilpotent statement
`minpoly K x = X^{nilpotencyClass x}`, itself absent from Mathlib.

## Proof architecture (no Jordan form, no eigenspace decomposition)

Let `y = x − λ`, nilpotent with `y^m = 0` and `m = nilpotencyClass y` minimal.

1. `(X − C λ)^m` annihilates `x` (`aeval x` of it is `y^m = 0`), so `x` is integral and
   `minpoly K x ∣ (X − C λ)^m`.
2. `X − C λ` is prime in `K[X]`, so a monic divisor of its `m`-th power is `(X − C λ)^d`
   for a unique `d ≤ m` (`dvd_prime_pow` + `eq_of_monic_of_associated`).
3. `aeval x (minpoly K x) = 0` forces `y^d = 0`, and minimality of the nilpotency class
   (`Nat.sInf_le`) gives `m ≤ d`.  Hence `d = m`.

No induction, no coordinates: the whole result descends from `dvd_prime_pow` and the
`sInf`-minimality of the nilpotency class.  The development is uniform in `(K, B)`, so the
matrix case (`B = Matrix n n K`) is a one-line specialisation.

## Axioms: 0 | Sorries: 0
-/

open Polynomial

namespace CayleyHamiltonMinpolyOQ06OQ02

variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

/-! ## Section I: Nilpotent generalized eigenvectors are integral -/

/-- A nilpotent element of a `K`-algebra is integral: `X ^ m` (with `x ^ m = 0`) is a
monic annihilating polynomial. -/
theorem isIntegral_of_isNilpotent {x : B} (hx : IsNilpotent x) : IsIntegral K x := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨X ^ m, monic_X_pow m, ?_⟩
  show (aeval x) (X ^ m) = 0
  rw [map_pow, aeval_X]
  exact hm

/-! ## Section II: The single-eigenvalue minimal polynomial -/

/-- **Minimal polynomial of a single-eigenvalue operator.**  If `x − λ` is nilpotent
with nilpotency class `m`, then `minpoly K x = (X − C λ) ^ m`.  In Jordan-normal-form
language `m` is the size of the largest Jordan block of `x` at the eigenvalue `λ`; this
identifies the minimal polynomial (hence its degree) with that block size. -/
theorem minpoly_eq_X_sub_C_pow (x : B) (l : K)
    (hx : IsNilpotent (x - algebraMap K B l)) :
    minpoly K x = (X - C l) ^ (nilpotencyClass (x - algebraMap K B l)) := by
  set y := x - algebraMap K B l with hy
  have hym : y ^ (nilpotencyClass y) = 0 := pow_nilpotencyClass hx
  -- `(X − C l)^m` annihilates `x`.
  have haeval : (aeval x) ((X - C l) ^ (nilpotencyClass y)) = 0 := by
    rw [map_pow, map_sub, aeval_X, aeval_C]
    exact hym
  -- `x` is integral, and `minpoly K x ∣ (X − C l)^m`.
  have hInt : IsIntegral K x :=
    ⟨(X - C l) ^ (nilpotencyClass y), (monic_X_sub_C l).pow _, haeval⟩
  have hdvd : minpoly K x ∣ (X - C l) ^ (nilpotencyClass y) := minpoly.dvd K x haeval
  -- A monic divisor of `(X − C l)^m` is `(X − C l)^d` for some `d ≤ m`.
  obtain ⟨d, hd_le, hassoc⟩ :=
    (dvd_prime_pow (prime_X_sub_C l) (nilpotencyClass y)).mp hdvd
  have hxd : minpoly K x = (X - C l) ^ d :=
    eq_of_monic_of_associated (minpoly.monic hInt) ((monic_X_sub_C l).pow d) hassoc
  -- `minpoly` annihilates `x`, so `y^d = 0`; minimality of the class gives `m ≤ d`.
  have haevald : y ^ d = 0 := by
    have h0 := minpoly.aeval K x
    rw [hxd, map_pow, map_sub, aeval_X, aeval_C] at h0
    exact h0
  have hmd : nilpotencyClass y ≤ d := Nat.sInf_le haevald
  rw [hxd, le_antisymm hd_le hmd]

/-- **Degree form.**  `deg (minpoly K x)` equals the nilpotency class of `x − λ`, i.e. the
size of the largest Jordan block of `x` at `λ`. -/
theorem natDegree_minpoly_eq (x : B) (l : K)
    (hx : IsNilpotent (x - algebraMap K B l)) :
    (minpoly K x).natDegree = nilpotencyClass (x - algebraMap K B l) := by
  rw [minpoly_eq_X_sub_C_pow x l hx, natDegree_pow, natDegree_X_sub_C, mul_one]

/-! ## Section III: The pure-nilpotent case (`λ = 0`) -/

/-- **Pure nilpotent operator.**  `minpoly K x = X ^ (nilpotencyClass x)`.  (Absent from
Mathlib.)  This is the eigenvalue-`0` Jordan block: the minimal polynomial is `X` raised to
the size of the largest block. -/
theorem minpoly_eq_X_pow (x : B) (hx : IsNilpotent x) :
    minpoly K x = X ^ (nilpotencyClass x) := by
  have h := minpoly_eq_X_sub_C_pow x (0 : K) (by simpa using hx)
  simpa using h

/-- Degree form of the pure-nilpotent case: `deg (minpoly K x) = nilpotencyClass x`. -/
theorem natDegree_minpoly_eq_nilpotencyClass (x : B) (hx : IsNilpotent x) :
    (minpoly K x).natDegree = nilpotencyClass x := by
  rw [minpoly_eq_X_pow x hx, natDegree_X_pow]

/-! ## Section IV: Matrix specialisation -/

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Nilpotent matrix.**  For a nilpotent matrix `M` over a field, `minpoly K M`
is `X` to the nilpotency class of `M`. -/
theorem minpoly_nilpotent_matrix (M : Matrix n n K) (hM : IsNilpotent M) :
    minpoly K M = X ^ (nilpotencyClass M) :=
  minpoly_eq_X_pow M hM

/-- **Nilpotent matrix, degree form.**  The degree of the minimal polynomial of a
nilpotent matrix equals its nilpotency class — equivalently, the size of its largest
Jordan block (the single-eigenvalue content of the classical Jordan theorem, which
Mathlib cannot yet state in full). -/
theorem natDegree_minpoly_nilpotent_matrix (M : Matrix n n K) (hM : IsNilpotent M) :
    (minpoly K M).natDegree = nilpotencyClass M :=
  natDegree_minpoly_eq_nilpotencyClass M hM

/-- **Scalar-plus-nilpotent matrix.**  If `M − λ·I` is nilpotent (single eigenvalue `λ`),
the minimal polynomial is `(X − λ)` to the size of the largest Jordan block. -/
theorem natDegree_minpoly_single_eigenvalue_matrix (M : Matrix n n K) (l : K)
    (hM : IsNilpotent (M - algebraMap K (Matrix n n K) l)) :
    (minpoly K M).natDegree = nilpotencyClass (M - algebraMap K (Matrix n n K) l) :=
  natDegree_minpoly_eq M l hM

end Matrix

end CayleyHamiltonMinpolyOQ06OQ02
