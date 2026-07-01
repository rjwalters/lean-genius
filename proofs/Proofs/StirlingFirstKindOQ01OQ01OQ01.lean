import Mathlib
import Proofs.StirlingFirstKindOQ01OQ01

/-
# Signed Stirling numbers, the falling factorial, and Stirling matrix inversion (OQ-01)

## What This Proves

The parent entry `StirlingFirstKindOQ01OQ01` identifies the **unsigned** Stirling numbers of
the first kind `c(n,k) = Nat.stirlingFirst n k` with the coefficients of the **rising**
factorial `ascPochhammer R n`.  This file supplies the three companion facts that turn that
single identity into the classical **duality between the two kinds of Stirling numbers**:

1. **Companion coefficient identity** (`coeff_descPochhammer_eq_stirlingFirst`).  The
   coefficients of the **falling** factorial `descPochhammer R n = x(x-1)⋯(x-n+1)` are the
   **signed** Stirling numbers of the first kind:

       `(descPochhammer R n).coeff k = (-1)^(n+k) · c(n,k)`,   i.e.  `= s(n,k)`.

2. **Second-kind generating identity** (`X_pow_eq_sum_stirlingSecond_descPochhammer`).  The
   monomial `xⁿ` expands in the falling-factorial basis with the Stirling numbers of the
   **second** kind `S(n,k) = Nat.stirlingSecond n k` as coordinates:

       `Xⁿ = ∑_{k=0}^{n} S(n,k) · descPochhammer R k`.

3. **Matrix inversion / orthogonality** (`stirling_orthogonality`).  Substituting (1) into (2)
   and comparing coefficients shows the signed first-kind matrix `[s(n,k)]` and the second-kind
   matrix `[S(n,k)]` are mutually inverse:

       `∑_{k} S(n,k) · s(k,m) = [n = m]`.

4. **Reverse orthogonality / two-sided inverse** (`stirling_orthogonality_reverse`).  The
   *other* product is the identity too, so the two triangles genuinely invert one another on
   both sides:

       `∑_{k} s(n,k) · S(k,m) = [n = m]`.

   The coefficient-comparison in (3) only yields one product; the reverse direction is obtained
   structurally from `Matrix.mul_eq_one_comm` applied to the `(n+1)×(n+1)` truncations (a
   one-sided inverse of a square matrix over a commutative ring is automatically two-sided).

## Context / Mathlib gap

Mathlib defines both `Nat.stirlingFirst` and `Nat.stirlingSecond` with their recurrences, and
both `ascPochhammer` / `descPochhammer`, but connects none of them.  The parent bridged the
unsigned first kind to the rising factorial; this file completes the picture on the falling-
factorial (signed) side and proves the headline structural fact that the two triangular
integer matrices invert one another.

## Approach

(1) is an induction on `n` comparing coefficients through the falling-factorial recurrence
`descPochhammer R (n+1) = descPochhammer R n · (X - n)`, the exact mirror of the parent's
rising-factorial argument; the extra `(X - n)` factor is what introduces the alternating sign,
which we carry as `(-1)^(n+k)` (an addition, avoiding truncated `ℕ`-subtraction).

(2) is an induction on `n` driven by the single engine
`X · descPochhammer R k = descPochhammer R (k+1) + k · descPochhammer R k`
(`X_mul_descPochhammer`); multiplying `Xⁿ = ∑ S(n,k) descPochhammer R k` by `X`, reindexing, and
using the second-kind recurrence `S(n+1,k+1) = S(n,k) + (k+1)·S(n,k+1)` reproduces row `n+1`.

(3) reads off the coefficient of `Xᵐ` in `Xⁿ`, which is `[m = n]`; expanding `Xⁿ` by (2) and each
falling factorial's coefficient by (1) turns the same coefficient into `∑_k S(n,k)·s(k,m)`.

(4) packages (3) as the statement `S · s = 1` for the `(n+1)×(n+1)` matrix truncations (the extra
off-triangle entries vanish), then invokes `Matrix.mul_eq_one_comm` to get `s · S = 1` and reads
off the `(n,m)` entry — the reverse orthogonality that completes the two-sided inverse.

All results are `0`-axiom (kernel-checked, no `sorry`, no `native_decide`).
-/

open Polynomial Finset

namespace StirlingMatrixInversion

variable {R : Type*} [CommRing R]

/-- **Signed first-kind coefficients.**  The coefficients of the falling factorial
`descPochhammer R n = x(x-1)⋯(x-n+1)` are the *signed* Stirling numbers of the first kind
`s(n,k) = (-1)^(n+k) c(n,k)`. -/
theorem coeff_descPochhammer_eq_stirlingFirst (n k : ℕ) :
    (descPochhammer R n).coeff k = (-1) ^ (n + k) * (Nat.stirlingFirst n k : R) := by
  induction n generalizing k with
  | zero =>
    rw [descPochhammer_zero, coeff_one]
    rcases k with _ | k
    · simp
    · simp
  | succ n ih =>
    rw [descPochhammer_succ_right, mul_sub, coeff_sub, ← C_eq_natCast, coeff_mul_C]
    rcases k with _ | m
    · -- constant term
      rw [mul_coeff_zero, coeff_X_zero, mul_zero, zero_sub, ih]
      rcases n with _ | t <;> simp
    · -- coefficient of `Xᵐ⁺¹`: the falling-factorial / Stirling recurrence with a sign
      rw [coeff_mul_X, ih m, ih (m + 1), Nat.stirlingFirst_succ_succ]
      push_cast
      ring

/-- **Multiplication engine.**  Multiplying a falling factorial by `X` shifts it up one and adds
a `k`-multiple of itself: `X · descPochhammer R k = descPochhammer R (k+1) + k · descPochhammer R k`.
This is the falling-factorial analogue of `X·xᵏ = xᵏ⁺¹`, and drives the second-kind expansion. -/
theorem X_mul_descPochhammer (k : ℕ) :
    (X : R[X]) * descPochhammer R k
      = descPochhammer R (k + 1) + (k : R[X]) * descPochhammer R k := by
  rw [descPochhammer_succ_right]
  ring

/-- **Second-kind generating identity (headline).**  The monomial `Xⁿ` expands in the
falling-factorial basis with the Stirling numbers of the second kind as coordinates:
`Xⁿ = ∑_{k=0}^{n} S(n,k) · descPochhammer R k`. -/
theorem X_pow_eq_sum_stirlingSecond_descPochhammer (n : ℕ) :
    (X : R[X]) ^ n
      = ∑ k ∈ range (n + 1), C (Nat.stirlingSecond n k : R) * descPochhammer R k := by
  induction n with
  | zero =>
    rw [pow_zero, Finset.sum_range_one, descPochhammer_zero, mul_one]
    simp
  | succ n ih =>
    -- reindexing fact: `∑ S(n,k)·(k · descPoch k) = ∑ (k+1)·S(n,k+1)·descPoch (k+1)`
    have hB : (∑ k ∈ range (n + 1),
                C (Nat.stirlingSecond n k : R) * ((k : R[X]) * descPochhammer R k))
            = ∑ k ∈ range (n + 1),
                C (((k + 1) * Nat.stirlingSecond n (k + 1) : ℕ) : R)
                  * descPochhammer R (k + 1) := by
      rw [Finset.sum_range_succ' (fun k =>
            C (Nat.stirlingSecond n k : R) * ((k : R[X]) * descPochhammer R k)) n,
          Finset.sum_range_succ (fun k =>
            C (((k + 1) * Nat.stirlingSecond n (k + 1) : ℕ) : R)
              * descPochhammer R (k + 1)) n]
      have hz₁ : Nat.stirlingSecond n (n + 1) = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)
      simp only [Nat.cast_zero, Nat.cast_mul, C_eq_natCast, hz₁, mul_zero,
        map_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [map_mul, C_eq_natCast]
      push_cast
      ring
    calc (X : R[X]) ^ (n + 1)
        = X * ∑ k ∈ range (n + 1), C (Nat.stirlingSecond n k : R) * descPochhammer R k := by
          rw [pow_succ', ih]
      _ = ∑ k ∈ range (n + 1),
            (C (Nat.stirlingSecond n k : R) * descPochhammer R (k + 1)
              + C (Nat.stirlingSecond n k : R) * ((k : R[X]) * descPochhammer R k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← mul_assoc, mul_comm (X : R[X]) (C (Nat.stirlingSecond n k : R)), mul_assoc,
            X_mul_descPochhammer, mul_add]
      _ = (∑ k ∈ range (n + 1), C (Nat.stirlingSecond n k : R) * descPochhammer R (k + 1))
            + ∑ k ∈ range (n + 1),
                C (Nat.stirlingSecond n k : R) * ((k : R[X]) * descPochhammer R k) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ k ∈ range (n + 1 + 1),
            C (Nat.stirlingSecond (n + 1) k : R) * descPochhammer R k := by
          rw [hB, ← Finset.sum_add_distrib,
            Finset.sum_range_succ' (fun k =>
              C (Nat.stirlingSecond (n + 1) k : R) * descPochhammer R k) (n + 1)]
          simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, map_zero, zero_mul, add_zero]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Nat.stirlingSecond_succ_succ]
          simp only [C_eq_natCast]
          push_cast
          ring

/-- **Matrix inversion / orthogonality (headline).**  Substituting the signed first-kind
coefficients (1) into the second-kind expansion (2) and comparing the coefficient of `Xᵐ` on
both sides of `Xⁿ = Xⁿ` shows the two Stirling triangles are mutually inverse:

    `∑_{k=0}^{n} S(n,k) · s(k,m) = [m = n]`,

where `s(k,m) = (-1)^(k+m) c(k,m)` is the signed first-kind entry. -/
theorem stirling_orthogonality (n m : ℕ) :
    (∑ k ∈ range (n + 1),
        (Nat.stirlingSecond n k : R) * ((-1) ^ (k + m) * (Nat.stirlingFirst k m : R)))
      = if m = n then 1 else 0 := by
  rw [← coeff_X_pow n m, X_pow_eq_sum_stirlingSecond_descPochhammer, finset_sum_coeff]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [coeff_C_mul, coeff_descPochhammer_eq_stirlingFirst]

/-- **Reverse matrix inversion / orthogonality (two-sided).**  Companion to
`stirling_orthogonality`, proving the *other* product of the two Stirling triangles is the
identity as well, so `[s(n,k)]` and `[S(n,k)]` are genuinely **mutually inverse**:

    `∑_{k=0}^{n} s(n,k) · S(k,m) = [m = n]`,

where `s(n,k) = (-1)^(n+k) c(n,k)` is the signed first-kind entry.  The coefficient comparison in
`stirling_orthogonality` produces only the product `S · s = I`; here we obtain the reverse
`s · S = I` structurally: for a square matrix over a commutative ring a one-sided inverse is
automatically two-sided (`Matrix.mul_eq_one_comm`), which we apply to the `(n+1)×(n+1)`
truncations of the two triangles. -/
theorem stirling_orthogonality_reverse (n m : ℕ) :
    (∑ k ∈ range (n + 1),
        ((-1) ^ (n + k) * (Nat.stirlingFirst n k : R)) * (Nat.stirlingSecond k m : R))
      = if m = n then 1 else 0 := by
  rcases le_or_gt m n with hmn | hnm
  · -- `m ≤ n`: use the square truncations and `Matrix.mul_eq_one_comm`.
    classical
    set S : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
      Matrix.of (fun i j => (Nat.stirlingSecond i.val j.val : R)) with hSdef
    set s : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
      Matrix.of (fun i j => (-1) ^ (i.val + j.val) * (Nat.stirlingFirst i.val j.val : R)) with hsdef
    -- forward product is the identity — this is exactly `stirling_orthogonality`, extended
    -- from `range (i+1)` to all of `Fin (n+1)` (the extra second-kind entries vanish).
    have hSs : S * s = 1 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.one_apply]
      have hconv :
          (∑ k : Fin (n + 1), S i k * s k j)
            = ∑ k ∈ range (i.val + 1),
                (Nat.stirlingSecond i.val k : R)
                  * ((-1) ^ (k + j.val) * (Nat.stirlingFirst k j.val : R)) := by
        simp only [hSdef, hsdef, Matrix.of_apply]
        rw [Fin.sum_univ_eq_sum_range
              (fun k => (Nat.stirlingSecond i.val k : R)
                * ((-1) ^ (k + j.val) * (Nat.stirlingFirst k j.val : R))) (n + 1)]
        have hsub : range (i.val + 1) ⊆ range (n + 1) := by
          intro x hx; simp only [Finset.mem_range] at hx ⊢; have := i.isLt; omega
        refine (Finset.sum_subset hsub ?_).symm
        intro k _ hk
        have hik : i.val < k := by
          simp only [Finset.mem_range] at hk; omega
        rw [Nat.stirlingSecond_eq_zero_of_lt hik]; simp
      rw [hconv, stirling_orthogonality i.val j.val]
      by_cases hij : i = j
      · subst hij; simp
      · have hji : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
        simp [hji, hij]
    -- hence the reverse product is the identity too
    have hsS : s * S = 1 := Matrix.mul_eq_one_comm.mp hSs
    -- read off entry `(n, m)`
    have key := congrFun (congrFun hsS ⟨n, Nat.lt_succ_self n⟩) ⟨m, by omega⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at key
    simp only [hSdef, hsdef, Matrix.of_apply, Fin.mk.injEq] at key
    rw [Fin.sum_univ_eq_sum_range
          (fun k => (-1) ^ (n + k) * (Nat.stirlingFirst n k : R)
            * (Nat.stirlingSecond k m : R)) (n + 1)] at key
    rw [key]
    rcases eq_or_ne m n with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  · -- `m > n`: every `S(k,m)` with `k ≤ n < m` vanishes, and `m ≠ n`.
    rw [if_neg (by omega : ¬ m = n)]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hkm : k < m := by simp only [Finset.mem_range] at hk; omega
    rw [Nat.stirlingSecond_eq_zero_of_lt hkm]; simp

end StirlingMatrixInversion

