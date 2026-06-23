/-
Orthogonality of the n-th roots of unity (discrete-Fourier inversion)

Source: Open question from the de-moivre gallery family (de-moivre-oq-05-oq-01)
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry (de-moivre-oq-05) proves the single classical fact that for
`n > 1` the `n` complex `n`-th roots of unity sum to zero, i.e.

      ∑_{k=0}^{n-1} ζ^k = 0.

This is exactly the `j = 1` slice of the full **orthogonality relation** that
underlies the discrete Fourier transform.  If `ζ` is a primitive `n`-th root of
unity then for every integer frequency `j`

      ∑_{k=0}^{n-1} ζ^{jk}  =  ⎧ n   if n ∣ j        (all phases coincide)
                               ⎨
                               ⎩ 0   if n ∤ j        (geometric cancellation).

This is the orthogonality / DFT-inversion identity: the columns of the DFT
matrix are pairwise orthogonal, and a full period of any non-trivial sampling
character sums to zero.  Mathlib records the `j = 1` geometric vanishing
(`IsPrimitiveRoot.geom_sum_eq_zero`) but not the full frequency-indexed
dichotomy; we supply it.

Proof.  Write each term as `ζ^{jk} = (ζ^j)^k`, so the sum is the geometric
series `∑_{k<n} w^k` with ratio `w = ζ^j`.

* If `n ∣ j` then `w = ζ^j = 1` (primitivity), every term is `1`, and the sum
  is `n`.
* If `n ∤ j` then `w = ζ^j ≠ 1` (primitivity again), while `w^n = (ζ^n)^j = 1`.
  The telescoping identity `(∑_{k<n} w^k)·(w − 1) = w^n − 1 = 0` together with
  `w − 1 ≠ 0` in an integral domain forces the sum to vanish.

We prove the relation over any integral domain possessing a primitive root,
then specialise to `ℂ` and to the explicit de Moivre / DFT form
`∑_{k<n} exp(2πi·jk/n)`, and finally recover the parent statement as the
`j = 1` corollary.

Theorems:
1. `sum_pow_eq_ite`              — orthogonality over an integral domain
2. `sum_pow_eq_zero_of_not_dvd`  — the cancellation (off-diagonal) case
3. `sum_complex_pow_eq_ite`      — the ℂ specialisation
4. `sum_exp_orthogonality`       — explicit de Moivre / DFT form
5. `sum_complex_zpow_eq_ite`     — signed-frequency (j : ℤ) orthogonality over ℂ
6. `sum_char_inner`             — orthonormality of the DFT characters (inversion)
7. `sum_geom_eq_zero`            — parent recovery: ∑ ζ^k = 0 for n > 1
-/

import Mathlib

open Finset

namespace DeMoivreOQ05OQ01

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Orthogonality of the roots of unity.**
For a primitive `n`-th root of unity `ζ` (`n > 0`) and any frequency `j`, the
power sum `∑_{k<n} ζ^{jk}` equals `n` when `n ∣ j` and `0` otherwise.  This is
the frequency-indexed generalisation of the parent's `∑_{k<n} ζ^k = 0`: writing
each term as `(ζ^j)^k` turns the sum into a geometric series with ratio `ζ^j`,
which is `1` exactly when `n ∣ j` and otherwise a non-trivial `n`-th root, so the
telescoping `(∑ w^k)(w − 1) = w^n − 1 = 0` collapses it to zero. -/
theorem sum_pow_eq_ite {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (j : ℕ) : ∑ k ∈ range n, ζ ^ (j * k) = if n ∣ j then (n : R) else 0 := by
  have hsplit : ∀ k, ζ ^ (j * k) = (ζ ^ j) ^ k := fun k => by rw [← pow_mul]
  simp only [hsplit]
  split_ifs with h
  · -- `n ∣ j` ⟹ `ζ^j = 1`, every term is `1`, the sum is `n`.
    rw [(hζ.pow_eq_one_iff_dvd j).mpr h]
    simp
  · -- `n ∤ j` ⟹ `ζ^j ≠ 1`, geometric cancellation.
    have hne : ζ ^ j - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro hh
      exact h ((hζ.pow_eq_one_iff_dvd j).mp hh)
    have hxn : (ζ ^ j) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hgs := geom_sum_mul (ζ ^ j) n
    rw [hxn, sub_self] at hgs
    rcases mul_eq_zero.mp hgs with h1 | h2
    · exact h1
    · exact absurd h2 hne

/-- **Off-diagonal cancellation.**
When the frequency `j` is not a multiple of `n`, the orthogonality sum vanishes —
the geometric-series form of the statement that distinct DFT modes are
orthogonal. -/
theorem sum_pow_eq_zero_of_not_dvd {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    {j : ℕ} (h : ¬ n ∣ j) : ∑ k ∈ range n, ζ ^ (j * k) = 0 := by
  rw [sum_pow_eq_ite hζ j, if_neg h]

/-- **The complex orthogonality relation.**
Specialisation of `sum_pow_eq_ite` to `ℂ`, whose canonical primitive `n`-th root
of unity is `exp(2πi/n)`. -/
theorem sum_complex_pow_eq_ite {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∑ k ∈ range n, (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) ^ (j * k)
      = if n ∣ j then (n : ℂ) else 0 :=
  sum_pow_eq_ite (Complex.isPrimitiveRoot_exp n hn.ne') j

/-- **Explicit de Moivre / discrete-Fourier form.**
The `n` sampled phases `exp(2πi·jk/n)`, `k = 0, …, n-1`, of the integer frequency
`j` sum to `n` when `j` is a multiple of `n` (all phases coincide) and to `0`
otherwise (a full period cancels).  This is the identity behind DFT inversion;
the parent's vanishing-sum is the `j = 1` instance. -/
theorem sum_exp_orthogonality {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∑ k ∈ range n, Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑k / ↑n)
      = if n ∣ j then (n : ℂ) else 0 := by
  rw [← sum_complex_pow_eq_ite hn j]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Integer-frequency orthogonality over ℂ.**
The orthogonality relation extends to *signed* frequencies `j : ℤ` (negative
modes), using the integer power `ζ^{jk}` of the primitive root `ζ = exp(2πi/n)`.
The proof is the same geometric collapse, now with `IsPrimitiveRoot`'s integer
divisibility criterion `ζ^j = 1 ↔ (n:ℤ) ∣ j`.  This signed form is what feeds
the orthonormality of the Fourier characters. -/
theorem sum_complex_zpow_eq_ite {n : ℕ} (hn : 0 < n) (j : ℤ) :
    ∑ k ∈ range n, (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) ^ (j * (k : ℤ))
      = if (n : ℤ) ∣ j then (n : ℂ) else 0 := by
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n) with hζdef
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  have hsplit : ∀ k : ℕ, ζ ^ (j * (k : ℤ)) = (ζ ^ j) ^ k := by
    intro k; rw [zpow_mul, zpow_natCast]
  simp only [hsplit]
  split_ifs with h
  · rw [(hprim.zpow_eq_one_iff_dvd j).mpr h]
    simp
  · have hne : ζ ^ j - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro hh
      exact h ((hprim.zpow_eq_one_iff_dvd j).mp hh)
    have hxn : (ζ ^ j) ^ n = 1 := by
      rw [← zpow_natCast (ζ ^ j) n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hprim.pow_eq_one, one_zpow]
    have hgs := geom_sum_mul (ζ ^ j) n
    rw [hxn, sub_self] at hgs
    rcases mul_eq_zero.mp hgs with h1 | h2
    · exact h1
    · exact absurd h2 hne

/-- **Orthonormality of the discrete Fourier characters (DFT inversion).**
For distinct residues `a, b < n` the sampled characters `k ↦ exp(2πi·ak/n)` and
`k ↦ exp(2πi·bk/n)` are orthogonal, and each has squared norm `n`:

      ∑_{k<n} exp(2πi·ak/n) · conj(exp(2πi·bk/n))  =  ⎧ n  if a = b
                                                       ⎩ 0  if a ≠ b.

This is the orthogonality of the rows of the DFT matrix — the identity that
makes the inverse discrete Fourier transform recover Fourier coefficients.  The
product of the two characters telescopes to `ζ^{(a−b)k}` for the signed
frequency `a − b`, and integer-frequency orthogonality gives the dichotomy;
since `|a − b| < n`, `n ∣ (a − b)` happens exactly when `a = b`. -/
theorem sum_char_inner {n : ℕ} (hn : 0 < n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    ∑ k ∈ range n, Complex.exp (2 * ↑Real.pi * Complex.I * ↑a * ↑k / ↑n)
        * (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I * ↑b * ↑k / ↑n))
      = if a = b then (n : ℂ) else 0 := by
  -- Each summand is the single signed mode `ζ^{(a−b)k}`.
  have key : ∀ k : ℕ,
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑a * ↑k / ↑n)
          * (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I * ↑b * ↑k / ↑n))
        = (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) ^ (((a : ℤ) - (b : ℤ)) * (k : ℤ)) := by
    intro k
    rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_int_mul]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_natCast,
      Complex.conj_I]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), sum_complex_zpow_eq_ite hn]
  -- `n ∣ (a − b)` with `|a − b| < n` happens exactly when `a = b`.
  rcases eq_or_ne a b with hab | hab
  · subst hab; simp
  · rw [if_neg hab, if_neg]
    rintro ⟨c, hc⟩
    have hb1 : (n : ℤ) * c < n := by rw [← hc]; omega
    have hb2 : -(n : ℤ) < (n : ℤ) * c := by rw [← hc]; omega
    have hc1 : c < 1 := by nlinarith
    have hc2 : -1 < c := by nlinarith
    have : c = 0 := by omega
    rw [this, mul_zero] at hc
    omega

/-- **Parent recovery.**
For `n > 1` the `n`-th roots of unity sum to zero, `∑_{k<n} ζ^k = 0`: the `j = 1`
case of orthogonality, since `n ∤ 1`.  This is exactly the parent statement
`de-moivre-oq-05`. -/
theorem sum_geom_eq_zero {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) :
    ∑ k ∈ range n, ζ ^ k = 0 := by
  have h := sum_pow_eq_zero_of_not_dvd hζ (j := 1)
    (by rw [Nat.dvd_one]; omega)
  simpa using h

end DeMoivreOQ05OQ01
