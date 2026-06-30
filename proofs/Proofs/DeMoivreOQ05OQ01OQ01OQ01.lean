/-
The normalised unitary discrete Fourier transform preserves the Euclidean norm

Source: Open question from the de-moivre gallery family
        (de-moivre-oq-05-oq-01-oq-01-oq-01)
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry (de-moivre-oq-05-oq-01-oq-01) proved the **Plancherel / Parseval
theorem** for the *unnormalised* discrete Fourier transform

      x̂(j)  =  ∑_{k<n} x(k)·exp(2πi·jk/n),        ∑_{j<n} |x̂(j)|²  =  n · ∑_{k<n} |x(k)|²,

so the bare DFT is `√n` times a unitary map.  This file performs the final
normalisation step requested by the parent's first open question: package the
**normalised** transform

      (Ux)(j)  =  x̂(j) / √n        with kernel   U(j,k) = exp(2πi·jk/n) / √n

and prove that it preserves the Euclidean energy *exactly* — no scale factor —

      ∑_{j<n} |(Ux)(j)|²  =  ∑_{k<n} |x(k)|²,         √(∑_j |(Ux)(j)|²) = √(∑_k |x(k)|²),

and, crucially, **exhibit `U` as a genuine element of the unitary group**: the
`n × n` matrix `U(j,k) = exp(2πi·jk/n)/√n` satisfies `U · Uᴴ = 1`, i.e.
`U ∈ Matrix.unitaryGroup (Fin n) ℂ`.

Proof.  Energy preservation is the parent's Parseval divided by `n`: each
normalised coefficient has `|(Ux)(j)|² = |x̂(j)|² / n`, so summing and using
`∑_j |x̂(j)|² = n·∑_k |x(k)|²` cancels the `n`.  Matrix unitarity is the
*column orthonormality* of the kernel: the `(j,l)` entry of `U·Uᴴ` is
`(1/n)·∑_{k<n} char n j k · conj(char n l k)`, which the parent's character
orthonormality `char_inner` evaluates to `(1/n)·(n·[j=l]) = [j=l]`, exactly the
identity matrix.

Theorems:
1. `udft`                       — the normalised DFT `(Ux)(j) = x̂(j)/√n`
2. `udft_parseval`              — exact energy law: ∑ |Ux|² = ∑ |x|²
3. `udft_norm_preserving`       — the ℓ²-norm form ‖Ux‖ = ‖x‖
4. `dftMatrix`                  — the normalised DFT matrix `U(j,k) = char/√n`
5. `dftMatrix_mem_unitaryGroup` — `U ∈ Matrix.unitaryGroup (Fin n) ℂ`
-/

import Mathlib
import Proofs.DeMoivreOQ05OQ01OQ01

open Finset DeMoivreOQ05OQ01OQ01

namespace DeMoivreOQ05OQ01OQ01OQ01

/-- The **normalised discrete Fourier transform** of a sampled signal
`x : ℕ → ℂ` of length `n`: `(Ux)(j) = x̂(j) / √n`.  Dividing the parent's
`√n`-scaled unitary by `√n` turns the DFT into a genuine isometry. -/
noncomputable def udft (n : ℕ) (x : ℕ → ℂ) (j : ℕ) : ℂ :=
  dft n x j / (Real.sqrt n : ℂ)

/-- **Parseval for the normalised DFT (energy form).**
The normalised transform preserves the squared ℓ²-energy *exactly*:

      ∑_{j<n} |(Ux)(j)|²  =  ∑_{k<n} |x(k)|².

This is the parent's `dft_parseval_norm` (`∑|x̂|² = n·∑|x|²`) divided by the
scale factor `n`. -/
theorem udft_parseval (n : ℕ) (hn : 0 < n) (x : ℕ → ℂ) :
    ∑ j ∈ range n, ‖udft n x j‖ ^ 2 = ∑ k ∈ range n, ‖x k‖ ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (n : ℝ) ≠ 0 := hn'.ne'
  have hden : ‖(Real.sqrt n : ℂ)‖ = Real.sqrt n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have key : ∀ j, ‖udft n x j‖ ^ 2 = ‖dft n x j‖ ^ 2 / n := by
    intro j
    unfold udft
    rw [norm_div, div_pow, hden, Real.sq_sqrt hn'.le]
  simp only [key]
  rw [← Finset.sum_div, dft_parseval_norm n hn x, mul_comm (n : ℝ),
    mul_div_assoc, div_self hnz, mul_one]

/-- **The normalised DFT preserves the Euclidean (ℓ²) norm.**
Taking square roots in `udft_parseval`, the ℓ²-norm of `Ux` equals the ℓ²-norm
of `x`: `‖Ux‖ = ‖x‖`. -/
theorem udft_norm_preserving (n : ℕ) (hn : 0 < n) (x : ℕ → ℂ) :
    Real.sqrt (∑ j ∈ range n, ‖udft n x j‖ ^ 2)
      = Real.sqrt (∑ k ∈ range n, ‖x k‖ ^ 2) := by
  rw [udft_parseval n hn x]

/-- The **normalised DFT matrix** `U(j,k) = exp(2πi·jk/n) / √n`, an `n × n`
complex matrix.  This is the operator implementing `udft` on `Fin n → ℂ`. -/
noncomputable def dftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => char n j k / (Real.sqrt n : ℂ)

/-- **The normalised DFT matrix is unitary.**
`U · Uᴴ = 1`, so `U ∈ Matrix.unitaryGroup (Fin n) ℂ`.  The `(j,l)` entry of
`U·Uᴴ` is `(1/n)∑_{k<n} char n j k · conj(char n l k)`, which the parent's
character orthonormality collapses to `[j=l]` — the identity matrix.  This is the
precise sense in which the discrete Fourier transform "is a unitary map". -/
theorem dftMatrix_mem_unitaryGroup (n : ℕ) (hn : 0 < n) :
    dftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  -- Rewrite each summand `U(j,k)·(Uᴴ)(k,l)` as a fraction over `n`.
  have hterm : ∀ k : Fin n,
      dftMatrix n j k * star (dftMatrix n) k l
        = (char n j k * (starRingEnd ℂ) (char n l k)) / (n : ℂ) := by
    intro k
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    simp only [dftMatrix]
    rw [← starRingEnd_apply, map_div₀, Complex.conj_ofReal, div_mul_div_comm,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hn'.le, Complex.ofReal_natCast]
  simp only [hterm]
  rw [← Finset.sum_div,
    Fin.sum_univ_eq_sum_range
      (fun k => char n j k * (starRingEnd ℂ) (char n l k)) n,
    char_inner hn j.isLt l.isLt]
  by_cases h : j = l
  · subst h
    rw [if_pos rfl, if_pos rfl, div_self hnz]
  · rw [if_neg (fun hc => h (Fin.val_injective hc)), if_neg h, zero_div]

end DeMoivreOQ05OQ01OQ01OQ01
