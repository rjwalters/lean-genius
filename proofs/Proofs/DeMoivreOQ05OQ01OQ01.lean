/-
Plancherel / Parseval for the discrete Fourier transform

Source: Open question from the de-moivre gallery family
        (de-moivre-oq-05-oq-01-oq-01)
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry (de-moivre-oq-05-oq-01) established the full **orthogonality
relation** of the `n`-th roots of unity and, as its sharpest corollary, the
*orthonormality of the discrete Fourier characters*:

      ∑_{k<n} exp(2πi·ak/n)·conj(exp(2πi·bk/n))  =  ⎧ n   if a = b
                                                     ⎩ 0   if a ≠ b      (a,b < n).

This file pushes that one structural step further to the **Plancherel /
Parseval theorem**, the energy-preservation law of the DFT.  Define the
(unnormalised) discrete Fourier transform of a sampled signal `x : ℕ → ℂ` by

      x̂(j)  =  ∑_{k<n} x(k)·exp(2πi·jk/n).

Then for any two signals `x, y` (Plancherel, complex bilinear form)

      ∑_{j<n} x̂(j)·conj(ŷ(j))  =  n · ∑_{k<n} x(k)·conj(y(k)),

and taking `y = x` gives **Parseval** in its energy form

      ∑_{j<n} |x̂(j)|²  =  n · ∑_{k<n} |x(k)|².

The transform therefore preserves the ℓ²-energy of a signal up to the scale
factor `n`: the DFT is `√n` times a unitary map.  Mathlib has the unitarity of
the *normalised* Fourier transform on `ZMod n` in the abstract `MeasureTheory`
machinery, but not this elementary explicit-exponential Parseval identity built
directly from roots-of-unity orthogonality, which we supply here.

Proof.  Expand both transforms, exchange the order of summation so the
frequency variable `j` runs innermost, and apply the character orthonormality
`∑_{j<n} exp(2πi·jk/n)·conj(exp(2πi·jl/n)) = n·[k=l]` (which is the parent's
`sum_char_inner` with the time/frequency roles swapped, valid because the kernel
`exp(2πi·jk/n)` is symmetric in `j` and `k`).  The orthonormality collapses the
double time-sum to its diagonal, leaving `n·∑_k x(k)·conj(y(k))`.

Theorems:
1. `char_symm`        — symmetry of the DFT kernel in time/frequency
2. `char_inner`       — character orthonormality, restated for the kernel
3. `freq_orthonormal` — orthonormality summed over the frequency index
4. `dft_add`          — linearity of the discrete Fourier transform
5. `dft_plancherel`   — Plancherel: ∑ x̂·conj ŷ = n·∑ x·conj y
6. `dft_parseval`     — Parseval (energy form): ∑ |x̂|² = n·∑ |x|²
7. `dft_parseval_norm`— Parseval in terms of the complex norm ‖·‖
-/

import Mathlib
import Proofs.DeMoivreOQ05OQ01

open Finset

namespace DeMoivreOQ05OQ01OQ01

/-- The DFT kernel: the sampled character `exp(2πi·jk/n)`.  This is exactly the
summand appearing in the parent's `sum_char_inner`. -/
noncomputable def char (n : ℕ) (j k : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑k / ↑n)

/-- The (unnormalised) **discrete Fourier transform** of a sampled signal
`x : ℕ → ℂ` of length `n`: `x̂(j) = ∑_{k<n} x(k)·exp(2πi·jk/n)`. -/
noncomputable def dft (n : ℕ) (x : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ range n, x k * char n j k

/-- **Symmetry of the DFT kernel.**
The kernel `exp(2πi·jk/n)` is symmetric in the time index `k` and the frequency
index `j`, because the exponent `jk` is.  This is what lets us reuse the
parent's character orthonormality (summed over the *time* index) for the sum
over the *frequency* index. -/
theorem char_symm (n j k : ℕ) : char n j k = char n k j := by
  unfold char
  congr 1
  ring

/-- **Character orthonormality, restated for the kernel.**
Direct repackaging of the parent's `sum_char_inner`: for residues `a, b < n`
the sampled characters `k ↦ char n a k` are orthonormal with squared norm `n`,
`∑_{k<n} char n a k · conj (char n b k) = n·[a=b]`. -/
theorem char_inner {n : ℕ} (hn : 0 < n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    ∑ k ∈ range n, char n a k * (starRingEnd ℂ) (char n b k)
      = if a = b then (n : ℂ) else 0 := by
  unfold char
  exact DeMoivreOQ05OQ01.sum_char_inner hn ha hb

/-- **Orthonormality over the frequency index.**
The same dichotomy with the sum taken over the *frequency* index `j` and the two
*time* indices `k, l` fixed: `∑_{j<n} char n j k · conj (char n j l) = n·[k=l]`.
Obtained from `char_inner` by the kernel symmetry `char_symm`.  This is the form
consumed by the Plancherel computation. -/
theorem freq_orthonormal {n : ℕ} (hn : 0 < n) {k l : ℕ} (hk : k < n) (hl : l < n) :
    ∑ j ∈ range n, char n j k * (starRingEnd ℂ) (char n j l)
      = if k = l then (n : ℂ) else 0 := by
  have hsymm : ∀ j, char n j k * (starRingEnd ℂ) (char n j l)
      = char n k j * (starRingEnd ℂ) (char n l j) := by
    intro j; rw [char_symm n j k, char_symm n j l]
  simp only [hsymm]
  exact char_inner hn hk hl

/-- **Linearity of the DFT.**
The discrete Fourier transform is additive: `(x+y)^ = x̂ + ŷ` pointwise in the
frequency variable. -/
theorem dft_add (n : ℕ) (x y : ℕ → ℂ) (j : ℕ) :
    dft n (fun k => x k + y k) j = dft n x j + dft n y j := by
  unfold dft
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **Plancherel theorem for the DFT.**
The discrete Fourier transform preserves the Hermitian inner product up to the
scale factor `n`:

      ∑_{j<n} x̂(j)·conj(ŷ(j))  =  n · ∑_{k<n} x(k)·conj(y(k)).

Expand both transforms into time sums, push the frequency sum innermost, and the
character orthonormality `freq_orthonormal` collapses the resulting double
time-sum to its diagonal. -/
theorem dft_plancherel (n : ℕ) (hn : 0 < n) (x y : ℕ → ℂ) :
    ∑ j ∈ range n, dft n x j * (starRingEnd ℂ) (dft n y j)
      = (n : ℂ) * ∑ k ∈ range n, x k * (starRingEnd ℂ) (y k) := by
  -- Step 1: each frequency summand is a double sum over the time indices k, l.
  have hterm : ∀ j ∈ range n,
      dft n x j * (starRingEnd ℂ) (dft n y j)
        = ∑ k ∈ range n, ∑ l ∈ range n,
            (x k * (starRingEnd ℂ) (y l)) * (char n j k * (starRingEnd ℂ) (char n j l)) := by
    intro j _
    simp only [dft, map_sum, map_mul]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [Finset.sum_congr rfl hterm]
  -- Step 2: swap the outer frequency sum past the first time sum, so each `k`
  -- block is `∑ j ∑ l (...)`.
  rw [Finset.sum_comm]
  -- Step 3: for each time index `k`, swap `∑ j ∑ l → ∑ l ∑ j`, pull the
  -- (time-only) coefficient out of the frequency sum, apply the orthonormality
  -- dichotomy, and collapse the inner diagonal.
  have hcollapse : ∀ k ∈ range n,
      (∑ j ∈ range n, ∑ l ∈ range n,
        (x k * (starRingEnd ℂ) (y l)) * (char n j k * (starRingEnd ℂ) (char n j l)))
        = (n : ℂ) * (x k * (starRingEnd ℂ) (y k)) := by
    intro k hk
    rw [mem_range] at hk
    rw [Finset.sum_comm]
    have hinner : ∀ l ∈ range n,
        (∑ j ∈ range n,
          (x k * (starRingEnd ℂ) (y l)) * (char n j k * (starRingEnd ℂ) (char n j l)))
          = (x k * (starRingEnd ℂ) (y l)) * (if k = l then (n : ℂ) else 0) := by
      intro l hl
      rw [mem_range] at hl
      rw [← Finset.mul_sum, freq_orthonormal hn hk hl]
    rw [Finset.sum_congr rfl hinner, Finset.sum_eq_single k]
    · rw [if_pos rfl]; ring
    · intro l _ hlk
      rw [if_neg (fun h => hlk h.symm), mul_zero]
    · intro h; exact absurd (mem_range.mpr hk) h
  rw [Finset.sum_congr rfl hcollapse, ← Finset.mul_sum]

/-- **Parseval theorem (energy form).**
Setting `y = x` in Plancherel gives the energy-preservation law: the DFT scales
the squared ℓ²-norm by exactly `n`,

      ∑_{j<n} |x̂(j)|²  =  n · ∑_{k<n} |x(k)|²,

so the discrete Fourier transform is `√n` times a unitary map. -/
theorem dft_parseval (n : ℕ) (hn : 0 < n) (x : ℕ → ℂ) :
    ∑ j ∈ range n, Complex.normSq (dft n x j)
      = (n : ℝ) * ∑ k ∈ range n, Complex.normSq (x k) := by
  have h := dft_plancherel n hn x x
  simp only [Complex.mul_conj] at h
  exact_mod_cast h

/-- **Parseval in terms of the complex norm.**
The same identity written with the Euclidean norm `‖·‖` on `ℂ`, using
`‖z‖² = normSq z`. -/
theorem dft_parseval_norm (n : ℕ) (hn : 0 < n) (x : ℕ → ℂ) :
    ∑ j ∈ range n, ‖dft n x j‖ ^ 2
      = (n : ℝ) * ∑ k ∈ range n, ‖x k‖ ^ 2 := by
  have h := dft_parseval n hn x
  simpa only [Complex.normSq_eq_norm_sq] using h

end DeMoivreOQ05OQ01OQ01
