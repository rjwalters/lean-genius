import Mathlib

/-
# De Moivre OQ-01-OQ-01-OQ-01: The Binomial Expansion of sin(nθ) and its Chebyshev-U Connection

## Open Question

This entry answers the **leading open question** posed by the parent entry
`de-moivre-oq-01-oq-01` ("The Binomial Expansion of cos(nθ) and its Chebyshev
Connection"):

> Can the companion `sin(nθ) = sin θ · Σ_j (-1)^j C(n,2j+1) cos^{n-2j-1} θ · sin^{2j} θ`
> expansion be derived the same way (as the *imaginary* part of the binomial
> theorem) and connected to `U_{n-1}`?

The answer is **yes**.  Where the parent extracted the *real* part of
`(cos θ + i sin θ)^n` to obtain `cos(nθ)` and the Chebyshev polynomial `T_n`,
this entry extracts the *imaginary* part to obtain `sin(nθ)` and connects the
explicit odd-index binomial sum to the Chebyshev polynomial of the **second**
kind `U_{n}`.

## Mathematical Content

De Moivre's theorem gives `(cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)`.
Expanding the left side by the binomial theorem and comparing *imaginary* parts,

  `sin(nθ) = Σ_{k=0}^n C(n,k) cos^k θ · sin^{n-k} θ · Im(i^{n-k})`.

Since `Im(i^m) = 0` for even `m` and `Im(i^{2j+1}) = (-1)^j`, only **odd** powers
of `sin` survive, recovering the classical closed form

  `sin(nθ) = Σ_{j} (-1)^j C(n,2j+1) cos^{n-2j-1} θ · sin^{2j+1} θ`
          `= sin θ · Σ_{j} (-1)^j C(n,2j+1) cos^{n-2j-1} θ · sin^{2j} θ`.

The bracketed factor, viewed as a polynomial in `cos θ` after `sin² = 1 - cos²`,
is exactly the Chebyshev polynomial `U_{n-1}(cos θ)`, giving the classical
identity `sin(nθ) = U_{n-1}(cos θ) · sin θ`.

## What is proved here (0 axioms, Mathlib-backed)

* `sin_nsmul_eq_im_pow`   — `sin(nθ) = Im((cos θ + i sin θ)^n)` (imaginary-part extraction).
* `sin_nsmul_binomial_im` — the full binomial expansion with the `Im(i^{n-k})` factor.
* `sin_nsmul_binomial_odd`— the classical `(-1)^j`, odd-index closed form.
* `sin_nsmul_eq_sin_mul`  — the `sin θ` factored form (the shape asked for in the OQ).
* `chebyshev_U_eq_binomial_sum` — the Chebyshev-U polynomial (times `sin θ`) equals the
  explicit odd-index binomial sum, closing the analogy with the parent's `T_n` result.

This is the exact odd-index / imaginary-part mirror of the parent's even-index /
real-part development; the two together give the full real+imaginary decomposition
of De Moivre's theorem in explicit binomial form.
-/

open Polynomial Polynomial.Chebyshev Real Finset

namespace DeMoivreOQ01OQ01OQ01

-- ============================================================
-- PART 1: Imaginary-part extraction from De Moivre
-- ============================================================

/-- The De Moivre base point `cos θ + i sin θ` equals `exp(iθ)`. -/
lemma cos_add_sin_I_eq_exp (θ : ℝ) :
    (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I = Complex.exp (↑θ * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- **Imaginary-part extraction**: `sin(nθ)` is the imaginary part of
`(cos θ + i sin θ)^n`.  This is the precise meaning of "comparing imaginary
parts in De Moivre's theorem". -/
lemma sin_nsmul_eq_im_pow (θ : ℝ) (n : ℕ) :
    Real.sin ((n : ℝ) * θ) = (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ^ n).im := by
  rw [cos_add_sin_I_eq_exp, ← Complex.exp_nat_mul]
  rw [show (↑n * (↑θ * Complex.I) : ℂ) = ↑((n : ℝ) * θ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_im]

-- ============================================================
-- PART 2: The binomial expansion of sin(nθ)
-- ============================================================

/-- **Binomial expansion of sin(nθ)** (imaginary-part form).  Expanding
`(cos θ + i sin θ)^n` by the binomial theorem and taking the imaginary part gives
an explicit polynomial in `cos θ` and `sin θ`.  The factor `Im(i^{n-k})` records
the sign pattern coming from the powers of `i`. -/
theorem sin_nsmul_binomial_im (θ : ℝ) (n : ℕ) :
    Real.sin ((n : ℝ) * θ) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * Real.cos θ ^ k * Real.sin θ ^ (n - k) *
          (Complex.I ^ (n - k)).im := by
  rw [sin_nsmul_eq_im_pow, add_pow, Complex.im_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hcast :
      (Real.cos θ : ℂ) ^ k * ((Real.sin θ : ℂ) * Complex.I) ^ (n - k) * (n.choose k : ℂ)
        = ((Real.cos θ ^ k * Real.sin θ ^ (n - k) * (n.choose k : ℝ) : ℝ) : ℂ) *
            Complex.I ^ (n - k) := by
    rw [mul_pow]; push_cast; ring
  rw [hcast, Complex.im_ofReal_mul]; ring

-- ============================================================
-- PART 3: Parity of Im(iᵐ) and the odd-index closed form
-- ============================================================

/-- `Im(i^m) = 0` when `m` is even. -/
lemma im_I_pow_even {m : ℕ} (hm : Even m) : (Complex.I ^ m).im = 0 := by
  obtain ⟨j, rfl⟩ := hm
  have h : Complex.I ^ (j + j) = (((-1 : ℝ) ^ j : ℝ) : ℂ) := by
    rw [← two_mul, pow_mul, Complex.I_sq]; push_cast; ring
  rw [h, Complex.ofReal_im]

/-- `Im(i^{2j+1}) = (-1)^j`. -/
lemma im_I_pow_two_mul_add_one (j : ℕ) : (Complex.I ^ (2 * j + 1)).im = (-1 : ℝ) ^ j := by
  have h : Complex.I ^ (2 * j + 1) = (((-1 : ℝ) ^ j : ℝ) : ℂ) * Complex.I := by
    rw [pow_add, pow_mul, Complex.I_sq, pow_one]; push_cast; ring
  rw [h, Complex.mul_I_im, Complex.ofReal_re]

/-- **Classical closed form of sin(nθ)**: only odd powers of `sin θ` survive,
with alternating signs.  This is the standard multiple-angle formula
`sin(nθ) = Σ_j (-1)^j C(n,2j+1) cos^{n-2j-1} θ · sin^{2j+1} θ`. -/
theorem sin_nsmul_binomial_odd (θ : ℝ) (n : ℕ) :
    Real.sin ((n : ℝ) * θ) =
      ∑ j ∈ Finset.range ((n + 1) / 2),
        (-1 : ℝ) ^ j * (n.choose (2 * j + 1) : ℝ) *
          Real.cos θ ^ (n - (2 * j + 1)) * Real.sin θ ^ (2 * j + 1) := by
  -- Reflect the index k ↦ n - k so the surviving power is that of `sin`.
  have key : Real.sin ((n : ℝ) * θ)
      = ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * Real.cos θ ^ (n - i) * Real.sin θ ^ i * (Complex.I ^ i).im := by
    rw [sin_nsmul_binomial_im, ← Finset.sum_range_reflect
          (fun k => (n.choose k : ℝ) * Real.cos θ ^ k * Real.sin θ ^ (n - k) *
            (Complex.I ^ (n - k)).im) (n + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hle : i ≤ n := by omega
    have h1 : n + 1 - 1 - i = n - i := by omega
    have h2 : n - (n - i) = i := by omega
    rw [h1, h2, Nat.choose_symm hle]
  -- The odd indices `i = 2j+1` are exactly the image of `range ((n+1)/2)` under `j ↦ 2j+1`.
  have hsub : (Finset.range ((n + 1) / 2)).image (fun j => 2 * j + 1) ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    omega
  -- Even-index terms vanish because `Im(i^i) = 0`.
  have hzero : ∀ i ∈ Finset.range (n + 1),
      i ∉ (Finset.range ((n + 1) / 2)).image (fun j => 2 * j + 1) →
      (n.choose i : ℝ) * Real.cos θ ^ (n - i) * Real.sin θ ^ i * (Complex.I ^ i).im = 0 := by
    intro i hi hni
    rw [Finset.mem_range] at hi
    have heven : Even i := by
      rcases Nat.even_or_odd i with he | ho
      · exact he
      · exfalso
        obtain ⟨j, rfl⟩ := ho
        exact hni (by
          rw [Finset.mem_image]
          exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
    rw [im_I_pow_even heven, mul_zero]
  rw [key, ← Finset.sum_subset hsub hzero,
      Finset.sum_image (fun x _ y _ h => by omega)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [im_I_pow_two_mul_add_one]; ring

-- ============================================================
-- PART 4: The `sin θ` factored form (as requested in the open question)
-- ============================================================

/-- **`sin θ`-factored form.**  Pulling `sin θ` out of every surviving term gives
the shape asked for in the parent entry's open question:
`sin(nθ) = sin θ · Σ_j (-1)^j C(n,2j+1) cos^{n-2j-1} θ · sin^{2j} θ`. -/
theorem sin_nsmul_eq_sin_mul (θ : ℝ) (n : ℕ) :
    Real.sin ((n : ℝ) * θ) =
      Real.sin θ *
        ∑ j ∈ Finset.range ((n + 1) / 2),
          (-1 : ℝ) ^ j * (n.choose (2 * j + 1) : ℝ) *
            Real.cos θ ^ (n - (2 * j + 1)) * Real.sin θ ^ (2 * j) := by
  rw [sin_nsmul_binomial_odd, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

-- ============================================================
-- PART 5: Connection to Chebyshev polynomials of the second kind
-- ============================================================

/-- **Chebyshev-U connection.**  The Chebyshev polynomial of the second kind
`U_n` evaluated at `cos θ`, multiplied by `sin θ`, equals the explicit odd-index
binomial sum for `sin((n+1)θ)`.  This is the second-kind mirror of the parent
entry's first-kind result `binomial_sum = T_n(cos θ)`.

Combined with `sin_nsmul_binomial_odd`, it exhibits `U_n(cos θ) · sin θ` as the
imaginary-part / odd-index counterpart of `T_n(cos θ)`. -/
theorem chebyshev_U_eq_binomial_sum (θ : ℝ) (n : ℕ) :
    (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos θ) * Real.sin θ =
      ∑ j ∈ Finset.range ((n + 1 + 1) / 2),
        (-1 : ℝ) ^ j * ((n + 1).choose (2 * j + 1) : ℝ) *
          Real.cos θ ^ ((n + 1) - (2 * j + 1)) * Real.sin θ ^ (2 * j + 1) := by
  rw [← sin_nsmul_binomial_odd θ (n + 1), Polynomial.Chebyshev.U_real_cos θ (n : ℤ)]
  congr 1
  push_cast
  ring

end DeMoivreOQ01OQ01OQ01
