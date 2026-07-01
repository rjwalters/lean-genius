import Mathlib

/-
# De Moivre OQ-01-OQ-01: The Binomial Expansion of cos(nθ) and its Chebyshev Connection

## Open Question

The parent entry (De Moivre OQ-01) establishes the *existence* result
`cos(nθ) = T_n(cos θ)` by quoting Mathlib's `Chebyshev.T_real_cos`.  This entry
supplies the missing *constructive* content: the **explicit binomial expansion**
of `cos(nθ)`, obtained by expanding `(cos θ + i sin θ)^n` with the binomial
theorem and taking the real part, and then proves that this explicit sum equals
the Chebyshev polynomial `T_n(cos θ)`.

## Mathematical Content

De Moivre's theorem gives `(cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)`.
Expanding the left side by the binomial theorem,

  `(cos θ + i sin θ)^n = Σ_{k=0}^n C(n,k) cos^k θ · (i sin θ)^{n-k}`,

and comparing real parts yields

  `cos(nθ) = Σ_{k=0}^n C(n,k) cos^k θ · sin^{n-k} θ · Re(i^{n-k})`.

Since `Re(i^m) = 0` for odd `m` and `Re(i^{2j}) = (-1)^j`, only even powers of
`sin` survive, recovering the classical closed form

  `cos(nθ) = Σ_{j=0}^{⌊n/2⌋} (-1)^j C(n,2j) cos^{n-2j} θ · sin^{2j} θ`.

## What is proved here (0 axioms, Mathlib-backed)

* `cos_nsmul_eq_re_pow` — `cos(nθ) = Re((cos θ + i sin θ)^n)` (real-part extraction).
* `cos_nsmul_binomial_re` — the full binomial expansion with the `Re(i^{n-k})` factor.
* `cos_nsmul_binomial_even` — the classical `(-1)^j`, even-index closed form.
* `binomial_eq_chebyshev_T` — the explicit sum equals `T_n(cos θ)`.
-/

open Polynomial Polynomial.Chebyshev Real Finset

namespace DeMoivreOQ01OQ01

-- ============================================================
-- PART 1: Real-part extraction from De Moivre
-- ============================================================

/-- The De Moivre base point `cos θ + i sin θ` equals `exp(iθ)`. -/
lemma cos_add_sin_I_eq_exp (θ : ℝ) :
    (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I = Complex.exp (↑θ * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- **Real-part extraction**: `cos(nθ)` is the real part of `(cos θ + i sin θ)^n`.
This is the precise meaning of "comparing real parts in De Moivre's theorem". -/
lemma cos_nsmul_eq_re_pow (θ : ℝ) (n : ℕ) :
    Real.cos ((n : ℝ) * θ) = (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ^ n).re := by
  rw [cos_add_sin_I_eq_exp, ← Complex.exp_nat_mul]
  rw [show (↑n * (↑θ * Complex.I) : ℂ) = ↑((n : ℝ) * θ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]

-- ============================================================
-- PART 2: The binomial expansion of cos(nθ)
-- ============================================================

/-- **Binomial expansion of cos(nθ)** (real-part form).  Expanding
`(cos θ + i sin θ)^n` by the binomial theorem and taking the real part gives an
explicit polynomial in `cos θ` and `sin θ`.  The factor `Re(i^{n-k})` records the
sign pattern coming from the powers of `i`. -/
theorem cos_nsmul_binomial_re (θ : ℝ) (n : ℕ) :
    Real.cos ((n : ℝ) * θ) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * Real.cos θ ^ k * Real.sin θ ^ (n - k) *
          (Complex.I ^ (n - k)).re := by
  rw [cos_nsmul_eq_re_pow, add_pow, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hcast :
      (Real.cos θ : ℂ) ^ k * ((Real.sin θ : ℂ) * Complex.I) ^ (n - k) * (n.choose k : ℂ)
        = ((Real.cos θ ^ k * Real.sin θ ^ (n - k) * (n.choose k : ℝ) : ℝ) : ℂ) *
            Complex.I ^ (n - k) := by
    rw [mul_pow]; push_cast; ring
  rw [hcast, Complex.re_ofReal_mul]; ring

-- ============================================================
-- PART 3: Parity of Re(iᵐ) and the even-index closed form
-- ============================================================

/-- `Re(i^m) = 0` when `m` is odd. -/
lemma re_I_pow_odd {m : ℕ} (hm : ¬ Even m) : (Complex.I ^ m).re = 0 := by
  obtain ⟨j, rfl⟩ : Odd m := Nat.not_even_iff_odd.mp hm
  have h : Complex.I ^ (2 * j + 1) = (((-1 : ℝ) ^ j : ℝ) : ℂ) * Complex.I := by
    rw [pow_add, pow_mul, Complex.I_sq, pow_one]; push_cast; ring
  rw [h, Complex.mul_I_re, Complex.ofReal_im, neg_zero]

/-- `Re(i^{2j}) = (-1)^j`. -/
lemma re_I_pow_two_mul (j : ℕ) : (Complex.I ^ (2 * j)).re = (-1 : ℝ) ^ j := by
  have h : Complex.I ^ (2 * j) = (((-1 : ℝ) ^ j : ℝ) : ℂ) := by
    rw [pow_mul, Complex.I_sq]; push_cast; ring
  rw [h, Complex.ofReal_re]

/-- **Classical closed form of cos(nθ)**: only even powers of `sin θ` survive,
with alternating signs.  This is the standard multiple-angle formula
`cos(nθ) = Σ_j (-1)^j C(n,2j) cos^{n-2j} θ · sin^{2j} θ`. -/
theorem cos_nsmul_binomial_even (θ : ℝ) (n : ℕ) :
    Real.cos ((n : ℝ) * θ) =
      ∑ j ∈ Finset.range (n / 2 + 1),
        (-1 : ℝ) ^ j * (n.choose (2 * j) : ℝ) *
          Real.cos θ ^ (n - 2 * j) * Real.sin θ ^ (2 * j) := by
  -- Reflect the index k ↦ n - k so the surviving power is that of `sin`.
  have key : Real.cos ((n : ℝ) * θ)
      = ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * Real.cos θ ^ (n - i) * Real.sin θ ^ i * (Complex.I ^ i).re := by
    rw [cos_nsmul_binomial_re, ← Finset.sum_range_reflect
          (fun k => (n.choose k : ℝ) * Real.cos θ ^ k * Real.sin θ ^ (n - k) *
            (Complex.I ^ (n - k)).re) (n + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hle : i ≤ n := by omega
    have h1 : n + 1 - 1 - i = n - i := by omega
    have h2 : n - (n - i) = i := by omega
    rw [h1, h2, Nat.choose_symm hle]
  -- The even indices `i = 2j` are exactly the image of `range (n/2+1)` under doubling.
  have hsub : (Finset.range (n / 2 + 1)).image (fun j => 2 * j) ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    omega
  -- Odd-index terms vanish because `Re(i^i) = 0`.
  have hzero : ∀ i ∈ Finset.range (n + 1),
      i ∉ (Finset.range (n / 2 + 1)).image (fun j => 2 * j) →
      (n.choose i : ℝ) * Real.cos θ ^ (n - i) * Real.sin θ ^ i * (Complex.I ^ i).re = 0 := by
    intro i hi hni
    rw [Finset.mem_range] at hi
    have hodd : ¬ Even i := by
      rintro ⟨k, rfl⟩
      exact hni (by
        rw [Finset.mem_image]
        exact ⟨k, Finset.mem_range.mpr (by omega), by omega⟩)
    rw [re_I_pow_odd hodd, mul_zero]
  rw [key, ← Finset.sum_subset hsub hzero,
      Finset.sum_image (fun x _ y _ h => by omega)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [re_I_pow_two_mul]; ring

-- ============================================================
-- PART 4: Connection to Chebyshev polynomials
-- ============================================================

/-- **Chebyshev connection**: the explicit binomial sum for `cos(nθ)` equals the
`n`-th Chebyshev polynomial of the first kind evaluated at `cos θ`. -/
theorem binomial_eq_chebyshev_T (θ : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * Real.cos θ ^ k * Real.sin θ ^ (n - k) * (Complex.I ^ (n - k)).re)
      = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (Real.cos θ) := by
  rw [← cos_nsmul_binomial_re, Polynomial.Chebyshev.T_real_cos]
  congr 1

end DeMoivreOQ01OQ01
