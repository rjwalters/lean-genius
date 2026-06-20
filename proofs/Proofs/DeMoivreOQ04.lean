import Mathlib

/-
# De Moivre OQ-04: The n-th Roots of Unity as Powers of ω = cos(2π/n) + i·sin(2π/n)

## Research Problem: de-moivre-oq-04

Use De Moivre's formula to show that

  ω = cos(2π/n) + i·sin(2π/n)

is a primitive n-th root of unity, and that its powers ω⁰, ω¹, …, ωⁿ⁻¹
are *exactly* the n distinct solutions of zⁿ = 1.

## Mathematical Content

De Moivre's formula states that, for every natural number n,

  (cos θ + i·sin θ)ⁿ = cos(nθ) + i·sin(nθ).

Specialising to θ = 2π/n collapses the right-hand side, because
n·(2π/n) = 2π and cos(2π) = 1, sin(2π) = 0:

  ωⁿ = cos(2π) + i·sin(2π) = 1.

So ω is an n-th root of unity, and therefore so is each power ωᵏ.
Identifying ω with the exponential e^{2πi/n} (Euler's formula) shows that ω is
in fact *primitive*: its successive powers are pairwise distinct for
0 ≤ k < n, and together they enumerate the whole solution set of zⁿ = 1.

This file is the trigonometric-form companion to the De Moivre family:
- oq-01 extracts cos nθ / sin nθ from the formula,
- oq-03 handles fractional exponents and root extraction in exponential form,
- **oq-04 (this file)** isolates ω = cos(2π/n)+i·sin(2π/n) as the generator of
  the n-th roots of unity, proving ωⁿ = 1 directly from `cos_add_sin_mul_I_pow`.

## References
- De Moivre (1707): original formula for integer powers
- Euler (1748): exponential form e^{iθ} = cos θ + i·sin θ
- Mathlib: `Complex.cos_add_sin_mul_I_pow`, `Complex.isPrimitiveRoot_exp`
-/

open Complex Real

namespace DeMoivreOQ04

/-- The candidate primitive n-th root of unity, in trigonometric form:
    ω = cos(2π/n) + i·sin(2π/n). -/
noncomputable def omega (n : ℕ) : ℂ :=
  Complex.cos (↑(2 * π / n)) + Complex.sin (↑(2 * π / n)) * I

/-! ## Part I: De Moivre collapses ωⁿ to 1 -/

/-- **Headline (De Moivre).** ωⁿ = 1 for every n > 0.

    Proof: by De Moivre's formula `cos_add_sin_mul_I_pow`,
      ωⁿ = cos(n·(2π/n)) + i·sin(n·(2π/n)) = cos(2π) + i·sin(2π) = 1. -/
theorem omega_pow_n (n : ℕ) (hn : 0 < n) : (omega n) ^ n = 1 := by
  unfold omega
  rw [Complex.cos_add_sin_mul_I_pow]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- n · (2π/n) = 2π   (as a complex number)
  have harg : (↑n : ℂ) * (↑(2 * π / n) : ℂ) = (↑(2 * π) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [harg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_two_pi, Real.sin_two_pi]
  norm_num

/-- Euler bridge: ω equals the exponential e^{2πi/n}.
    This identifies the trigonometric generator with Mathlib's `exp` form. -/
theorem omega_eq_exp (n : ℕ) : omega n = Complex.exp (2 * π * I / n) := by
  unfold omega
  rw [← Complex.exp_mul_I]
  congr 1
  push_cast
  ring

/-! ## Part II: ω is a primitive n-th root of unity -/

/-- ω is a *primitive* n-th root of unity (via the exponential identification). -/
theorem omega_isPrimitiveRoot (n : ℕ) (hn : 0 < n) :
    IsPrimitiveRoot (omega n) n := by
  rw [omega_eq_exp]
  exact Complex.isPrimitiveRoot_exp n hn.ne'

/-! ## Part III: every power of ω is an n-th root of unity -/

/-- Each power ωᵏ is again an n-th root of unity: (ωᵏ)ⁿ = (ωⁿ)ᵏ = 1ᵏ = 1. -/
theorem omega_pow_pow_n (n k : ℕ) (hn : 0 < n) : (omega n ^ k) ^ n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, omega_pow_n n hn, one_pow]

/-! ## Part IV: the powers ω⁰, …, ωⁿ⁻¹ are pairwise distinct -/

/-- For 0 ≤ i, j < n, ωⁱ = ωʲ forces i = j: the n powers are distinct. -/
theorem omega_pow_inj (n : ℕ) (hn : 0 < n) {i j : ℕ}
    (hi : i < n) (hj : j < n) (h : omega n ^ i = omega n ^ j) : i = j :=
  (omega_isPrimitiveRoot n hn).pow_inj hi hj h

/-- The map k ↦ ωᵏ is injective on {0, 1, …, n-1}. -/
theorem omega_pow_injOn (n : ℕ) (hn : 0 < n) :
    Set.InjOn (omega n ^ ·) (Finset.range n) :=
  (omega_isPrimitiveRoot n hn).injOn_pow

/-! ## Part V: the powers enumerate *all* n-th roots of unity -/

/-- The n-th roots of unity are *exactly* the powers ω⁰, ω¹, …, ωⁿ⁻¹.
    (As a multiset: `nthRoots n 1 = map (ω ^ ·) (range n)`.) -/
theorem nthRoots_eq_omega_powers (n : ℕ) (hn : 0 < n) :
    Polynomial.nthRoots n (1 : ℂ) = (Multiset.range n).map (omega n ^ ·) := by
  have h := (omega_isPrimitiveRoot n hn).nthRoots_eq (α := 1) (a := 1) (by simp)
  simpa using h

/-- There are exactly n distinct n-th roots of unity. -/
theorem card_nthRootsFinset (n : ℕ) (hn : 0 < n) :
    (Polynomial.nthRootsFinset n (1 : ℂ)).card = n :=
  (omega_isPrimitiveRoot n hn).card_nthRootsFinset

/-! ## Part VI: verified small cases -/

-- n = 1: ω = cos(2π) + i·sin(2π) = 1
example : omega 1 = 1 := by
  simp only [omega, Nat.cast_one, div_one]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_two_pi, Real.sin_two_pi]
  norm_num

-- n = 2: ω = cos π + i·sin π = -1
example : omega 2 = -1 := by
  simp only [omega, Nat.cast_ofNat]
  rw [show (2 * π / 2 : ℝ) = π by ring]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]
  norm_num

-- n = 4: ω = cos(π/2) + i·sin(π/2) = i
example : omega 4 = I := by
  simp only [omega, Nat.cast_ofNat]
  rw [show (2 * π / 4 : ℝ) = π / 2 by ring]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

/-! ## Part VII: Summary -/

/-- **De Moivre OQ-04 Summary.** For n > 0, with ω = cos(2π/n) + i·sin(2π/n):
    (1) ωⁿ = 1 (De Moivre);
    (2) ω is a primitive n-th root of unity;
    (3) every power ωᵏ is an n-th root of unity;
    (4) there are exactly n distinct n-th roots of unity. -/
theorem demoivre_oq04_summary (n : ℕ) (hn : 0 < n) :
    (omega n) ^ n = 1 ∧
    IsPrimitiveRoot (omega n) n ∧
    (∀ k, (omega n ^ k) ^ n = 1) ∧
    (Polynomial.nthRootsFinset n (1 : ℂ)).card = n :=
  ⟨omega_pow_n n hn,
   omega_isPrimitiveRoot n hn,
   fun k => omega_pow_pow_n n k hn,
   card_nthRootsFinset n hn⟩

end DeMoivreOQ04
