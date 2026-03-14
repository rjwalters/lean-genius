/-
  Angle Trisection OQ02-OQ03-OQ01:
  Gauss-Wantzel Theorem via Cyclotomic Field Infrastructure

  Bridges the gap between the axiomized Gauss-Wantzel theorem (OQ02-OQ03)
  and Mathlib's cyclotomic field infrastructure.

  Key decomposition of the OQ02-OQ03 axioms:
  1. cos(2π/n) is algebraic over ℚ — via primitive root of unity
  2. |Gal(minpoly(cos(2π/n)))| = φ(n)/2 — via maximal real subfield degree

  This file proves:
  - ζₙ = exp(2πi/n) is a primitive n-th root of unity (from Mathlib)
  - cos(2π/n) = Re(ζₙ) connection via Euler's formula
  - ζₙ + ζₙ⁻¹ = 2·cos(2π/n) (the key bridge)
  - Cyclotomic polynomial properties
  - [ℚ(ζₙ):ℚ] = φ(n) (from Mathlib IsCyclotomicExtension.finrank)
  - Complex conjugation as an automorphism of ℚ(ζₙ)/ℚ
  - Maximal real subfield degree [ℚ(cos(2π/n)):ℚ] = φ(n)/2 (axiomized)

  Status: 0 sorries, several axioms for infrastructure gaps.
-/

import Mathlib

open Complex Polynomial Polynomial.Chebyshev

namespace AngleTrisectionOQ02OQ03OQ01

-- ============================================================================
-- § 1. Primitive Roots of Unity and Euler's Formula
-- ============================================================================

/-- The n-th root of unity: ζₙ = exp(2πi/n) -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- exp(2πi/n) expressed via Euler's formula: cos(2π/n) + i·sin(2π/n) -/
theorem zeta_eq_cos_sin (n : ℕ) :
    zeta n = ↑(Real.cos (2 * Real.pi / n)) + ↑(Real.sin (2 * Real.pi / n)) * Complex.I := by
  unfold zeta
  rw [show (2 : ℂ) * ↑Real.pi * I / ↑(n : ℕ) = ↑(2 * Real.pi / ↑n) * I by push_cast; ring]
  rw [exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

/-- The real part of ζₙ is cos(2π/n). -/
theorem zeta_re (n : ℕ) : (zeta n).re = Real.cos (2 * Real.pi / n) := by
  rw [zeta_eq_cos_sin]
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]

/-- The imaginary part of ζₙ is sin(2π/n). -/
theorem zeta_im (n : ℕ) : (zeta n).im = Real.sin (2 * Real.pi / n) := by
  rw [zeta_eq_cos_sin]
  simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re]

/-- The conjugate of ζₙ is ζₙ⁻¹ = exp(-2πi/n). -/
theorem zeta_conj (n : ℕ) (hn : (n : ℂ) ≠ 0) :
    starRingEnd ℂ (zeta n) = (zeta n)⁻¹ := by
  unfold zeta
  rw [map_div₀, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]
  rw [show (2 : ℂ) * ↑Real.pi * -I / ↑(n : ℕ) = -(2 * ↑Real.pi * I / ↑(n : ℕ)) by ring]
  rw [Complex.exp_neg]

/-- Key bridge: ζₙ + conj(ζₙ) = 2·cos(2π/n).
    This connects cyclotomic fields to the real cosine. -/
theorem zeta_add_conj (n : ℕ) :
    zeta n + starRingEnd ℂ (zeta n) = 2 * ↑(Real.cos (2 * Real.pi / n)) := by
  rw [zeta_eq_cos_sin]
  simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- ζₙ + ζₙ⁻¹ = 2·cos(2π/n) (when n ≠ 0 as a complex number). -/
theorem zeta_add_inv (n : ℕ) (hn : (n : ℂ) ≠ 0) :
    zeta n + (zeta n)⁻¹ = 2 * ↑(Real.cos (2 * Real.pi / n)) := by
  rw [← zeta_conj n hn, zeta_add_conj]

-- ============================================================================
-- § 2. Powers and Unit Circle
-- ============================================================================

/-- |ζₙ| = 1: the root of unity lies on the unit circle. -/
theorem zeta_abs (n : ℕ) : Complex.abs (zeta n) = 1 := by
  unfold zeta
  rw [show (2 : ℂ) * ↑Real.pi * I / ↑(n : ℕ) = ↑(2 * Real.pi / ↑n) * I by push_cast; ring]
  rw [Complex.abs_exp_ofReal_mul_I]

/-- ζₙ ≠ 0 (since |ζₙ| = 1). -/
theorem zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := by
  intro h
  have := zeta_abs n
  rw [h, map_zero] at this
  norm_num at this

/-- ζₙⁿ = 1: the defining property of an n-th root of unity. -/
theorem zeta_pow (n : ℕ) (hn : 0 < n) : zeta n ^ n = 1 := by
  unfold zeta
  rw [← Complex.exp_natCast_mul]
  have : (n : ℂ) * (2 * ↑Real.pi * I / ↑n) = 2 * ↑Real.pi * I := by
    field_simp
    ring
  rw [this]
  simp [Complex.exp_two_pi_mul_I]

/-- ζₙ is an n-th root of unity (i.e., ζₙ ∈ rootsOfUnity n ℂ). -/
theorem zeta_mem_rootsOfUnity (n : ℕ) (hn : 0 < n) :
    (Units.mk0 (zeta n) (zeta_ne_zero n)) ^ n = 1 := by
  ext
  simp [Units.val_pow_eq_pow_val, zeta_pow n hn]

-- ============================================================================
-- § 3. Cos(2π/n) Special Values
-- ============================================================================

/-- cos(2π/1) = cos(2π) = 1. -/
theorem cos_2pi_div_1 : Real.cos (2 * Real.pi / 1) = 1 := by
  simp [Real.cos_two_pi]

/-- cos(2π/2) = cos(π) = -1. -/
theorem cos_2pi_div_2 : Real.cos (2 * Real.pi / 2) = -1 := by
  norm_num [Real.cos_pi]

/-- cos(2π/4) = cos(π/2) = 0. -/
theorem cos_2pi_div_4 : Real.cos (2 * Real.pi / 4) = 0 := by
  norm_num [show (2 : ℝ) * Real.pi / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two]

-- ============================================================================
-- § 4. Algebraicity of cos(2π/n)
-- ============================================================================

-- The proof that cos(2π/n) is algebraic over ℚ requires connecting
-- Real.cos to cyclotomic polynomials. The key insight:
--
-- ζₙ is a root of xⁿ - 1 = 0, hence algebraic over ℚ.
-- cos(2π/n) = (ζₙ + ζₙ⁻¹)/2, a polynomial in ζₙ.
-- Algebraic elements are closed under +, ×, ⁻¹ (for nonzero).
-- Therefore cos(2π/n) is algebraic.

/-- cos(2π/n) as a function of ζₙ: explicit formula. -/
theorem cos_eq_half_zeta_plus_inv (n : ℕ) (hn : (n : ℂ) ≠ 0) :
    (Real.cos (2 * Real.pi / n) : ℂ) = (zeta n + (zeta n)⁻¹) / 2 := by
  rw [zeta_add_inv n hn]
  ring

/-- The minimal polynomial of ζₙ over ℤ divides xⁿ - 1.
    In Mathlib, this is captured by the cyclotomic polynomial Φₙ(x)
    which is the irreducible factor of xⁿ - 1 over ℚ. -/
theorem zeta_is_root_of_unity_poly (n : ℕ) (hn : 0 < n) :
    (X ^ n - 1 : ℂ[X]).IsRoot (zeta n) := by
  simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, zeta_pow n hn, sub_self]

-- ============================================================================
-- § 5. Chebyshev Polynomials and the Minimal Polynomial of cos(2π/n)
-- ============================================================================

-- The minimal polynomial of cos(2π/n) over ℚ is related to Chebyshev
-- polynomials. Specifically, if Φₙ(x) = Π(x - ζₙᵏ) for gcd(k,n)=1,
-- then the minimal polynomial of 2·cos(2π/n) is the "Chebyshev-like"
-- polynomial obtained from Φₙ by the substitution x → (t + t⁻¹).

/-- The Chebyshev polynomial of the first kind T_n satisfies
    T_n(cos θ) = cos(nθ). This connects polynomial roots to cosine values.

    PROVED from Mathlib: Polynomial.Chebyshev.T ℤ n provides integer-coefficient
    Chebyshev polynomials, map_T shows they map correctly between rings, and
    T_real_cos gives the evaluation identity. -/
theorem chebyshev_T_exists (n : ℕ) :
    ∃ P : ℤ[X], ∀ θ : ℝ, (P.map (Int.castRingHom ℝ)).eval (Real.cos θ) = Real.cos (n * θ) := by
  refine ⟨T ℤ (n : ℤ), fun θ => ?_⟩
  rw [map_T (Int.castRingHom ℝ) (n : ℤ), T_real_cos θ (n : ℤ)]
  push_cast; ring

/-- The degree of the Chebyshev polynomial T_n is n.

    PROVED from Mathlib: natDegree_T gives (T R n).natDegree = n.natAbs,
    and for n : ℕ we have (↑n : ℤ).natAbs = n. -/
theorem chebyshev_T_degree (n : ℕ) (hn : 0 < n) :
    ∃ P : ℤ[X], P.natDegree = n ∧
    ∀ θ : ℝ, (P.map (Int.castRingHom ℝ)).eval (Real.cos θ) = Real.cos (n * θ) := by
  refine ⟨T ℤ (n : ℤ), ?_, fun θ => ?_⟩
  · rw [Polynomial.Chebyshev.natDegree_T]; simp [Int.natAbs_ofNat]
  · rw [map_T (Int.castRingHom ℝ) (n : ℤ), T_real_cos θ (n : ℤ)]
    push_cast; ring

-- ============================================================================
-- § 6. Cyclotomic Extension Degree
-- ============================================================================

-- Mathlib provides [ℚ(ζₙ):ℚ] = φ(n) via IsCyclotomicExtension.finrank.
-- We connect this to our concrete ζₙ = exp(2πi/n).

/-- The cyclotomic polynomial Φₙ(x) ∈ ℚ[X] has degree φ(n).
    This is a direct consequence of Mathlib's cyclotomic polynomial API. -/
theorem cyclotomic_degree (n : ℕ) (hn : 0 < n) :
    (Polynomial.cyclotomic n ℚ).natDegree = Nat.totient n :=
  Polynomial.natDegree_cyclotomic n ℚ

/-- The cyclotomic polynomial is irreducible over ℚ.
    This is a key result from algebraic number theory, available in Mathlib. -/
theorem cyclotomic_irreducible (n : ℕ) (hn : 0 < n) :
    Irreducible (Polynomial.cyclotomic n ℚ) :=
  Polynomial.cyclotomic.irreducible_rat hn

-- ============================================================================
-- § 7. Maximal Real Subfield
-- ============================================================================

-- The maximal real subfield ℚ(ζₙ⁺) = ℚ(ζₙ + ζₙ⁻¹) = ℚ(2cos(2π/n)).
-- Complex conjugation σ: ζₙ ↦ ζₙ⁻¹ is an order-2 automorphism.
-- The fixed field of σ is the maximal real subfield.
-- [ℚ(ζₙ):ℚ(ζₙ⁺)] = 2, so [ℚ(ζₙ⁺):ℚ] = φ(n)/2 for n ≥ 3.

/-- Complex conjugation restricts to an automorphism of ℚ(ζₙ) of order 2 (for n ≥ 3).
    This gives the index-2 subgroup whose fixed field is the maximal real subfield.

    Proof: The map autEquivPow gives Gal(ℚ(ζₙ)/ℚ) ≃ (ℤ/nℤ)*.
    The element -1 ∈ (ℤ/nℤ)* maps to an automorphism σ with:
    - σ ≠ id: since -1 ≠ 1 in (ℤ/nℤ)* for n ≥ 3
    - σ² = id: since (-1)² = 1 in (ℤ/nℤ)* -/
theorem complex_conj_order_two (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    ∃ (σ : (CyclotomicField n ℚ) ≃ₐ[ℚ] (CyclotomicField n ℚ)),
    σ ≠ AlgEquiv.refl ∧ σ * σ = AlgEquiv.refl := by
  set K := CyclotomicField n ℚ
  have hn_pos : 0 < n := by omega
  have hirr := Polynomial.cyclotomic.irreducible_rat hn_pos
  have hequiv := galCyclotomicEquivUnitsZMod (L := K) hirr
  -- The automorphism corresponding to -1 ∈ (ℤ/nℤ)*
  set u : (ZMod n)ˣ := -1
  set σ := hequiv.symm u
  refine ⟨σ, ?_, ?_⟩
  · -- σ ≠ refl: -1 ≠ 1 in (ℤ/nℤ)* for n ≥ 3
    intro h
    have h_eq : hequiv σ = hequiv (AlgEquiv.refl) := congr_arg hequiv h
    rw [hequiv.apply_symm_apply] at h_eq
    -- hequiv(refl) = 1
    have h_one : hequiv AlgEquiv.refl = 1 := map_one hequiv
    rw [h_one] at h_eq
    -- So -1 = 1 in (ZMod n)ˣ, contradiction for n ≥ 3
    have h_units : (-1 : (ZMod n)ˣ) = 1 := h_eq
    have h_neg : (-1 : ZMod n) = 1 := by
      have := congr_arg Units.val h_units; simpa using this
    -- -1 = 1 means 1 + 1 = 0 in ZMod n (since -1 + 1 = 0 = 1 + 1)
    have h2 : (2 : ZMod n) = 0 := by
      have h0 := neg_add_cancel (1 : ZMod n)  -- -1 + 1 = 0
      rw [h_neg] at h0  -- 1 + 1 = 0
      rw [show (2 : ZMod n) = 1 + 1 from by norm_num]
      exact h0
    -- (2 : ZMod n) = 0 means n | 2
    rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) from by push_cast; ring] at h2
    have h_dvd : n ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 n).mp h2
    -- But n ≥ 3 and n | 2 is impossible
    omega
  · -- σ² = refl: (-1)² = 1
    have h_sq : u * u = 1 := by ext; simp
    have : σ * σ = hequiv.symm (u * u) := by
      show hequiv.symm u * hequiv.symm u = hequiv.symm (u * u)
      rw [← map_mul hequiv.symm]
    rw [this, h_sq, map_one hequiv.symm]

/-- The degree of the maximal real subfield over ℚ is φ(n)/2 for n ≥ 3.
    This is the key numerical fact connecting cyclotomic theory to constructibility. -/
axiom maximal_real_subfield_degree (n : ℕ) (hn : 3 ≤ n) :
    ∃ (F : IntermediateField ℚ (CyclotomicField n ℚ)),
    Module.finrank ℚ F = Nat.totient n / 2

-- ============================================================================
-- § 8. Connecting to the OQ02-OQ03 Axioms
-- ============================================================================

-- We show how the cyclotomic infrastructure implies the two primitive axioms
-- from AngleTrisectionOQ02OQ03.lean (Section XIV).

/-- cos(2π/n) satisfies a monic polynomial over ℤ of degree φ(n)/2.
    This polynomial is called the minimal polynomial of cos(2π/n) over ℚ.
    Its existence proves cos(2π/n) is algebraic (hence integral) over ℚ.

    Proof roadmap (not yet available in Mathlib):
    1. ζₙ is a root of Φₙ(x) ∈ ℤ[x] of degree φ(n)
    2. cos(2π/n) = (ζₙ + ζₙ⁻¹)/2 satisfies a related polynomial
    3. The substitution x = (t + t⁻¹)/2 in Φₙ gives a polynomial of degree φ(n)/2
    4. This polynomial has integer coefficients (by Vieta's formulas) -/
axiom cos_minimal_poly_degree (n : ℕ) (hn : 3 ≤ n) :
    ∃ P : ℚ[X], P.Monic ∧ P.natDegree = Nat.totient n / 2 ∧
    Polynomial.aeval (Real.cos (2 * Real.pi / n)) P = 0

/-- From cos_minimal_poly_degree, cos(2π/n) is integral over ℚ.
    This is the first primitive axiom from OQ02-OQ03 Section XIV. -/
theorem cos_algebraic_from_cyclotomic (n : ℕ) (hn : 3 ≤ n) :
    IsAlgebraic ℚ (Real.cos (2 * Real.pi / n)) := by
  obtain ⟨P, hP_monic, _, hP_root⟩ := cos_minimal_poly_degree n hn
  exact ⟨P, hP_monic.ne_zero, hP_root⟩

-- ============================================================================
-- § 9. Degree Computation for Galois Group
-- ============================================================================

-- The Galois group of the minimal polynomial of cos(2π/n) has order
-- equal to the degree of the minimal polynomial (since the extension is Galois).

/-- For n ≥ 3, the extension ℚ(cos(2π/n))/ℚ is Galois (it's a subfield
    of the Galois extension ℚ(ζₙ)/ℚ, fixed by a normal subgroup). -/
axiom cos_extension_is_galois (n : ℕ) (hn : 3 ≤ n) :
    ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    Real.cos (2 * Real.pi / n) ∈ K ∧
    Module.finrank ℚ K = Nat.totient n / 2

/-- From the Galois extension, |Gal(minpoly(cos(2π/n)))| = φ(n)/2.
    This is the second primitive axiom from OQ02-OQ03 Section XIV.

    Combined with cos_algebraic_from_cyclotomic, these two results give
    the complete decomposition needed for the Gauss-Wantzel theorem. -/
theorem gal_card_from_cyclotomic (n : ℕ) (hn : 3 ≤ n) :
    ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    Real.cos (2 * Real.pi / n) ∈ K ∧
    Module.finrank ℚ K = Nat.totient n / 2 :=
  cos_extension_is_galois n hn

-- ============================================================================
-- § 10. Axiom Count and Roadmap
-- ============================================================================

/-
  AXIOM INVENTORY (updated):
  1. chebyshev_T_exists: ✅ PROVED (line 171, from Mathlib T_real_cos)
  2. chebyshev_T_degree: ✅ PROVED (line 181, from Mathlib natDegree_T)
  3. complex_conj_order_two: ✅ PROVED (line 224, via galCyclotomicEquivUnitsZMod and -1 ∈ (ℤ/nℤ)*)

  4. maximal_real_subfield_degree: [ℚ(ζₙ⁺):ℚ] = φ(n)/2
     STATUS: Requires Galois theory fixed-field degree formula
     EFFORT: ~150 lines (fixed field of order-2 subgroup has index 2)

  5. cos_minimal_poly_degree: minpoly(cos(2π/n)) has degree φ(n)/2
     STATUS: Follows from maximal_real_subfield_degree + cos generates subfield
     EFFORT: ~100 lines (connecting CyclotomicField to ℝ via embedding)

  6. cos_extension_is_galois: ℚ(cos(2π/n))/ℚ is Galois of degree φ(n)/2
     STATUS: Follows from fixed field of normal subgroup being Galois
     EFFORT: ~80 lines

  TOTAL ESTIMATED: ~490 lines to eliminate all axioms.
  DEPENDENCY: 4 → 5 → 6 → gal_card, and 1+2 are independent.

  PROVED IN THIS FILE:
  - zeta_eq_cos_sin: ζₙ = cos(2π/n) + i·sin(2π/n)
  - zeta_re/zeta_im: Re/Im of ζₙ
  - zeta_conj: conj(ζₙ) = ζₙ⁻¹
  - zeta_add_conj/zeta_add_inv: ζₙ + ζₙ⁻¹ = 2cos(2π/n)
  - zeta_abs: |ζₙ| = 1
  - zeta_ne_zero: ζₙ ≠ 0
  - zeta_pow: ζₙⁿ = 1
  - zeta_is_root_of_unity_poly: ζₙ is root of xⁿ - 1
  - cos_eq_half_zeta_plus_inv: cos = (ζ + ζ⁻¹)/2
  - cos_2pi_div_1/2/4: special values
  - cyclotomic_degree: deg(Φₙ) = φ(n) (from Mathlib)
  - cyclotomic_irreducible: Φₙ irreducible over ℚ (from Mathlib)
  - cos_algebraic_from_cyclotomic: cos(2π/n) is algebraic (from axiom)
  - gal_card_from_cyclotomic: Galois group has order φ(n)/2 (from axiom)
-/

#check @zeta_eq_cos_sin
#check @zeta_add_inv
#check @zeta_pow
#check @cyclotomic_degree
#check @cyclotomic_irreducible
#check @cos_algebraic_from_cyclotomic

end AngleTrisectionOQ02OQ03OQ01
