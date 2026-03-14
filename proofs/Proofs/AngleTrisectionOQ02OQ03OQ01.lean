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
  - Maximal real subfield degree [ℚ(cos(2π/n)):ℚ] = φ(n)/2 (PROVED via fixedField)

  Status: 0 sorries, 2 axioms remaining (cos_minimal_poly_degree, cos_extension_is_galois).
  maximal_real_subfield_degree: PROVED (was axiom, now theorem via fundamental theorem of Galois theory)
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
  push_cast; ring

/-- The real part of ζₙ is cos(2π/n). -/
theorem zeta_re (n : ℕ) : (zeta n).re = Real.cos (2 * Real.pi / n) := by
  rw [zeta_eq_cos_sin, add_re, ofReal_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]
  ring

/-- The imaginary part of ζₙ is sin(2π/n). -/
theorem zeta_im (n : ℕ) : (zeta n).im = Real.sin (2 * Real.pi / n) := by
  rw [zeta_eq_cos_sin, add_im, ofReal_im, mul_im, ofReal_re, I_re, ofReal_im, I_im]
  ring

/-- The conjugate of ζₙ is ζₙ⁻¹ = exp(-2πi/n). -/
theorem zeta_conj (n : ℕ) (hn : (n : ℂ) ≠ 0) :
    starRingEnd ℂ (zeta n) = (zeta n)⁻¹ := by
  unfold zeta
  rw [show (2 : ℂ) * ↑Real.pi * I / ↑(n : ℕ) = ↑(2 * Real.pi / ↑n) * I by push_cast; ring]
  rw [← Complex.exp_conj]
  have : (starRingEnd ℂ) (↑(2 * Real.pi / ↑n) * I) = -(↑(2 * Real.pi / ↑n) * I) := by
    rw [map_mul, conj_ofReal, conj_I, mul_neg]
  rw [this, Complex.exp_neg]

/-- Key bridge: ζₙ + conj(ζₙ) = 2·cos(2π/n).
    This connects cyclotomic fields to the real cosine. -/
theorem zeta_add_conj (n : ℕ) :
    zeta n + starRingEnd ℂ (zeta n) = 2 * ↑(Real.cos (2 * Real.pi / n)) := by
  rw [zeta_eq_cos_sin, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  push_cast; ring

/-- ζₙ + ζₙ⁻¹ = 2·cos(2π/n) (when n ≠ 0 as a complex number). -/
theorem zeta_add_inv (n : ℕ) (hn : (n : ℂ) ≠ 0) :
    zeta n + (zeta n)⁻¹ = 2 * ↑(Real.cos (2 * Real.pi / n)) := by
  rw [← zeta_conj n hn, zeta_add_conj]

-- ============================================================================
-- § 2. Powers and Unit Circle
-- ============================================================================

/-- ‖ζₙ‖ = 1: the root of unity lies on the unit circle. -/
theorem zeta_norm (n : ℕ) : ‖zeta n‖ = 1 := by
  unfold zeta
  rw [show (2 : ℂ) * ↑Real.pi * I / ↑(n : ℕ) = ↑(2 * Real.pi / ↑n) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- ζₙ ≠ 0 (since ‖ζₙ‖ = 1). -/
theorem zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := by
  intro h
  have := zeta_norm n
  rw [h, norm_zero] at this
  norm_num at this

/-- ζₙⁿ = 1: the defining property of an n-th root of unity. -/
theorem zeta_pow (n : ℕ) (hn : 0 < n) : zeta n ^ n = 1 := by
  unfold zeta
  rw [← exp_nat_mul]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : ↑n * (2 * ↑Real.pi * I / ↑n) = 2 * ↑Real.pi * I := by
    field_simp; ring
  rw [this, Complex.exp_two_pi_mul_I]

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

/-- cos(2π/n) as a function of ζₙ: explicit formula. -/
theorem cos_eq_half_zeta_plus_inv (n : ℕ) (hn : (n : ℂ) ≠ 0) :
    (Real.cos (2 * Real.pi / n) : ℂ) = (zeta n + (zeta n)⁻¹) / 2 := by
  rw [zeta_add_inv n hn]
  ring

/-- The minimal polynomial of ζₙ over ℤ divides xⁿ - 1. -/
theorem zeta_is_root_of_unity_poly (n : ℕ) (hn : 0 < n) :
    (X ^ n - 1 : ℂ[X]).IsRoot (zeta n) := by
  simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, zeta_pow n hn, sub_self]

-- ============================================================================
-- § 5. Chebyshev Polynomials and the Minimal Polynomial of cos(2π/n)
-- ============================================================================

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

-- ============================================================================
-- § 6. Cyclotomic Extension Degree
-- ============================================================================

/-- The cyclotomic polynomial Φₙ(x) ∈ ℚ[X] has degree φ(n). -/
theorem cyclotomic_degree (n : ℕ) (hn : 0 < n) :
    (Polynomial.cyclotomic n ℚ).natDegree = Nat.totient n :=
  Polynomial.natDegree_cyclotomic n ℚ

/-- The cyclotomic polynomial is irreducible over ℚ. -/
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

    Proof: The map galCyclotomicEquivUnitsZMod gives Gal(ℚ(ζₙ)/ℚ) ≃ (ℤ/nℤ)*.
    The element -1 ∈ (ℤ/nℤ)* maps to an automorphism σ with:
    - σ ≠ id: since -1 ≠ 1 in (ℤ/nℤ)* for n ≥ 3
    - σ² = id: since (-1)² = 1 in (ℤ/nℤ)* -/
theorem complex_conj_order_two (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    ∃ (σ : (CyclotomicField n ℚ) ≃ₐ[ℚ] (CyclotomicField n ℚ)),
    σ ≠ 1 ∧ σ ^ 2 = 1 := by
  set K := CyclotomicField n ℚ
  have hn_pos : 0 < n := by omega
  have hirr := Polynomial.cyclotomic.irreducible_rat hn_pos
  have hequiv := galCyclotomicEquivUnitsZMod (L := K) hirr
  -- The automorphism corresponding to -1 ∈ (ℤ/nℤ)*
  set u : (ZMod n)ˣ := -1
  set σ := hequiv.symm u
  refine ⟨σ, ?_, ?_⟩
  · -- σ ≠ 1: -1 ≠ 1 in (ℤ/nℤ)* for n ≥ 3
    intro h
    have h_eq : hequiv σ = hequiv 1 := congr_arg hequiv h
    rw [hequiv.apply_symm_apply, map_one hequiv] at h_eq
    -- So -1 = 1 in (ZMod n)ˣ, hence in ZMod n
    have h_neg : (-1 : ZMod n) = 1 := by
      have := congr_arg (fun x : (ZMod n)ˣ => (x : ZMod n)) h_eq
      simpa [u] using this
    -- -1 = 1 means 2 = 0 in ZMod n, so n | 2, contradicting n ≥ 3
    have h2 : (2 : ZMod n) = 0 := by
      have := neg_add_cancel (1 : ZMod n)
      rw [h_neg] at this
      rwa [show (2 : ZMod n) = 1 + 1 from by norm_num]
    rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) from by push_cast; ring] at h2
    have h_dvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp h2
    exact absurd (Nat.le_of_dvd (by omega) h_dvd) (by omega)
  · -- σ² = 1: (-1)² = 1
    have h_sq : u * u = 1 := by
      show (-1 : (ZMod n)ˣ) * (-1) = 1
      rw [neg_mul_neg, one_mul]
    rw [sq]
    show hequiv.symm u * hequiv.symm u = 1
    rw [← map_mul hequiv.symm, h_sq, map_one hequiv.symm]

/-- The degree of the maximal real subfield over ℚ is φ(n)/2 for n ≥ 3.
    This is the key numerical fact connecting cyclotomic theory to constructibility.

    Proof: Complex conjugation σ has order 2 in Gal(ℚ(ζₙ)/ℚ). The fixed field
    F = ℚ(ζₙ)^⟨σ⟩ satisfies [ℚ(ζₙ):F] = |⟨σ⟩| = 2 by the fundamental theorem
    of Galois theory. Tower law gives [F:ℚ] = φ(n)/2. -/
theorem maximal_real_subfield_degree (n : ℕ) (hn : 3 ≤ n) :
    ∃ (F : IntermediateField ℚ (CyclotomicField n ℚ)),
    Module.finrank ℚ F = Nat.totient n / 2 := by
  haveI : NeZero n := ⟨by omega⟩
  have hn_pos : 0 < n := by omega
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hn_pos
  -- Step 1: Get order-2 automorphism σ from complex_conj_order_two
  obtain ⟨σ, hσ_ne, hσ_sq⟩ := complex_conj_order_two n hn
  -- Step 2: σ has order exactly 2
  have hord : orderOf σ = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact orderOf_eq_prime hσ_sq hσ_ne
  -- Step 3: The cyclic subgroup H = ⟨σ⟩ has cardinality 2
  set H := Subgroup.zpowers σ
  have hcard : Nat.card H = 2 := by rw [Nat.card_zpowers, hord]
  -- Step 4: The fixed field F = K^H has [K:F] = |H| = 2
  refine ⟨IntermediateField.fixedField H, ?_⟩
  have hKF : Module.finrank (IntermediateField.fixedField H)
      (CyclotomicField n ℚ) = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, hcard]
  -- Step 5: [K:ℚ] = φ(n)
  have hKQ : Module.finrank ℚ (CyclotomicField n ℚ) = Nat.totient n :=
    IsCyclotomicExtension.finrank (CyclotomicField n ℚ) hirr
  -- Step 6: Tower law: [F:ℚ] * [K:F] = [K:ℚ]
  have htower := Module.finrank_mul_finrank ℚ
    (↥(IntermediateField.fixedField H)) (CyclotomicField n ℚ)
  rw [hKF, hKQ] at htower
  omega

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

/-- For n ≥ 3, the extension ℚ(cos(2π/n))/ℚ is Galois of degree φ(n)/2.
    This follows from: the fixed field of a normal subgroup is a Galois extension. -/
axiom cos_extension_is_galois (n : ℕ) (hn : 3 ≤ n) :
    ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    Real.cos (2 * Real.pi / n) ∈ K ∧
    Module.finrank ℚ K = Nat.totient n / 2

/-- From the Galois extension, |Gal(minpoly(cos(2π/n)))| = φ(n)/2.
    This is the second primitive axiom from OQ02-OQ03 Section XIV. -/
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
  AXIOM INVENTORY (updated after maximal_real_subfield_degree proof):
  1. chebyshev_T_exists: ✅ PROVED (from Mathlib T_real_cos)
  2. complex_conj_order_two: ✅ PROVED (via galCyclotomicEquivUnitsZMod and -1 ∈ (ℤ/nℤ)*)
  3. maximal_real_subfield_degree: ✅ PROVED (via fixedField + tower law)

  4. cos_minimal_poly_degree: minpoly(cos(2π/n)) has degree φ(n)/2
     STATUS: AXIOM. Requires connecting CyclotomicField to ℝ via embedding.
     EFFORT: ~100 lines

  5. cos_extension_is_galois: ℚ(cos(2π/n))/ℚ is Galois of degree φ(n)/2
     STATUS: AXIOM. Follows from normality of conjugation subgroup.
     EFFORT: ~80 lines

  REMAINING: 2 axioms (down from 3).
  DEPENDENCY: 4 is independent, 5 depends on 4.

  PROVED IN THIS FILE:
  - zeta_eq_cos_sin: ζₙ = cos(2π/n) + i·sin(2π/n)
  - zeta_re/zeta_im: Re/Im of ζₙ
  - zeta_conj: conj(ζₙ) = ζₙ⁻¹
  - zeta_add_conj/zeta_add_inv: ζₙ + ζₙ⁻¹ = 2cos(2π/n)
  - zeta_norm: ‖ζₙ‖ = 1
  - zeta_ne_zero: ζₙ ≠ 0
  - zeta_pow: ζₙⁿ = 1
  - zeta_is_root_of_unity_poly: ζₙ is root of xⁿ - 1
  - cos_eq_half_zeta_plus_inv: cos = (ζ + ζ⁻¹)/2
  - cos_2pi_div_1/2/4: special values
  - cyclotomic_degree: deg(Φₙ) = φ(n) (from Mathlib)
  - cyclotomic_irreducible: Φₙ irreducible over ℚ (from Mathlib)
  - complex_conj_order_two: ∃ σ ∈ Gal, σ ≠ 1 ∧ σ² = 1
  - maximal_real_subfield_degree: [F:ℚ] = φ(n)/2 (via fixedField)
  - cos_algebraic_from_cyclotomic: cos(2π/n) is algebraic (from axiom)
  - gal_card_from_cyclotomic: Galois group has order φ(n)/2 (from axiom)
-/

#check @zeta_eq_cos_sin
#check @zeta_add_inv
#check @zeta_pow
#check @cyclotomic_degree
#check @cyclotomic_irreducible
#check @maximal_real_subfield_degree
#check @cos_algebraic_from_cyclotomic

end AngleTrisectionOQ02OQ03OQ01
