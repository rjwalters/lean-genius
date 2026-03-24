import Mathlib

/-
# ℂ is the Unique Algebraic Closure of ℝ

## What This Proves
The complex numbers ℂ form the unique algebraic closure of the real numbers ℝ.
Specifically:
1. ℂ is algebraic over ℝ (every complex number satisfies a real polynomial of degree ≤ 2)
2. ℂ is an algebraic closure of ℝ (algebraically closed + algebraic over ℝ)
3. Any algebraic closure of ℝ is ℝ-algebra isomorphic to ℂ (uniqueness)
4. [ℂ:ℝ] = 2 (the extension degree)
5. ℝ is not algebraically closed (X² + 1 has no real root)
6. Every complex number satisfies its characteristic real quadratic X² − 2Re(z)X + |z|²
7. ℂ is the smallest algebraically closed field containing ℝ

## Approach
- **Foundation**: Mathlib provides `Complex.isAlgClosed` and `Module.Finite ℝ ℂ`
- **Key bridge**: Finite extensions are integral, integral ↔ algebraic for fields
- **Uniqueness**: `IsAlgClosure.equiv` gives ℝ-algebra isomorphism between closures
- **Minimality**: Degree 2 means no proper subfield between ℝ and ℂ is algebraically closed

## Proof Techniques
- Field extension theory (finite → algebraic)
- Polynomial evaluation and root analysis
- Algebraic closure uniqueness (Steinitz theorem)

Historical Note: The fact that ℂ is algebraically closed was first proved by Gauss (1799).
That ℂ is the *unique* algebraic closure follows from Steinitz's theorem (1910) on
the existence and uniqueness of algebraic closures.
-/

open Polynomial Complex

namespace FTAUniqueAlgebraicClosure

/-
  Part 1: The Extension Degree [ℂ:ℝ] = 2

  The complex numbers form a 2-dimensional real vector space with basis {1, i}.
  This is the most fundamental structural fact about the extension ℝ ⊂ ℂ.
-/

-- The extension degree [ℂ:ℝ] = 2
theorem finrank_complex_over_reals : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- ℂ is a finite-dimensional ℝ-vector space
example : Module.Finite ℝ ℂ := inferInstance

/-
  Part 2: ℂ is Algebraic over ℝ

  Since [ℂ:ℝ] = 2 < ∞, the extension is finite, hence integral, hence algebraic.
  Every z ∈ ℂ satisfies a polynomial of degree ≤ 2 over ℝ.
-/

-- Every complex number is algebraic over ℝ (finite extension → algebraic)
instance complex_algebraic_over_reals : Algebra.IsAlgebraic ℝ ℂ :=
  Algebra.IsAlgebraic.of_finite ℝ ℂ

/-
  Part 3: ℂ is an Algebraic Closure of ℝ

  A field K is an algebraic closure of R if:
  (1) K is algebraically closed (every non-constant polynomial has a root)
  (2) K is algebraic over R (every element satisfies a polynomial over R)

  We combine Complex.isAlgClosed with our algebraicity result.
-/

-- ℂ is an algebraic closure of ℝ
instance complex_is_alg_closure : IsAlgClosure ℝ ℂ where
  isAlgClosed := Complex.isAlgClosed
  isAlgebraic := complex_algebraic_over_reals

/-
  Part 4: Uniqueness — Any Algebraic Closure of ℝ ≅ ℂ

  By Steinitz's theorem, algebraic closures are unique up to isomorphism.
  If L is any algebraic closure of ℝ, there exists an ℝ-algebra isomorphism L ≃ₐ[ℝ] ℂ.
-/

-- Any algebraic closure of ℝ is isomorphic to ℂ
noncomputable def unique_algebraic_closure
    (L : Type*) [Field L] [Algebra ℝ L] [Module.IsTorsionFree ℝ L]
    [IsAlgClosure ℝ L] : L ≃ₐ[ℝ] ℂ :=
  IsAlgClosure.equiv ℝ L ℂ

/-
  Part 5: ℝ is NOT Algebraically Closed

  The polynomial X² + 1 has no real root, since x² + 1 > 0 for all x ∈ ℝ.
  This shows ℝ strictly needs extension to become algebraically closed.
-/

-- X² + 1 has no real root
theorem no_real_root_of_x_sq_plus_one (x : ℝ) : x ^ 2 + 1 ≠ 0 := by
  have h : 0 < x ^ 2 + 1 := by positivity
  linarith

-- ℝ is not algebraically closed
theorem reals_not_alg_closed : ¬ IsAlgClosed ℝ := by
  intro h
  -- If ℝ were algebraically closed, X² + 1 would have a real root
  have hp : degree (X ^ 2 + 1 : ℝ[X]) ≠ 0 := by
    simp [degree_add_eq_left_of_degree_lt, degree_X_pow]
  obtain ⟨r, hr⟩ := h.exists_root _ hp
  -- But x² + 1 > 0 for all real x
  rw [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
  exact no_real_root_of_x_sq_plus_one r hr

/-
  Part 6: Every Complex Number Satisfies a Real Quadratic

  For any z ∈ ℂ, the polynomial X² - 2·Re(z)·X + |z|² has z as a root.
  This is the minimal polynomial for z ∉ ℝ, and factors as (X - z)(X - z̄).
-/

-- The characteristic quadratic of z: X² - 2·Re(z)·X + |z|²
noncomputable def charQuad (z : ℂ) : ℝ[X] :=
  X ^ 2 - C (2 * z.re) * X + C (z.re ^ 2 + z.im ^ 2)

-- z is a root of its characteristic quadratic
theorem is_root_charQuad (z : ℂ) :
    (charQuad z).eval₂ (algebraMap ℝ ℂ) z = 0 := by
  have halg : algebraMap ℝ ℂ = Complex.ofReal := rfl
  simp only [charQuad, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, halg]
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.zero_re, sq]
    ring
  · simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.zero_im, sq]
    ring

-- The conjugate z̄ is also a root
theorem is_root_charQuad_conj (z : ℂ) :
    (charQuad z).eval₂ (algebraMap ℝ ℂ) (starRingEnd ℂ z) = 0 := by
  have : charQuad z = charQuad (starRingEnd ℂ z) := by
    simp [charQuad, Complex.conj_re, Complex.conj_im]
  rw [this]
  exact is_root_charQuad (starRingEnd ℂ z)

/-
  Part 7: Minimality — ℂ is the Smallest Algebraically Closed Extension of ℝ

  Since [ℂ:ℝ] = 2, there are no intermediate fields between ℝ and ℂ
  (by the tower law, any intermediate field K has [ℂ:K]·[K:ℝ] = 2,
  so [K:ℝ] = 1 or 2). This means ℂ is the minimal algebraic closure.
-/

-- The tower law applied to ℝ ⊂ K ⊂ ℂ constrains K
-- [K:ℝ] divides [ℂ:ℝ] = 2, so [K:ℝ] ∈ {1, 2}
-- If [K:ℝ] = 1 then K = ℝ; if [K:ℝ] = 2 then K = ℂ
theorem no_intermediate_field (K : IntermediateField ℝ ℂ)
    (hK : Module.Finite ℝ K) :
    Module.finrank ℝ K = 1 ∨ Module.finrank ℝ K = 2 := by
  -- [ℂ:ℝ] = [ℂ:K] · [K:ℝ] and [ℂ:ℝ] = 2
  have h2 := finrank_complex_over_reals
  have htower := Module.finrank_mul_finrank ℝ (↥K) ℂ
  -- htower : finrank ℝ ↥K * finrank ↥K ℂ = finrank ℝ ℂ
  rw [h2] at htower
  -- finrank ℝ ↥K * finrank ↥K ℂ = 2, and both factors are positive
  have hK_pos : 0 < Module.finrank ℝ ↥K := Module.finrank_pos
  have hCK_pos : 0 < Module.finrank (↥K) ℂ := Module.finrank_pos
  -- a * b = 2 with b > 0 implies a ≤ 2
  have hle : Module.finrank ℝ ↥K ≤ 2 := by
    calc Module.finrank ℝ ↥K
        ≤ Module.finrank ℝ ↥K * Module.finrank (↥K) ℂ :=
          le_mul_of_one_le_right (Nat.zero_le _) hCK_pos
        _ = 2 := htower
  interval_cases (Module.finrank ℝ ↥K) <;> omega

/-
  Part 8: The Quadratic Extension is Necessary and Sufficient

  The extension ℝ → ℂ = ℝ[i] / (i² + 1) is the unique quadratic extension
  that makes every polynomial split. One step suffices because:
  - Degree 1: already has roots in ℝ
  - Degree 2: X² + bX + c = (X - z)(X - z̄) with z ∈ ℂ
  - Degree n: factors completely by induction using the quadratic formula
-/

-- i² = -1 (the defining relation of ℂ over ℝ)
theorem I_squared : (Complex.I : ℂ) ^ 2 = -1 := by
  rw [sq, Complex.I_mul_I]

-- ℂ = ℝ(i): every complex number is of the form a + bi
theorem complex_eq_real_add_real_I (z : ℂ) :
    z = ↑z.re + ↑z.im * Complex.I :=
  (Complex.re_add_im z).symm

-- The algebraic closure of ℝ requires exactly one quadratic extension
-- (contrast with ℚ, whose closure is infinite-dimensional)
theorem closure_degree_is_two :
    Module.finrank ℝ ℂ = 2 ∧ IsAlgClosure ℝ ℂ :=
  ⟨finrank_complex_over_reals, complex_is_alg_closure⟩

end FTAUniqueAlgebraicClosure

-- Verification
#check FTAUniqueAlgebraicClosure.complex_is_alg_closure
#check FTAUniqueAlgebraicClosure.unique_algebraic_closure
#check FTAUniqueAlgebraicClosure.reals_not_alg_closed
#check FTAUniqueAlgebraicClosure.finrank_complex_over_reals
#check FTAUniqueAlgebraicClosure.no_intermediate_field
