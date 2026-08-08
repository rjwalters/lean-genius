import Proofs.Erdos85SymmetricSectorFactorization
import Mathlib.LinearAlgebra.Semisimple

/-!
# Semisimplicity of invariant restrictions of symmetric rational matrices

The hard-sector defect operator is the restriction of a symmetric rational
matrix to an invariant subspace.  This file supplies the missing abstract
bridge: a symmetric rational matrix has squarefree minimal polynomial, hence
its endomorphism is semisimple, and every invariant restriction remains
semisimple.
-/

open Polynomial
open scoped Matrix

namespace Erdos85

noncomputable section

/-- The minimal polynomial of a symmetric rational matrix is squarefree.

The proof is purely rational.  If `q²` divides the minimal polynomial `m`,
write `m = q²h`.  Symmetry makes `aeval A (qh)` symmetric, while its square
vanishes; the rational sum-of-squares argument therefore makes it zero.
Minimality then gives `m ∣ qh`, and cancellation forces `q` to be a unit. -/
theorem minpoly_squarefree_of_isSymm
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℚ} (hA : A.IsSymm) :
    Squarefree (minpoly ℚ A) := by
  intro q hq
  haveI : Algebra.IsIntegral ℚ (Matrix V V ℚ) :=
    Algebra.IsIntegral.of_finite ℚ _
  have hint : IsIntegral ℚ A := Algebra.IsIntegral.isIntegral A
  have hm0 : minpoly ℚ A ≠ 0 := minpoly.ne_zero hint
  obtain ⟨h, hm⟩ := hq
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hm0
    rw [hm, hzero, zero_mul, zero_mul]
  have hh0 : h ≠ 0 := by
    intro hzero
    apply hm0
    rw [hm, hzero, mul_zero]
  set M : Matrix V V ℚ := Polynomial.aeval A (q * h) with hMdef
  have hMsq : M * M = 0 := by
    rw [hMdef, ← map_mul]
    have hpoly : (q * h) * (q * h) = minpoly ℚ A * h := by
      rw [hm]
      ring
    rw [hpoly, map_mul, minpoly.aeval, zero_mul]
  have hMsymm : M.IsSymm := matrix_isSymm_aeval hA _
  have hM0 : M = 0 :=
    matrix_eq_zero_of_isSymm_of_mul_self_eq_zero hMsymm hMsq
  have hann : Polynomial.aeval A (q * h) = 0 := by
    rw [← hMdef, hM0]
  have hmindvd : minpoly ℚ A ∣ q * h := minpoly.dvd ℚ A hann
  obtain ⟨u, hu⟩ := hmindvd
  have hu' : q * h = q * ((q * u) * h) := by
    calc
      q * h = minpoly ℚ A * u := hu
      _ = q * ((q * u) * h) := by rw [hm]; ring
  have hc : h = (q * u) * h := mul_left_cancel₀ hq0 hu'
  have hcancel : 1 = q * u := by
    apply mul_right_cancel₀ hh0
    simpa using hc
  exact isUnit_iff_exists_inv.mpr ⟨u, hcancel.symm⟩

/-- A symmetric rational matrix, viewed as an endomorphism, is semisimple. -/
theorem toLin'_isSemisimple_of_isSymm
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℚ} (hA : A.IsSymm) :
    Module.End.IsSemisimple (Matrix.toLin' A : Module.End ℚ (V → ℚ)) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := minpoly ℚ (Matrix.toLin' A))
  · rw [Matrix.minpoly_toLin']
    exact minpoly_squarefree_of_isSymm hA
  · exact minpoly.aeval ℚ (Matrix.toLin' A)

/-- Restricting a symmetric rational matrix to any invariant subspace
preserves semisimplicity. -/
theorem restrict_isSemisimple_of_isSymm
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℚ} (hA : A.IsSymm)
    (p : Submodule ℚ (V → ℚ))
    (hp : p ∈ Module.End.invtSubmodule (Matrix.toLin' A)) :
    Module.End.IsSemisimple ((Matrix.toLin' A).restrict hp) :=
  (toLin'_isSemisimple_of_isSymm hA).restrict hp

/-- Peel a designated rational eigenvalue from the minimal polynomial of a
semisimple endomorphism.  The residual factor avoids that eigenvalue, divides
the minimal polynomial, and together with the linear factor annihilates the
operator. -/
theorem exists_residual_factor_of_isSemisimple
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : Module.End ℚ E) (hT : T.IsSemisimple) (μ : ℚ) :
    ∃ r : ℚ[X], r.eval μ ≠ 0 ∧ r ∣ minpoly ℚ T ∧
      minpoly ℚ T ∣ (X - C μ) * r := by
  set m : ℚ[X] := minpoly ℚ T with hm
  have hsq : Squarefree m := by
    rw [hm]
    exact hT.minpoly_squarefree
  have hnrepeat : ¬ (X - C μ : ℚ[X]) ^ 2 ∣ m := by
    intro hdvd
    exact not_isUnit_X_sub_C μ (hsq (X - C μ) (by simpa [pow_two] using hdvd))
  by_cases hμ : (X - C μ : ℚ[X]) ∣ m
  · obtain ⟨r, hr⟩ := hμ
    have hrdvd : r ∣ m := Dvd.intro_left _ hr.symm
    have hreval : r.eval μ ≠ 0 := by
      intro hzero
      obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hzero
      apply hnrepeat
      refine ⟨q, ?_⟩
      rw [hr, hq, pow_two]
      ring
    exact ⟨r, hreval, hrdvd, by rw [hr]⟩
  · have hmeval : m.eval μ ≠ 0 := by
      intro hzero
      exact hμ (Polynomial.dvd_iff_isRoot.mpr hzero)
    refine ⟨m, hmeval, dvd_rfl, ?_⟩
    exact dvd_mul_left m (X - C μ)

/-- The residual factor produced above is coprime to its removed linear
factor, and their product annihilates the semisimple operator. -/
theorem exists_coprime_residual_annihilator_of_isSemisimple
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : Module.End ℚ E) (hT : T.IsSemisimple) (μ : ℚ) :
    ∃ r : ℚ[X], r.eval μ ≠ 0 ∧ IsCoprime (X - C μ) r ∧
      Polynomial.aeval T ((X - C μ) * r) = 0 ∧ r ∣ minpoly ℚ T := by
  obtain ⟨r, hreval, hrdvd, hann⟩ :=
    exists_residual_factor_of_isSemisimple T hT μ
  have hcop : IsCoprime (X - C μ) r := by
    rw [(irreducible_X_sub_C μ).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact hreval
  have haeval : Polynomial.aeval T ((X - C μ) * r) = 0 := by
    obtain ⟨q, hq⟩ := hann
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  exact ⟨r, hreval, hcop, haeval, hrdvd⟩

end

end Erdos85
