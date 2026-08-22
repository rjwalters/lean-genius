import Proofs.Erdos85RationalPrimaryTraceSplit
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# A primary sector excludes the distinguished square pair

If a primary polynomial does not vanish at the distinguished `T`-eigenvalue
`δ`, then the corresponding primary restriction of `S` cannot contain an
eigenvalue `θ` whose square identity pairs it back to `δ`.
-/

open Polynomial

namespace Erdos85

noncomputable section

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- A vector with `T v = δ v` evaluates every polynomial in `T` by scalar
evaluation at `δ`. -/
theorem aeval_apply_of_apply_eq_smul
    (T : E →ₗ[K] E) {δ : K} {v : E} (hTv : T v = δ • v)
    (p : K[X]) : aeval T p v = p.eval δ • v := by
  have hpow : ∀ n : ℕ, (T ^ n) v = (δ ^ n) • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Module.End.mul_apply, hTv, map_smul, ih,
          pow_succ, mul_smul]
        exact smul_comm δ (δ ^ n) v
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial n a =>
      rw [aeval_monomial, eval_monomial]
      simp [Module.End.mul_apply, hpow, smul_smul, mul_comm]

/-- If `p(δ) ≠ 0`, the restriction of `S` to `ker p(T)` has no
eigenvalue `θ` satisfying `κ-θ²=δ`, under `S²=κI-T`. -/
theorem not_isRoot_charpoly_kerAevalRestrict_of_pair_eq_distinguished
    [FiniteDimensional K E]
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    (p : K[X]) {κ δ θ : K}
    (hsq : S * S = κ • (1 : E →ₗ[K] E) - T)
    (hpδ : p.eval δ ≠ 0) (hpair : κ - θ ^ 2 = δ) :
    ¬ IsRoot (kerAevalRestrict S T hcomm p).charpoly θ := by
  intro hroot
  let R := kerAevalRestrict S T hcomm p
  have heig : Module.End.HasEigenvalue R θ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly R θ).mpr hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hSv : S (v : E) = θ • (v : E) := by
    simpa [R, kerAevalRestrict_coe] using congrArg Subtype.val hv.apply_eq_smul
  have hsquare := LinearMap.congr_fun hsq (v : E)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, hSv, map_smul] at hsquare
  have hTv : T (v : E) = δ • (v : E) := by
    rw [← hpair, sub_smul, pow_two, mul_smul]
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using (eq_sub_iff_add_eq.mp hsquare)
  have hvker : aeval T p (v : E) = 0 := v.property
  rw [aeval_apply_of_apply_eq_smul T hTv p] at hvker
  have hvzero : (v : E) = 0 :=
    (smul_eq_zero.mp hvker).resolve_left hpδ
  exact hv.2 (Subtype.ext hvzero)

/-- Complex-root wrapper over `ℚ`: if the distinguished difference is the
rational square `a²`, then no real root of the mapped primary-restriction
characteristic polynomial can pair back to `δ`. -/
theorem pair_ne_distinguished_of_mem_roots_map_primary_charpoly
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S)
    (p : ℚ[X]) {κ δ a : ℚ}
    (hsq : S * S = κ • (1 : E →ₗ[ℚ] E) - T)
    (hpδ : p.eval δ ≠ 0) (ha : κ - a ^ 2 = δ)
    {z : ℂ}
    (hz : z ∈ ((kerAevalRestrict S T hcomm p).charpoly.map
      (algebraMap ℚ ℂ)).roots)
    (hzreal : z.im = 0) :
    (κ : ℝ) - z.re ^ 2 ≠ (δ : ℝ) := by
  intro hpair
  have hsquare : z.re ^ 2 = (a : ℝ) ^ 2 := by
    have haR : (κ : ℝ) - (a : ℝ) ^ 2 = (δ : ℝ) := by
      exact_mod_cast ha
    linarith
  have hfne : (kerAevalRestrict S T hcomm p).charpoly ≠ 0 :=
    (LinearMap.charpoly_monic _).ne_zero
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquare with hza | hza
  · have hz_eq : z = (a : ℂ) := by
      apply Complex.ext
      · simpa using hza
      · simpa using hzreal
    have hrootC : IsRoot
        ((kerAevalRestrict S T hcomm p).charpoly.map (algebraMap ℚ ℂ))
        (a : ℂ) := by
      rw [← hz_eq]
      exact (mem_roots (by simpa using hfne)).mp hz
    have hrootQ : IsRoot (kerAevalRestrict S T hcomm p).charpoly a :=
      (Polynomial.isRoot_map_iff (algebraMap ℚ ℂ).injective).mp hrootC
    exact not_isRoot_charpoly_kerAevalRestrict_of_pair_eq_distinguished
      (κ := κ) (δ := δ) (θ := a) S T hcomm p hsq hpδ ha hrootQ
  · have hz_eq : z = (-a : ℚ) := by
      apply Complex.ext
      · norm_num at hza ⊢
        exact hza
      · simpa using hzreal
    have hrootC : IsRoot
        ((kerAevalRestrict S T hcomm p).charpoly.map (algebraMap ℚ ℂ))
        ((-a : ℚ) : ℂ) := by
      rw [← hz_eq]
      exact (mem_roots (by simpa using hfne)).mp hz
    have hrootQ : IsRoot (kerAevalRestrict S T hcomm p).charpoly (-a) :=
      (Polynomial.isRoot_map_iff (algebraMap ℚ ℂ).injective).mp hrootC
    apply not_isRoot_charpoly_kerAevalRestrict_of_pair_eq_distinguished
      (κ := κ) (δ := δ) (θ := -a) S T hcomm p hsq hpδ
        (by simpa [sq] using ha)
    exact hrootQ

#print axioms aeval_apply_of_apply_eq_smul
#print axioms not_isRoot_charpoly_kerAevalRestrict_of_pair_eq_distinguished
#print axioms pair_ne_distinguished_of_mem_roots_map_primary_charpoly

end

end Erdos85
