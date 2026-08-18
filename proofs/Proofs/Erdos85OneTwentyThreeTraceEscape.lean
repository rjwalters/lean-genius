import Proofs.Erdos85OwnerFiberTraceSplit
import Proofs.Erdos85RationalPrimaryTraceSplit

/-!
# The forced nonprincipal trace at scalar 123

The degree-124 saturated exterior has a fiber-sum-zero sector of trace
`-135` on which the adjacency and lifted cycle-defect operators satisfy
`S² = 123 I - T`.  The principal defect frequency `T=2` has square root
`11`.  If every nonprincipal primary sector had trace zero, the principal
sector would have trace `-135`, impossible because its trace is divisible
by `11`.

This file isolates that numerical escape from the graph transport and the
cyclotomic arithmetic: any surviving residual must carry a genuinely
nonprincipal asymmetric trace orbit.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- At scalar `123`, total trace `-135` forces nonzero trace outside the
principal defect frequency `2`. -/
theorem residual_trace_ne_zero_of_sq_oneTwentyThree_of_trace_neg135
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S) (r : ℚ[X])
    (hcop : IsCoprime (X - C (2 : ℚ)) r)
    (hann : aeval T ((X - C (2 : ℚ)) * r) = 0)
    (hsq : S * S = (123 : ℚ) • (1 : E →ₗ[ℚ] E) - T)
    (htrace : LinearMap.trace ℚ E S = -(135 : ℚ)) :
    LinearMap.trace ℚ (LinearMap.ker (aeval T r))
      (kerAevalRestrict S T hcomm r) ≠ 0 := by
  intro hresidual
  have hsplit := trace_eq_add_trace_restrict_ker_aeval
    S T hcomm hcop hann
  have hprincipal : LinearMap.trace ℚ
      (LinearMap.ker (aeval T (X - C (2 : ℚ))))
      (kerAevalRestrict S T hcomm (X - C (2 : ℚ))) = -(135 : ℚ) := by
    rw [htrace, hresidual] at hsplit
    linarith
  let Z : E →ₗ[ℚ] E := 0
  have hsq' : S * S = (123 : ℚ) • (1 : E →ₗ[ℚ] E) + Z - T := by
    simp [Z, hsq]
  have hZT : Z * T = (0 : ℚ) • Z := by simp [Z]
  have hprincipalSq := kerAevalRestrict_X_sub_C_sq
    S T Z hcomm hsq' hZT (by norm_num : (2 : ℚ) ≠ 0)
  norm_num at hprincipalSq
  exact false_of_trace_eq_neg_of_sq_eq_square_nat_of_not_dvd
    (kerAevalRestrict S T hcomm (X - C (2 : ℚ)))
      (d := 135) (t := 11) (by norm_num) hprincipalSq hprincipal
      (by norm_num)

/-- Hence the residual restriction has an asymmetric irreducible
characteristic factor, the algebraic seed of a second square-carrying
frequency orbit. -/
theorem exists_asymmetric_residual_factor_oneTwentyThree
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S) (r : ℚ[X])
    (hcop : IsCoprime (X - C (2 : ℚ)) r)
    (hann : aeval T ((X - C (2 : ℚ)) * r) = 0)
    (hsq : S * S = (123 : ℚ) • (1 : E →ₗ[ℚ] E) - T)
    (htrace : LinearMap.trace ℚ E S = -(135 : ℚ)) :
    ∃ q : ℚ[X], Irreducible q ∧ q.Monic ∧
      q ∣ (kerAevalRestrict S T hcomm r).charpoly ∧
        Polynomial.signedReflection q ≠ q := by
  apply exists_asymmetric_factor_of_kerAevalRestrict_trace_ne_zero
  exact residual_trace_ne_zero_of_sq_oneTwentyThree_of_trace_neg135
    S T hcomm r hcop hann hsq htrace

end

end Erdos85
