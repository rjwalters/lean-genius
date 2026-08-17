import Proofs.Erdos85QuadraticTrace

/-!
# Dimension bound for a square-scalar trace sector

If a rational endomorphism squares to `t² I`, its eigenvalues are `±t`.
Consequently a sector contributing trace `-d` must have dimension at least
`d / t`.  The proof below uses the same rational idempotent as
`LinearMap.exists_int_mul_eq_trace_of_sq_eq_square_nat`, avoiding any choice
of eigenbasis.
-/

namespace Erdos85

noncomputable section

/-- A rational square-scalar sector carrying trace `-d` has enough dimension
to support that trace: `d ≤ t * finrank E`. -/
theorem nat_le_mul_finrank_of_trace_eq_neg_of_sq_eq_square_nat
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E) {d t : ℕ} (ht : 0 < t)
    (hT : T * T = ((t * t : ℕ) : ℚ) • LinearMap.id)
    (htrace : LinearMap.trace ℚ E T = -(d : ℚ)) :
    d ≤ t * Module.finrank ℚ E := by
  let S : E →ₗ[ℚ] E := (t : ℚ)⁻¹ • T
  let P : E →ₗ[ℚ] E := (2 : ℚ)⁻¹ • (LinearMap.id + S)
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hS : S * S = LinearMap.id := by
    ext x
    have hx := LinearMap.congr_fun hT x
    change (t : ℚ)⁻¹ • T ((t : ℚ)⁻¹ • T x) = x
    rw [map_smul, smul_smul]
    change ((t : ℚ)⁻¹ * (t : ℚ)⁻¹) • (T * T) x = x
    rw [hx]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    change (((t : ℚ)⁻¹ * (t : ℚ)⁻¹) * (t * t : ℕ)) • x = x
    have hc : (t : ℚ)⁻¹ * (t : ℚ)⁻¹ * (t * t : ℕ) = 1 := by
      push_cast
      field_simp
    rw [hc, one_smul]
  have hP : IsIdempotentElem P := by
    rw [IsIdempotentElem]
    ext x
    have hsx : S (S x) = x := by
      simpa only [Module.End.mul_apply, LinearMap.id_coe, id_eq] using
        LinearMap.congr_fun hS x
    change (2 : ℚ)⁻¹ • ((2 : ℚ)⁻¹ • (x + S x) +
      S ((2 : ℚ)⁻¹ • (x + S x))) = (2 : ℚ)⁻¹ • (x + S x)
    rw [map_smul, map_add, hsx]
    module
  have hproj := LinearMap.IsIdempotentElem.isProj_range P hP
  have htraceP := hproj.trace
  have htrace_expand : LinearMap.trace ℚ E P =
      (2 : ℚ)⁻¹ * ((Module.finrank ℚ E : ℚ) +
        (t : ℚ)⁻¹ * LinearMap.trace ℚ E T) := by
    simp only [P, S, map_smul, map_add, LinearMap.trace_id]
    ring
  rw [htrace_expand, htrace] at htraceP
  have hrnonneg : (0 : ℚ) ≤
      Module.finrank ℚ (LinearMap.range P) := by positivity
  have hboundQ : (d : ℚ) ≤
      (t : ℚ) * (Module.finrank ℚ E : ℚ) := by
    field_simp at htraceP
    nlinarith
  exact_mod_cast hboundQ

/-- In particular, a square-four sector with trace `-8` has dimension at
least four.  This is the exceptional-sector multiplicity threshold used by
the order-64 seven-component trace analysis. -/
theorem four_le_finrank_of_sq_eq_four_of_trace_eq_neg_eight
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E)
    (hT : T * T = (4 : ℚ) • LinearMap.id)
    (htrace : LinearMap.trace ℚ E T = -(8 : ℚ)) :
    4 ≤ Module.finrank ℚ E := by
  have h := nat_le_mul_finrank_of_trace_eq_neg_of_sq_eq_square_nat
    T (d := 8) (t := 2) (by norm_num) (by norm_num at hT ⊢; exact hT) htrace
  omega

end

end Erdos85
