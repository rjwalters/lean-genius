import Mathlib

/-!
# Eigenpairs for a shifted defect operator

If `A² = κI - T`, every `A`-eigenvector is automatically a `T`-eigenvector.
When `T = D - J` and `J T = δ J`, every nonprincipal `T`-eigenvector is
annihilated by `J`, hence is also a `D = T + J` eigenvector.
-/

namespace Erdos85

noncomputable section

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- **Shifted-defect eigenpair bridge.**  Under `A² = κI - T`, an
`A`-eigenvalue `θ` pairs with the `T`-eigenvalue `κ-θ²`.  If this is not
the distinguished value `δ` on which `J` can survive, then `Jw=0`, so the
same vector is an eigenvector of the unshifted operator `T+J`. -/
theorem shiftedDefect_eigenpair_of_adjacency_eigenpair
    (A T J : E →ₗ[K] E) {κ δ θ : K} {w : E}
    (hsq : A * A = κ • (1 : E →ₗ[K] E) - T)
    (hJT : J * T = δ • J)
    (heigen : A w = θ • w)
    (hpair_ne : κ - θ ^ 2 ≠ δ) :
    T w = (κ - θ ^ 2) • w ∧
      J w = 0 ∧
      (T + J) w = (κ - θ ^ 2) • w := by
  have hsquare := LinearMap.congr_fun hsq w
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, heigen, map_smul] at hsquare
  have hT : T w = (κ - θ ^ 2) • w := by
    rw [sub_smul, pow_two, mul_smul]
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using (eq_sub_iff_add_eq.mp hsquare)
  have hJ : J w = 0 := by
    have h := LinearMap.congr_fun hJT w
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hT, map_smul] at h
    have hz : ((κ - θ ^ 2) - δ) • J w = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr h
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hpair_ne)
  refine ⟨hT, hJ, ?_⟩
  simp [hT, hJ]

#print axioms shiftedDefect_eigenpair_of_adjacency_eigenpair

end

end Erdos85
