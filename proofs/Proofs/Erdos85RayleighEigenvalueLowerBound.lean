import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# A finite-dimensional Rayleigh eigenvalue lower bound

The supremum of the Rayleigh quotient of a real symmetric operator is an
eigenvalue.  The convenient consumer form below compares that eigenvalue to
the quotient at one explicitly chosen nonzero vector.
-/

namespace Erdos85

noncomputable section

theorem exists_eigenvalue_ge_rayleigh
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (v : E) (hv : v ≠ 0) :
    ∃ mu : ℝ,
      Module.End.HasEigenvalue T mu ∧
      @inner ℝ E _ v (T v) / ‖v‖ ^ 2 ≤ mu := by
  let q : {x : E // x ≠ 0} → ℝ :=
    fun x => @inner ℝ E _ x (T x) / ‖(x : E)‖ ^ 2
  let mu : ℝ := ⨆ x, q x
  have heig : Module.End.HasEigenvalue T mu := by
    simpa [mu, q, real_inner_comm] using
      hT.hasEigenvalue_iSup_of_finiteDimensional
  have hbounded : BddAbove (Set.range q) := by
    let Tc := hT.toSelfAdjoint
    refine ⟨‖Tc.1‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    have habs := Tc.1.rayleighQuotient_le_norm (x : E)
    dsimp [q]
    have hq :
        @inner ℝ E _ (x : E) (T x) / ‖(x : E)‖ ^ 2 =
          Tc.1.rayleighQuotient (x : E) := by
      rw [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply]
      dsimp [Tc]
      change @inner ℝ E _ (x : E) (T x) / ‖(x : E)‖ ^ 2 =
        @inner ℝ E _ (T x) (x : E) / ‖(x : E)‖ ^ 2
      rw [real_inner_comm]
    rw [hq]
    exact le_trans (le_abs_self _) habs
  refine ⟨mu, heig, ?_⟩
  have hle : q ⟨v, hv⟩ ≤ ⨆ x, q x :=
    le_ciSup hbounded ⟨v, hv⟩
  simpa [mu, q] using hle

end

end Erdos85
