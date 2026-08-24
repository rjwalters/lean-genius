import Proofs.Erdos85PureEndpointExteriorMinimalEvenConfiguration

/-!
# Kernel rigidity of a minimal binary even configuration

A support-minimal nonzero binary dependence is a circuit.  Consequently the
incidence kernel restricted to its support contains only zero and the
all-ones circuit vector.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Every binary incidence-kernel vector on a support-minimal pointwise-even
configuration is either zero or the all-ones vector. -/
theorem minimal_even_configuration_kernelVector_eq_zero_or_one
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (hminimal : ∀ U : Finset α, U ⊂ Finset.univ → U.Nonempty →
      ¬ ∀ y : β, Even ((U.filter fun a => Inc a y).card))
    (x : α → ZMod 2)
    (hx : ∀ y : β,
      ∑ a : α, (if Inc a y then x a else 0) = 0) :
    x = 0 ∨ x = 1 := by
  classical
  by_cases hxzero : x = 0
  · exact Or.inl hxzero
  right
  let U := (Finset.univ : Finset α).filter fun a => x a = 1
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hval : ∀ a : α, x a = if a ∈ U then 1 else 0 := by
    intro a
    rcases hbinary (x a) with ha0 | ha1
    · simp [U, ha0]
    · simp [U, ha1]
  have hU : U.Nonempty := by
    by_contra hUnon
    apply hxzero
    funext a
    have haU : a ∉ U := by
      rw [Finset.not_nonempty_iff_eq_empty] at hUnon
      simp [hUnon]
    simp [hval a, haU]
  have hUeven : ∀ y : β, Even ((U.filter fun a => Inc a y).card) := by
    intro y
    have hy := hx y
    simp_rw [hval] at hy
    have hcast : (((U.filter fun a => Inc a y).card : ℕ) : ZMod 2) = 0 := by
      calc
        (((U.filter fun a => Inc a y).card : ℕ) : ZMod 2) =
            ∑ a ∈ (U.filter fun a => Inc a y), (1 : ZMod 2) := by simp
        _ = ∑ a ∈ U, if Inc a y then (1 : ZMod 2) else 0 := by
          rw [Finset.sum_filter]
        _ = ∑ a : α, if a ∈ U then
              (if Inc a y then (1 : ZMod 2) else 0) else 0 := by
          calc
            (∑ a ∈ U, if Inc a y then (1 : ZMod 2) else 0) =
                ∑ a ∈ U, if a ∈ U then
                  (if Inc a y then (1 : ZMod 2) else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro a haU
              simp [haU]
            _ = ∑ a ∈ (Finset.univ : Finset α), if a ∈ U then
                  (if Inc a y then (1 : ZMod 2) else 0) else 0 := by
              apply Finset.sum_subset (Finset.subset_univ U)
              intro a _haUniv haU
              simp [haU]
            _ = _ := by rfl
        _ = ∑ a : α, if Inc a y then
              (if a ∈ U then (1 : ZMod 2) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          by_cases haU : a ∈ U <;>
            by_cases hay : Inc a y <;> simp [haU, hay]
        _ = 0 := hy
    exact ZMod.natCast_eq_zero_iff_even.mp hcast
  have hUeq : U = (Finset.univ : Finset α) := by
    apply Finset.eq_univ_of_forall
    intro a
    by_contra ha
    have hproper : U ⊂ (Finset.univ : Finset α) :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ U, fun hEq => ha (by simp [hEq])⟩
    exact hminimal U hproper hU hUeven
  funext a
  have haU : a ∈ U := by simp [hUeq]
  simpa [haU] using hval a

/-- Matrix form: the incidence kernel of a nonempty minimal even
configuration is exactly the line spanned by the all-ones circuit vector,
and therefore has finrank one. -/
theorem minimal_even_configuration_kernel_eq_span_one
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (heven : ∀ y : β,
      Even (((Finset.univ : Finset α).filter fun a => Inc a y).card))
    (hminimal : ∀ U : Finset α, U ⊂ Finset.univ → U.Nonempty →
      ¬ ∀ y : β, Even ((U.filter fun a => Inc a y).card)) :
    let M : Matrix β α (ZMod 2) := fun y a => if Inc a y then 1 else 0
    LinearMap.ker M.mulVecLin = (ZMod 2) ∙ (1 : α → ZMod 2) ∧
      Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = 1 := by
  classical
  dsimp only
  let M : Matrix β α (ZMod 2) := fun y a => if Inc a y then 1 else 0
  have honeKer : (1 : α → ZMod 2) ∈ LinearMap.ker M.mulVecLin := by
    rw [LinearMap.mem_ker]
    funext y
    have hcast :
        (((((Finset.univ : Finset α).filter fun a => Inc a y).card : ℕ) :
          ZMod 2)) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr (heven y)
    simp only [Pi.zero_apply]
    change M.mulVec (1 : α → ZMod 2) y = 0
    simpa [M, Matrix.mulVec, dotProduct] using hcast
  have hker : LinearMap.ker M.mulVecLin =
      (ZMod 2) ∙ (1 : α → ZMod 2) := by
    apply le_antisymm
    · intro x hxker
      have hxsum : ∀ y : β,
          ∑ a : α, (if Inc a y then x a else 0) = 0 := by
        intro y
        have h := congrFun (LinearMap.mem_ker.mp hxker) y
        simpa [M, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul] using h
      rcases minimal_even_configuration_kernelVector_eq_zero_or_one
          Inc hminimal x hxsum with rfl | rfl
      · exact Submodule.zero_mem _
      · exact Submodule.subset_span (Set.mem_singleton _)
    · apply Submodule.span_le.mpr
      intro x hx
      have hxone : x = (1 : α → ZMod 2) := by simpa using hx
      simpa [hxone] using honeKer
  refine ⟨hker, ?_⟩
  rw [hker]
  apply finrank_span_singleton
  exact one_ne_zero

end

end Erdos85

#print axioms Erdos85.minimal_even_configuration_kernelVector_eq_zero_or_one
#print axioms Erdos85.minimal_even_configuration_kernel_eq_span_one
