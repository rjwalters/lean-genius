import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Trace

/-!
# Trace and characteristic polynomial across an invariant direct sum

The spectral obstructions for the even second-order boundary split the
adjacency space into component-constant vectors and their complementary
component-orthogonal vectors.  This file isolates the linear-algebra bridge:
on two complementary invariant subspaces, both trace and characteristic
polynomial split into the corresponding restricted pieces.
-/

namespace Erdos85

open LinearMap
open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

private theorem invariant_prodMap_eq_conj
    (f : E →ₗ[K] E) (U W : Submodule K E) (hUW : IsCompl U W)
    (hU : ∀ x ∈ U, f x ∈ U) (hW : ∀ x ∈ W, f x ∈ W) :
    (f.restrict hU).prodMap (f.restrict hW) =
      (U.prodEquivOfIsCompl W hUW).symm.conj f := by
  let e := U.prodEquivOfIsCompl W hUW
  let bU := Module.Free.chooseBasis K U
  let bW := Module.Free.chooseBasis K W
  let b := bU.prod bW
  apply b.ext
  simp only [Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr,
    LinearMap.prodMap_apply, LinearEquiv.conj_apply, LinearEquiv.symm_symm,
    Submodule.coe_prodEquivOfIsCompl, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coprod_apply,
    Submodule.coe_subtype, map_add, Sum.forall, Sum.elim_inl, map_zero,
    ZeroMemClass.coe_zero, add_zero, LinearEquiv.eq_symm_apply, and_self,
    Submodule.coe_prodEquivOfIsCompl', LinearMap.coe_restrict_apply,
    hU, hW, implies_true, Sum.elim_inr, zero_add, e, b]

/-- The characteristic polynomial of an endomorphism is the product of the
characteristic polynomials of its restrictions to two complementary invariant
subspaces. -/
theorem charpoly_eq_mul_restrict_of_isCompl
    (f : E →ₗ[K] E) (U W : Submodule K E) (hUW : IsCompl U W)
    (hU : ∀ x ∈ U, f x ∈ U) (hW : ∀ x ∈ W, f x ∈ W) :
    f.charpoly = (f.restrict hU).charpoly * (f.restrict hW).charpoly := by
  let e := U.prodEquivOfIsCompl W hUW
  have hblock := invariant_prodMap_eq_conj f U W hUW hU hW
  rw [← e.symm.charpoly_conj f, ← hblock, charpoly_prodMap]

/-- Trace is additive across two complementary invariant subspaces. -/
theorem trace_eq_add_trace_restrict_of_isCompl
    (f : E →ₗ[K] E) (U W : Submodule K E) (hUW : IsCompl U W)
    (hU : ∀ x ∈ U, f x ∈ U) (hW : ∀ x ∈ W, f x ∈ W) :
    trace K E f =
      trace K U (f.restrict hU) + trace K W (f.restrict hW) := by
  let e := U.prodEquivOfIsCompl W hUW
  have hblock := invariant_prodMap_eq_conj f U W hUW hU hW
  rw [← trace_conj' f e.symm, ← hblock, trace_prodMap']

end Erdos85
