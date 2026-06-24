/-
  The Lagrange basis polynomials as a *basis* of the degree-`< n` polynomials.

  Fix `n` DISTINCT nodes `v : Fin n → F` over a field `F`.  The companion entry
  `VandermondeInterpolationOQ01OQ02` packages the two halves of the interpolation
  problem (existence + uniqueness) into a single linear isomorphism

      `evalEquiv : degreeLT F n ≃ₗ[F] (Fin n → F)`,   `p ↦ (j ↦ p.eval (v j))`,

  whose inverse is the explicit Lagrange interpolant.  This entry transports the
  *standard basis* of `Fin n → F` across that isomorphism to obtain a concrete
  basis of the polynomial space `degreeLT F n`:

      `lagrangeBasis : Basis (Fin n) F (degreeLT F n)`,

  whose `j`-th vector is exactly Mathlib's Lagrange basis polynomial
  `Lagrange.basis univ v j` (`lagrangeBasis_coe`).

  The structural payoff is the **interpolation reading of the coordinates**:

      `(lagrangeBasis).repr p j = (p : F[X]).eval (v j)`   (`lagrangeBasis_repr`),

  i.e. the coordinate of a degree-`< n` polynomial in the Lagrange basis is
  simply its value at the corresponding node.  Equivalently every such `p` is the
  interpolation sum of its node values (`degreeLT_eq_node_sum`).  The defining
  Kronecker-delta property `(lagrangeBasis j).eval (v k) = [j = k]`
  (`eval_lagrangeBasis`) exhibits this basis as the dual of the evaluation
  functionals.

  The file is self-contained: the small interpolation isomorphism is rebuilt here
  (mirroring the companion entry) so the basis result can be checked in isolation.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Polynomial Finset

namespace VandermondeInterpolationOQ01OQ02OQ01

variable {F : Type*} [Field F] {n : ℕ} {v : Fin n → F}

/-! ### The interpolation isomorphism (self-contained companion of OQ01OQ02) -/

/-- The number of nodes is `n`. -/
private theorem card_univ_fin : #(univ : Finset (Fin n)) = n := by simp

/-- The Lagrange interpolant lands in `degreeLT F n` (degree `< n`). -/
theorem interp_mem_degreeLT (hv : Function.Injective v) (r : Fin n → F) :
    Lagrange.interpolate univ v r ∈ degreeLT F n := by
  rw [mem_degreeLT]
  have h := Lagrange.degree_interpolate_lt (s := univ) (v := v) (r := r) hv.injOn
  rwa [card_univ_fin] at h

/-- The **evaluation map** `p ↦ (j ↦ p.eval (v j))` as an `F`-linear map. -/
def evalNodes (v : Fin n → F) : degreeLT F n →ₗ[F] (Fin n → F) :=
  LinearMap.pi fun j => (Polynomial.leval (v j)).comp (degreeLT F n).subtype

@[simp] theorem evalNodes_apply (v : Fin n → F) (p : degreeLT F n) (j : Fin n) :
    evalNodes v p j = (p : F[X]).eval (v j) := rfl

/-- The Lagrange interpolant as an `F`-linear map into `degreeLT F n`. -/
noncomputable def interpLT (hv : Function.Injective v) :
    (Fin n → F) →ₗ[F] degreeLT F n :=
  LinearMap.codRestrict _ (Lagrange.interpolate univ v) (interp_mem_degreeLT hv)

/-- The evaluation map is a linear isomorphism `degreeLT F n ≃ₗ[F] (Fin n → F)`,
with inverse the Lagrange interpolant. -/
noncomputable def evalEquiv (hv : Function.Injective v) :
    degreeLT F n ≃ₗ[F] (Fin n → F) :=
  LinearEquiv.ofLinear (evalNodes v) (interpLT hv)
    (by
      refine LinearMap.ext fun r => funext fun j => ?_
      show (Lagrange.interpolate univ v r).eval (v j) = r j
      exact Lagrange.eval_interpolate_at_node r hv.injOn (mem_univ j))
    (by
      refine LinearMap.ext fun p => Subtype.ext ?_
      have hdeg : (p : F[X]).degree < #(univ : Finset (Fin n)) := by
        rw [card_univ_fin]; exact mem_degreeLT.1 p.2
      exact (Lagrange.eq_interpolate hv.injOn hdeg).symm)

@[simp] theorem evalEquiv_apply (hv : Function.Injective v) (p : degreeLT F n) :
    evalEquiv hv p = evalNodes v p := rfl

@[simp] theorem evalEquiv_symm_apply (hv : Function.Injective v) (r : Fin n → F) :
    ((evalEquiv hv).symm r : F[X]) = Lagrange.interpolate univ v r := rfl

/-! ### The Lagrange basis -/

/-- The **Lagrange basis** of `degreeLT F n`: the image of the standard basis of
`Fin n → F` under the inverse evaluation isomorphism.  Its vectors are the
Lagrange basis polynomials. -/
noncomputable def lagrangeBasis (hv : Function.Injective v) :
    Module.Basis (Fin n) F (degreeLT F n) :=
  (Pi.basisFun F (Fin n)).map (evalEquiv hv).symm

@[simp] theorem lagrangeBasis_apply (hv : Function.Injective v) (j : Fin n) :
    lagrangeBasis hv j = (evalEquiv hv).symm (Pi.single j 1) := by
  simp only [lagrangeBasis, Module.Basis.map_apply, Pi.basisFun_apply]

/-- The `j`-th vector of `lagrangeBasis` is Mathlib's Lagrange basis polynomial
`Lagrange.basis univ v j`. -/
theorem lagrangeBasis_coe (hv : Function.Injective v) (j : Fin n) :
    ((lagrangeBasis hv j : degreeLT F n) : F[X]) = Lagrange.basis univ v j := by
  rw [lagrangeBasis_apply, evalEquiv_symm_apply, Lagrange.interpolate_apply,
    Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro h; exact absurd (mem_univ j) h

/-- **Kronecker-delta property.** The `j`-th Lagrange basis polynomial takes the
value `1` at node `v j` and `0` at the other nodes — it is dual to the evaluation
functionals. -/
theorem eval_lagrangeBasis (hv : Function.Injective v) (j k : Fin n) :
    ((lagrangeBasis hv j : degreeLT F n) : F[X]).eval (v k) = if j = k then 1 else 0 := by
  rw [lagrangeBasis_coe]
  by_cases h : j = k
  · subst h; rw [if_pos rfl, Lagrange.eval_basis_self hv.injOn (mem_univ j)]
  · rw [if_neg h, Lagrange.eval_basis_of_ne h (mem_univ k)]

/-- **Interpolation reading of the coordinates.** The coordinate of a degree-`< n`
polynomial in the Lagrange basis is its value at the corresponding node. -/
@[simp] theorem lagrangeBasis_repr (hv : Function.Injective v) (p : degreeLT F n)
    (j : Fin n) : (lagrangeBasis hv).repr p j = (p : F[X]).eval (v j) := by
  simp only [lagrangeBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, Pi.basisFun_repr, evalEquiv_apply, evalNodes_apply]

/-- Every degree-`< n` polynomial is the interpolation sum of its node values
against the Lagrange basis. -/
theorem degreeLT_eq_node_sum (hv : Function.Injective v) (p : degreeLT F n) :
    ∑ j, (p : F[X]).eval (v j) • lagrangeBasis hv j = p := by
  conv_rhs => rw [← (lagrangeBasis hv).sum_repr p]
  exact Finset.sum_congr rfl fun j _ => by rw [lagrangeBasis_repr]

/-- The Lagrange basis polynomials are linearly independent. -/
theorem lagrangeBasis_linearIndependent (hv : Function.Injective v) :
    LinearIndependent F (lagrangeBasis hv) := (lagrangeBasis hv).linearIndependent

/-- The Lagrange basis polynomials span `degreeLT F n`. -/
theorem lagrangeBasis_span (hv : Function.Injective v) :
    Submodule.span F (Set.range (lagrangeBasis hv)) = ⊤ := (lagrangeBasis hv).span_eq

/-- **Structural consequence.** The space of degree-`< n` polynomials has dimension
`n`, witnessed concretely by the `n` Lagrange basis polynomials. -/
theorem finrank_degreeLT (hv : Function.Injective v) :
    Module.finrank F (degreeLT F n) = n := by
  rw [Module.finrank_eq_card_basis (lagrangeBasis hv), Fintype.card_fin]

end VandermondeInterpolationOQ01OQ02OQ01
