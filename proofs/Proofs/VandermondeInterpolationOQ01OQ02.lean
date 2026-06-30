/-
  The evaluation-at-nodes map is a linear ISOMORPHISM: the full interpolation
  isomorphism via the explicit Lagrange interpolant.

  Fix `n` DISTINCT nodes `v : Fin n → F` over a field `F`.  The two companion
  entries supply the two halves of the interpolation problem:

    * `VandermondeInterpolationOQ01` — *uniqueness* (Vandermonde nonvanishing):
      a polynomial of degree `< n` is determined by its values at the nodes;
    * `VandermondeInterpolationOQ01OQ01` — *existence* (the explicit Lagrange
      interpolant `interp v r` realizes any prescribed value vector `r`).

  This entry packages the two halves into a single structural object: the
  **evaluation map**

      `evalNodes v : degreeLT F n →ₗ[F] (Fin n → F)`,  `p ↦ (j ↦ p.eval (v j))`

  is a *linear isomorphism* `evalEquiv`, whose inverse is exactly the Lagrange
  interpolant `interp v`.  Equivalently:

    * **Surjectivity (existence half)** `evalNodes_surjective` /
      `exists_eval_eq`: every value vector is hit by some degree `< n` polynomial;
    * **Injectivity (uniqueness half)** `evalNodes_injective`;
    * **Bijectivity / isomorphism** `evalEquiv`, with the explicit two-sided
      inverse `interp v` (`evalEquiv_symm_apply`);
    * **Structural consequence** `finrank_degreeLT`: the space of polynomials of
      degree `< n` has dimension `n` (transported across the isomorphism).

  Mathlib already has `Lagrange.funEquivDegreeLT : degreeLT F #s ≃ₗ[F] ↥s → F`,
  but it is indexed by the *subtype* `↥s` and its inverse carries a `dite` guard
  (`if hx : x ∈ s then r ⟨x, hx⟩ else 0`).  The contribution here is the clean
  `Fin n → F` form matching the companion entries, with the honest companion
  interpolant `interp v` (no `dite`) as the explicit two-sided inverse, and the
  existence/surjectivity statement exposed standalone.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Polynomial Finset

namespace VandermondeInterpolationOQ01OQ02

variable {F : Type*} [Field F] {n : ℕ} {v : Fin n → F}

/-- The number of nodes is `n`. -/
private theorem card_univ_fin : #(univ : Finset (Fin n)) = n := by simp

/-- The explicit **Lagrange interpolant** through the nodes `v` with values `r`
(the same interpolant as the companion entry). -/
noncomputable def interp (v r : Fin n → F) : F[X] :=
  Lagrange.interpolate univ v r

/-- The Lagrange interpolant lands in `degreeLT F n` (degree `< n`). -/
theorem interp_mem_degreeLT (hv : Function.Injective v) (r : Fin n → F) :
    Lagrange.interpolate univ v r ∈ degreeLT F n := by
  rw [mem_degreeLT]
  have h := Lagrange.degree_interpolate_lt (s := univ) (v := v) (r := r) hv.injOn
  rwa [card_univ_fin] at h

/-- **The evaluation-at-nodes map** `p ↦ (j ↦ p.eval (v j))`, as an `F`-linear
map on the space of polynomials of degree `< n`. -/
def evalNodes (v : Fin n → F) : degreeLT F n →ₗ[F] (Fin n → F) :=
  LinearMap.pi fun j => (Polynomial.leval (v j)).comp (degreeLT F n).subtype

@[simp] theorem evalNodes_apply (v : Fin n → F) (p : degreeLT F n) (j : Fin n) :
    evalNodes v p j = (p : F[X]).eval (v j) := rfl

/-- The Lagrange interpolant, as an `F`-linear map `(Fin n → F) →ₗ[F] degreeLT F n`
(the codomain-restricted `Lagrange.interpolate`). -/
noncomputable def interpLT (hv : Function.Injective v) :
    (Fin n → F) →ₗ[F] degreeLT F n :=
  LinearMap.codRestrict _ (Lagrange.interpolate univ v) (interp_mem_degreeLT hv)

@[simp] theorem interpLT_coe (hv : Function.Injective v) (r : Fin n → F) :
    (interpLT hv r : F[X]) = interp v r := rfl

/-- **The full interpolation isomorphism.** Evaluation at `n` distinct nodes is
a linear isomorphism `degreeLT F n ≃ₗ[F] (Fin n → F)`, whose inverse is the
explicit Lagrange interpolant. -/
noncomputable def evalEquiv (hv : Function.Injective v) :
    degreeLT F n ≃ₗ[F] (Fin n → F) :=
  LinearEquiv.ofLinear (evalNodes v) (interpLT hv)
    (by
      -- `evalNodes ∘ interpLT = id`: the interpolant realizes the values
      refine LinearMap.ext fun r => funext fun j => ?_
      show (Lagrange.interpolate univ v r).eval (v j) = r j
      exact Lagrange.eval_interpolate_at_node r hv.injOn (mem_univ j))
    (by
      -- `interpLT ∘ evalNodes = id`: a degree `< n` polynomial is its own interpolant
      refine LinearMap.ext fun p => Subtype.ext ?_
      have hdeg : (p : F[X]).degree < #(univ : Finset (Fin n)) := by
        rw [card_univ_fin]; exact mem_degreeLT.1 p.2
      exact (Lagrange.eq_interpolate hv.injOn hdeg).symm)

@[simp] theorem evalEquiv_apply (hv : Function.Injective v) (p : degreeLT F n) :
    evalEquiv hv p = evalNodes v p := rfl

@[simp] theorem evalEquiv_symm_apply (hv : Function.Injective v) (r : Fin n → F) :
    ((evalEquiv hv).symm r : F[X]) = interp v r := rfl

/-- The evaluation map is **bijective** (the interpolation problem is well-posed). -/
theorem evalNodes_bijective (hv : Function.Injective v) :
    Function.Bijective (evalNodes v) := (evalEquiv hv).bijective

/-- **Surjectivity — the existence half.** Every value vector is the
evaluation-at-nodes of some polynomial of degree `< n`. -/
theorem evalNodes_surjective (hv : Function.Injective v) :
    Function.Surjective (evalNodes v) := (evalEquiv hv).surjective

/-- **Injectivity — the uniqueness half.** A polynomial of degree `< n` is
determined by its values at the nodes. -/
theorem evalNodes_injective (hv : Function.Injective v) :
    Function.Injective (evalNodes v) := (evalEquiv hv).injective

/-- **Existence (concrete form).** For any target values `r` there is a
polynomial of degree `< n` interpolating the data — the Lagrange interpolant. -/
theorem exists_eval_eq (hv : Function.Injective v) (r : Fin n → F) :
    ∃ p : F[X], p.degree < (n : ℕ) ∧ ∀ j, p.eval (v j) = r j := by
  refine ⟨interp v r, ?_, fun j => ?_⟩
  · have h := Lagrange.degree_interpolate_lt (s := univ) (v := v) (r := r) hv.injOn
    rwa [card_univ_fin] at h
  · exact Lagrange.eval_interpolate_at_node r hv.injOn (mem_univ j)

/-- **Structural consequence.** Transporting the isomorphism, the space of
polynomials of degree `< n` over `F` has dimension `n`. -/
theorem finrank_degreeLT (hv : Function.Injective v) :
    Module.finrank F (degreeLT F n) = n := by
  rw [(evalEquiv hv).finrank_eq, Module.finrank_fin_fun]

end VandermondeInterpolationOQ01OQ02
