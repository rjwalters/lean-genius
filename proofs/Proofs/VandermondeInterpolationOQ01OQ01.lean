/-
  Explicit Lagrange interpolant realizes the unique polynomial interpolant.

  Over a field `F`, fix `n` DISTINCT nodes `v : Fin n → F` and target values
  `r : Fin n → F`.  The companion entry `VandermondeInterpolationOQ01` proves
  the *uniqueness* half of the interpolation problem (via the nonvanishing of
  the Vandermonde determinant): a polynomial of degree `< n` is determined by
  its values at `n` distinct points.  This file supplies the complementary
  *existence* half and packages the two together into a clean well-posedness
  statement.

  The existence witness is the explicit **Lagrange interpolant**
  `interp v r = ∑ i, r i · ℓ_i`, where `ℓ_i` is the `i`-th Lagrange basis
  polynomial.  We show:

    * **Existence (the realizer)** `eval_interp`: the Lagrange interpolant takes
      the prescribed value `r j` at every node `v j`;
    * **Degree bound** `degree_interp_lt` / `natDegree_interp_lt`: it has degree
      `< n`;
    * **It is the answer** `eq_interp_of_eval_eq`: *any* polynomial of degree
      `< n` matching the values equals the Lagrange interpolant;
    * **Well-posedness** `existsUnique_interp` (degree form) and
      `existsUnique_interp_natDegree` (the `natDegree` form matching the
      companion): there is a *unique* polynomial of degree `< n` interpolating
      the data, and it is exactly the Lagrange interpolant;
    * **Reproduction** `interp_eval_self`: interpolating the values of a
      polynomial of degree `< n` returns that polynomial — Lagrange
      interpolation is a left inverse to evaluation on `degree < n` polynomials.

  The mathematical engine is Mathlib's `Lagrange.*` API
  (`eval_interpolate_at_node`, `degree_interpolate_lt`,
  `eq_interpolate_of_eval_eq`); the contribution here is to recast it in the
  `Fin n` / `Function.Injective` / `natDegree` idiom of the companion entry and
  to expose the interpolation problem's existence-and-uniqueness explicitly.
  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Polynomial Finset

namespace VandermondeInterpolationOQ01OQ01

variable {F : Type*} [Field F] {n : ℕ} {v : Fin n → F} {r : Fin n → F}

omit [Field F] in
/-- A globally injective node map is injective on `univ`. -/
private theorem injOn_univ (hv : Function.Injective v) :
    Set.InjOn v ↑(Finset.univ : Finset (Fin n)) := hv.injOn

/-- The number of nodes is `n`. -/
private theorem card_univ_fin : #(Finset.univ : Finset (Fin n)) = n := by simp

/-- The explicit **Lagrange interpolant** through the nodes `v` with values `r`. -/
noncomputable def interp (v r : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ v r

/-- **Existence (the realizer).** The Lagrange interpolant takes the prescribed
value `r j` at each node `v j`. -/
theorem eval_interp (hv : Function.Injective v) (j : Fin n) :
    (interp v r).eval (v j) = r j := by
  unfold interp
  exact Lagrange.eval_interpolate_at_node r (injOn_univ hv) (mem_univ j)

/-- The Lagrange interpolant has degree `< n`. -/
theorem degree_interp_lt (hv : Function.Injective v) :
    (interp v r).degree < (n : ℕ) := by
  have h := Lagrange.degree_interpolate_lt (v := v) (r := r) (injOn_univ hv)
  rwa [card_univ_fin] at h

/-- If `p` has degree `< n`, then `natDegree p < n`. -/
private theorem natDegree_lt_of_degree_lt {p : F[X]} (h : p.degree < (n : ℕ))
    (hn : 0 < n) : p.natDegree < n := by
  rcases eq_or_ne p 0 with rfl | hp
  · simpa using hn
  · rwa [degree_eq_natDegree hp, Nat.cast_lt] at h

/-- If `natDegree p < n`, then `p` has degree `< n`. -/
private theorem degree_lt_of_natDegree_lt {p : F[X]} (h : p.natDegree < n) :
    p.degree < (n : ℕ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [degree_eq_natDegree hp, Nat.cast_lt]; exact h

/-- For `n ≥ 1` the Lagrange interpolant has `natDegree < n` (the idiom of the
companion entry). -/
theorem natDegree_interp_lt (hv : Function.Injective v) (hn : 0 < n) :
    (interp v r).natDegree < n :=
  natDegree_lt_of_degree_lt (degree_interp_lt hv) hn

/-- **The interpolant is the answer.** Any polynomial of degree `< n` that
matches the prescribed values at the nodes equals the Lagrange interpolant. -/
theorem eq_interp_of_eval_eq (hv : Function.Injective v) {p : F[X]}
    (hdeg : p.degree < (n : ℕ)) (hp : ∀ j, p.eval (v j) = r j) :
    p = interp v r := by
  unfold interp
  refine Lagrange.eq_interpolate_of_eval_eq r (injOn_univ hv) ?_ ?_
  · rwa [card_univ_fin]
  · intro i _; exact hp i

/-- **Well-posedness (degree form).** There is a unique polynomial of degree
`< n` interpolating the data, and it is the Lagrange interpolant. -/
theorem existsUnique_interp (hv : Function.Injective v) :
    ∃! p : F[X], p.degree < (n : ℕ) ∧ ∀ j, p.eval (v j) = r j := by
  refine ⟨interp v r, ⟨degree_interp_lt hv, eval_interp hv⟩, ?_⟩
  rintro q ⟨hqdeg, hqeval⟩
  exact eq_interp_of_eval_eq hv hqdeg hqeval

/-- **Well-posedness (`natDegree` form, `n ≥ 1`).** Mirrors the companion
entry's `natDegree < n` framing: there is a unique polynomial of `natDegree < n`
interpolating the data. -/
theorem existsUnique_interp_natDegree (hv : Function.Injective v) (hn : 0 < n) :
    ∃! p : F[X], p.natDegree < n ∧ ∀ j, p.eval (v j) = r j := by
  refine ⟨interp v r, ⟨natDegree_interp_lt hv hn, eval_interp hv⟩, ?_⟩
  rintro q ⟨hqdeg, hqeval⟩
  exact eq_interp_of_eval_eq hv (degree_lt_of_natDegree_lt hqdeg) hqeval

/-- **Reproduction.** Interpolating the values of a polynomial of degree `< n`
returns the polynomial: Lagrange interpolation is a left inverse to evaluation
on polynomials of degree `< n`. -/
theorem interp_eval_self (hv : Function.Injective v) {f : F[X]}
    (hdeg : f.degree < (n : ℕ)) :
    interp v (fun i => f.eval (v i)) = f :=
  (eq_interp_of_eval_eq hv hdeg (fun _ => rfl)).symm

/-- The Lagrange interpolant is `F`-linear in the value vector `r`. -/
theorem interp_add (v : Fin n → F) (r r' : Fin n → F) :
    interp v (r + r') = interp v r + interp v r' := by
  unfold interp; exact map_add _ r r'

/-- The Lagrange interpolant commutes with scalar multiplication of the data. -/
theorem interp_smul (v : Fin n → F) (c : F) (r : Fin n → F) :
    interp v (c • r) = c • interp v r := by
  unfold interp; exact map_smul _ c r

end VandermondeInterpolationOQ01OQ01
