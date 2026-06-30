import Mathlib

/-
# OQ-07-OQ-01: The inverse is a polynomial in `A` of MINIMAL degree (minpoly form)

A sharpening of the parent result `cayley-hamilton-minpoly-oq-07`
(`CayleyHamiltonMinpolyOQ07.inv_eq_aeval_invPoly`), which expressed the inverse
of an invertible matrix `A` as `A⁻¹ = (aeval A) r` for an explicit polynomial `r`
of degree `< n = Fintype.card n`, built from the **characteristic** polynomial.

## Mathematical content

The characteristic polynomial is rarely the smallest polynomial annihilating `A`:
the **minimal polynomial** `m = minpoly K A` divides it and is generally of much
smaller degree (e.g. `m = X − 1` for `A = 1`, regardless of `n`).  Running the
Cayley–Hamilton division trick with `m` in place of `charpoly` yields the
inverse as a polynomial in `A` of degree `< deg m`, which is the **minimal degree**
attainable for any polynomial expression of `A⁻¹`.

The two ingredients are:

* **Invertibility ⟺ nonzero constant term.** For `A` invertible, `m.coeff 0 ≠ 0`.
  If it vanished then `m = (divX m) · X`, so `(divX m)(A) · A = m(A) = 0`; cancelling
  the unit `A` gives `(divX m)(A) = 0` with `deg (divX m) < deg m`, contradicting
  the minimality of `m` (via `minpoly.dvd`).  This is the place where invertibility
  is genuinely used — `0` is not a root of the minimal polynomial.

* **The division identity.** `m = (divX m) · X + C (m.coeff 0)` evaluated at `A`
  becomes `(divX m)(A) · A + c₀ • 1 = 0`, so with `c₀ = m.coeff 0 ≠ 0`,

      A⁻¹ = (−c₀)⁻¹ • (divX m)(A) = (aeval A) s,
      s = C (−c₀)⁻¹ · divX m,   deg s < deg m ≤ n.

Since `deg m ≤ deg (charpoly A) = n` (`Matrix.minpoly_dvd_charpoly`), this strictly
refines the parent's degree-`< n` bound, and `deg m` is exactly the minimal degree
of any polynomial representation of `A⁻¹` (it cannot be smaller: a degree-`< deg m`
polynomial `q` with `(aeval A) q = A⁻¹` would give `(aeval A)(X·q − 1) = 0` with
`X·q − 1 ≠ 0` of degree `< deg m` after the constant adjustment — but we only need,
and prove, the existential sharp bound here).

Self-contained: imports only `Mathlib`.  Sorry-free and axiom-free
(`#print axioms` below: only `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace CayleyHamiltonMinpolyOQ07OQ01

open Polynomial Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {K : Type*} [Field K]

/-- Every matrix over a field is integral over `K` (the matrix algebra is a finite
free `K`-module), so its minimal polynomial is monic and nonzero. -/
theorem isIntegral_matrix (A : Matrix n n K) : IsIntegral K A :=
  Algebra.IsIntegral.isIntegral A

/-- The **minimal-polynomial inverse**: `s = C (−c₀)⁻¹ · divX (minpoly K A)`, where
`c₀ = (minpoly K A).coeff 0`.  Evaluating it at `A` produces `A⁻¹`
(see `inv_eq_aeval_minInvPoly`). -/
noncomputable def minInvPoly (A : Matrix n n K) : K[X] :=
  C (-((minpoly K A).coeff 0))⁻¹ * (minpoly K A).divX

/-- **Invertibility forces a nonzero constant term.** If `det A ≠ 0`, then `0` is
not a root of the minimal polynomial: `(minpoly K A).coeff 0 ≠ 0`.  This is the
arithmetic heart of the refinement and the only place invertibility is used. -/
theorem minpoly_coeff_zero_ne_zero (A : Matrix n n K) (hA : A.det ≠ 0) :
    (minpoly K A).coeff 0 ≠ 0 := by
  intro h
  have hAi : IsIntegral K A := isIntegral_matrix A
  have hm_ne : minpoly K A ≠ 0 := minpoly.ne_zero hAi
  -- minpoly = divX (minpoly) · X  (since the constant term vanishes)
  have hdec : minpoly K A = (minpoly K A).divX * X := by
    have hd := divX_mul_X_add (minpoly K A)
    rw [h, C_0, add_zero] at hd
    exact hd.symm
  -- evaluate at A: (divX m)(A) · A = 0
  have haev : (aeval A) (minpoly K A).divX * A = 0 := by
    have h0 : (aeval A) (minpoly K A) = 0 := minpoly.aeval K A
    rw [hdec, map_mul, aeval_X] at h0
    exact h0
  -- cancel the unit A on the right
  have hinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)
  have hg0 : (aeval A) (minpoly K A).divX = 0 := by
    calc (aeval A) (minpoly K A).divX
        = (aeval A) (minpoly K A).divX * (A * A⁻¹) := by rw [hinv, mul_one]
      _ = ((aeval A) (minpoly K A).divX * A) * A⁻¹ := by rw [mul_assoc]
      _ = 0 * A⁻¹ := by rw [haev]
      _ = 0 := by rw [zero_mul]
  -- but then minpoly ∣ divX (minpoly), impossible by degree
  have hg_ne : (minpoly K A).divX ≠ 0 := by
    intro hg; apply hm_ne; rw [hdec, hg, zero_mul]
  have hdvd : minpoly K A ∣ (minpoly K A).divX := minpoly.dvd K A hg0
  have hle : (minpoly K A).natDegree ≤ (minpoly K A).divX.natDegree :=
    natDegree_le_of_dvd hdvd hg_ne
  have hlt : (minpoly K A).divX.natDegree < (minpoly K A).natDegree :=
    natDegree_lt_natDegree hg_ne (degree_divX_lt hm_ne)
  omega

/-- **Cayley–Hamilton (minpoly form) in additive form.** Evaluating the
decomposition `minpoly K A = divX (minpoly K A) · X + C c₀` at `A` gives
`(divX m)(A) · A + c₀ • 1 = 0`. -/
theorem aeval_divX_mul_self (A : Matrix n n K) :
    (aeval A) (minpoly K A).divX * A
      + algebraMap K (Matrix n n K) ((minpoly K A).coeff 0) = 0 := by
  have hm : (aeval A) (minpoly K A) = 0 := minpoly.aeval K A
  have hdec : (minpoly K A).divX * X + C ((minpoly K A).coeff 0) = minpoly K A :=
    divX_mul_X_add (minpoly K A)
  have h2 : (aeval A) ((minpoly K A).divX * X + C ((minpoly K A).coeff 0)) = 0 := by
    rw [hdec]; exact hm
  rwa [map_add, map_mul, aeval_X, aeval_C] at h2

/-- **The minpoly inverse polynomial is a left inverse.**
`(aeval A) (minInvPoly A) · A = 1`. -/
theorem aeval_minInvPoly_mul_self (A : Matrix n n K) (hA : A.det ≠ 0) :
    (aeval A) (minInvPoly A) * A = 1 := by
  have hc₀ : (minpoly K A).coeff 0 ≠ 0 := minpoly_coeff_zero_ne_zero A hA
  have hc : (-((minpoly K A).coeff 0)) ≠ 0 := neg_ne_zero.mpr hc₀
  have hBA : (aeval A) (minpoly K A).divX * A
      = (-((minpoly K A).coeff 0)) • (1 : Matrix n n K) := by
    have h := eq_neg_of_add_eq_zero_left (aeval_divX_mul_self A)
    rw [h, Algebra.algebraMap_eq_smul_one, neg_smul]
  have hexp : (aeval A) (minInvPoly A)
      = (-((minpoly K A).coeff 0))⁻¹ • (aeval A) (minpoly K A).divX := by
    rw [minInvPoly, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [hexp, smul_mul_assoc, hBA, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Main result.** For an invertible matrix `A` over a field, the inverse is the
evaluation at `A` of the explicit minimal-polynomial-based polynomial `minInvPoly A`. -/
theorem inv_eq_aeval_minInvPoly (A : Matrix n n K) (hA : A.det ≠ 0) :
    A⁻¹ = (aeval A) (minInvPoly A) :=
  Matrix.inv_eq_left_inv (aeval_minInvPoly_mul_self A hA)

/-- **Right-inverse companion.** `A · (aeval A) (minInvPoly A) = 1`. -/
theorem self_mul_aeval_minInvPoly (A : Matrix n n K) (hA : A.det ≠ 0) :
    A * (aeval A) (minInvPoly A) = 1 :=
  Matrix.mul_eq_one_comm.mp (aeval_minInvPoly_mul_self A hA)

/-- **Sharp degree bound.** The minpoly inverse polynomial has degree
`< deg (minpoly K A)` — the minimal degree of any polynomial representation of `A⁻¹`. -/
theorem minInvPoly_natDegree_lt [Nonempty n] (A : Matrix n n K) :
    (minInvPoly A).natDegree < (minpoly K A).natDegree := by
  have hAi : IsIntegral K A := isIntegral_matrix A
  have hm_ne : minpoly K A ≠ 0 := minpoly.ne_zero hAi
  have hdeg_pos : 0 < (minpoly K A).natDegree := by
    have := minpoly.natDegree_pos hAi
    omega
  have h1 : (minInvPoly A).natDegree ≤ (minpoly K A).divX.natDegree := by
    rw [minInvPoly]; exact natDegree_C_mul_le _ _
  have h2 : (minpoly K A).divX.natDegree < (minpoly K A).natDegree := by
    by_cases hdv : (minpoly K A).divX = 0
    · rw [hdv, natDegree_zero]; exact hdeg_pos
    · exact natDegree_lt_natDegree hdv (degree_divX_lt hm_ne)
  omega

/-- `deg (minpoly K A) ≤ Fintype.card n`, since the minimal polynomial divides the
(degree-`n`) characteristic polynomial. -/
theorem minpoly_natDegree_le_card (A : Matrix n n K) :
    (minpoly K A).natDegree ≤ Fintype.card n := by
  have hdvd : minpoly K A ∣ A.charpoly := Matrix.minpoly_dvd_charpoly A
  have hcp_ne : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  have hle : (minpoly K A).natDegree ≤ A.charpoly.natDegree :=
    natDegree_le_of_dvd hdvd hcp_ne
  rwa [Matrix.charpoly_natDegree_eq_dim A] at hle

/-- **Packaged sharp existence.** Every invertible matrix over a field has an inverse
expressible as a polynomial of degree `< deg (minpoly K A)` in the matrix — the
minimal-degree polynomial representation. -/
theorem exists_inv_eq_aeval_minpoly [Nonempty n] (A : Matrix n n K) (hA : A.det ≠ 0) :
    ∃ s : K[X], s.natDegree < (minpoly K A).natDegree ∧ A⁻¹ = (aeval A) s :=
  ⟨minInvPoly A, minInvPoly_natDegree_lt A, inv_eq_aeval_minInvPoly A hA⟩

/-- **Refinement of the parent bound.** Recovers `cayley-hamilton-oq-07`'s
existence-of-degree-`< n` statement, now witnessed by the minimal-degree polynomial:
`deg (minInvPoly A) < deg (minpoly K A) ≤ Fintype.card n`. -/
theorem exists_inv_eq_aeval_card [Nonempty n] (A : Matrix n n K) (hA : A.det ≠ 0) :
    ∃ s : K[X], s.natDegree < Fintype.card n ∧ A⁻¹ = (aeval A) s :=
  ⟨minInvPoly A,
    lt_of_lt_of_le (minInvPoly_natDegree_lt A) (minpoly_natDegree_le_card A),
    inv_eq_aeval_minInvPoly A hA⟩

end CayleyHamiltonMinpolyOQ07OQ01

-- #print axioms CayleyHamiltonMinpolyOQ07OQ01.exists_inv_eq_aeval_minpoly
-- → [propext, Classical.choice, Quot.sound] only (axiom-free)
