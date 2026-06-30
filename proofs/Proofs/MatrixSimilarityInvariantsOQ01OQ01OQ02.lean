import Mathlib

/-
# Functorial Kernel Isomorphism for Similar Matrices

The companion entry [oq-01-oq-01] (`MatrixSimilarityInvariantsOQ01OQ01`) proves that the
**nullity** — the dimension of the kernel of the associated linear map `A.mulVecLin` — is a
similarity invariant: if `B = P A P⁻¹` then `dim (ker B) = dim (ker A)`.  That is an equality
of *numbers*; it tells us the two kernels have the same size but produces no actual map
between them.

This entry upgrades the equality of dimensions to an **explicit linear isomorphism of the
kernels themselves**, answering the parent's second open question:

> *Does the kernel of `A.mulVecLin` transport functorially under conjugation, giving an
> explicit linear isomorphism of kernels rather than only equality of dimensions?*

The isomorphism is the conceptual one.  Conjugation `B = P A P⁻¹` is a change of basis by
the invertible matrix `P`, and that very change of basis carries kernel to kernel:

* `x ∈ ker B  ⟹  P⁻¹ *ᵥ x ∈ ker A`   (because `A (P⁻¹ x) = P⁻¹ (B x) = 0`), and
* `y ∈ ker A  ⟹  P *ᵥ y ∈ ker B`     (because `B (P y) = P (A y) = 0`).

These two maps are mutually inverse — `P⁻¹ *ᵥ (P *ᵥ y) = y` and `P *ᵥ (P⁻¹ *ᵥ x) = x` — so
they assemble into a `LinearEquiv`

  `kerEquiv : ker B.mulVecLin ≃ₗ[K] ker A.mulVecLin`.

Main results:

* `kerEquiv` — the explicit linear isomorphism of kernels, built from the witness `P`.
* `kerEquiv_apply` / `kerEquiv_symm_apply` — it acts as `P⁻¹ *ᵥ ·` (and its inverse as
  `P *ᵥ ·`), so it is genuinely the change-of-basis map, not an abstract dimension-counting
  artefact.
* `kerEquiv_refl` — the witness `P = 1` for `A ~ A` gives the identity isomorphism
  (the *functor-on-identities* law).
* `kerEquiv_trans` — stacking two conjugations `B = P A P⁻¹`, `C = Q B Q⁻¹` (so
  `C = (QP) A (QP)⁻¹`) composes the kernel isomorphisms (the *functor-on-composition* law).
* `nullity_eq_of_conj` — recovering the parent's equality of dimensions as a one-line
  corollary (`LinearEquiv.finrank_eq`), confirming the iso refines the numeric statement.
* `Similar.nonempty_kerEquiv` — the basis-free existence form for the `Similar` relation.

The functoriality laws `kerEquiv_refl` and `kerEquiv_trans` are exactly what justifies the
word "functorial": the kernel construction is a functor from the groupoid of matrices and
conjugations to `K`-vector spaces and linear isomorphisms.

Mathlib has all the ingredients (`Matrix.mulVecLin`, `Matrix.mulVec_mulVec`,
`LinearEquiv.ofLinear`, `LinearMap.restrict`) but states neither the conjugation-transports-
kernels isomorphism nor its functoriality.  Absent from Mathlib.
-/

namespace MatrixSimilarityInvariantsOQ01OQ01OQ02

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Two square matrices are **similar** if one is a conjugate of the other by an invertible
matrix: `B = P * A * P⁻¹`.  (Same definition as the companion entries.) -/
def Similar (A B : Matrix n n K) : Prop :=
  ∃ P : (Matrix n n K)ˣ, B = P.val * A * P⁻¹.val

/-! ## The conjugation identities

From `B = P A P⁻¹` we extract the two "intertwining" identities that make conjugation move
kernels around: `A` commutes with `P⁻¹` up to `B`, and `B` commutes with `P` up to `A`. -/

variable {A B : Matrix n n K} {P : (Matrix n n K)ˣ}

/-- `A * P⁻¹ = P⁻¹ * B`: the intertwining identity pushing `A` through `P⁻¹`. -/
theorem conj_intertwine_left (hB : B = P.val * A * P⁻¹.val) :
    A * P⁻¹.val = P⁻¹.val * B := by
  rw [hB, ← mul_assoc P⁻¹.val (P.val * A) P⁻¹.val, ← mul_assoc P⁻¹.val P.val A,
    Units.inv_mul, one_mul]

/-- `B * P = P * A`: the intertwining identity pushing `B` through `P`. -/
theorem conj_intertwine_right (hB : B = P.val * A * P⁻¹.val) :
    B * P.val = P.val * A := by
  rw [hB, mul_assoc (P.val * A), Units.inv_mul, mul_one]

/-! ## Kernel transport -/

/-- The change of basis `P⁻¹` carries `ker B` into `ker A`. -/
theorem mapsTo_ker_left (hB : B = P.val * A * P⁻¹.val) (x : n → K)
    (hx : x ∈ LinearMap.ker B.mulVecLin) :
    P⁻¹.val.mulVecLin x ∈ LinearMap.ker A.mulVecLin := by
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  rw [mulVec_mulVec, conj_intertwine_left hB, ← mulVec_mulVec, hx, mulVec_zero]

/-- The change of basis `P` carries `ker A` into `ker B`. -/
theorem mapsTo_ker_right (hB : B = P.val * A * P⁻¹.val) (y : n → K)
    (hy : y ∈ LinearMap.ker A.mulVecLin) :
    P.val.mulVecLin y ∈ LinearMap.ker B.mulVecLin := by
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hy ⊢
  rw [mulVec_mulVec, conj_intertwine_right hB, ← mulVec_mulVec, hy, mulVec_zero]

/-! ## The explicit kernel isomorphism -/

/-- **Functorial kernel isomorphism.** If `B = P A P⁻¹`, the change of basis `P⁻¹` restricts
to an explicit linear isomorphism `ker B.mulVecLin ≃ₗ[K] ker A.mulVecLin`, with inverse the
restriction of `P`. -/
noncomputable def kerEquiv (hB : B = P.val * A * P⁻¹.val) :
    (LinearMap.ker B.mulVecLin) ≃ₗ[K] (LinearMap.ker A.mulVecLin) :=
  LinearEquiv.ofLinear
    (P⁻¹.val.mulVecLin.restrict (mapsTo_ker_left hB))
    (P.val.mulVecLin.restrict (mapsTo_ker_right hB))
    (by
      refine LinearMap.ext fun y => Subtype.ext ?_
      simp only [LinearMap.comp_apply, LinearMap.restrict_coe_apply, LinearMap.id_coe, id_eq,
        mulVecLin_apply]
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec])
    (by
      refine LinearMap.ext fun x => Subtype.ext ?_
      simp only [LinearMap.comp_apply, LinearMap.restrict_coe_apply, LinearMap.id_coe, id_eq,
        mulVecLin_apply]
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec])

@[simp]
theorem kerEquiv_apply (hB : B = P.val * A * P⁻¹.val) (x : LinearMap.ker B.mulVecLin) :
    (kerEquiv hB x : n → K) = P⁻¹.val *ᵥ (x : n → K) := rfl

@[simp]
theorem kerEquiv_symm_apply (hB : B = P.val * A * P⁻¹.val) (y : LinearMap.ker A.mulVecLin) :
    ((kerEquiv hB).symm y : n → K) = P.val *ᵥ (y : n → K) := rfl

/-! ## Functoriality -/

/-- **Functor on identities.** The trivial conjugation `A = 1 * A * 1⁻¹` gives the identity
isomorphism of `ker A` with itself. -/
theorem kerEquiv_refl (A : Matrix n n K) (hA : A = (1 : (Matrix n n K)ˣ).val * A * (1 : (Matrix n n K)ˣ)⁻¹.val) :
    kerEquiv hA = LinearEquiv.refl K (LinearMap.ker A.mulVecLin) := by
  refine LinearEquiv.ext fun x => Subtype.ext ?_
  simp [kerEquiv_apply]

/-- **Functor on composition.** Two stacked conjugations `B = P A P⁻¹` and `C = Q B Q⁻¹`
realise `C = (Q*P) A (Q*P)⁻¹`, and the kernel isomorphisms compose accordingly:
the `A ← C` map is the `A ← B` map after the `B ← C` map. -/
theorem kerEquiv_trans {C : Matrix n n K} {Q : (Matrix n n K)ˣ}
    (hB : B = P.val * A * P⁻¹.val) (hC : C = Q.val * B * Q⁻¹.val)
    (hCA : C = (Q * P).val * A * (Q * P)⁻¹.val) (x : LinearMap.ker C.mulVecLin) :
    (kerEquiv hCA x : n → K) = (kerEquiv hB (kerEquiv hC x) : n → K) := by
  simp only [kerEquiv_apply]
  rw [mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul]

/-! ## Recovering the numeric invariant -/

/-- **The isomorphism refines the parent's equality of dimensions.** Taking finrank of both
sides of `kerEquiv` recovers `nullity B = nullity A` of the companion entry. -/
theorem nullity_eq_of_conj (hB : B = P.val * A * P⁻¹.val) :
    finrank K (LinearMap.ker B.mulVecLin) = finrank K (LinearMap.ker A.mulVecLin) :=
  (kerEquiv hB).finrank_eq

/-! ## Basis-free existence form -/

/-- **Existence form for the `Similar` relation.** Similar matrices have isomorphic kernels.
This is the basis-free packaging: `Similar A B` only asserts *some* conjugator exists, and we
produce an isomorphism from it. -/
theorem Similar.nonempty_kerEquiv (h : Similar A B) :
    Nonempty ((LinearMap.ker B.mulVecLin) ≃ₗ[K] (LinearMap.ker A.mulVecLin)) := by
  obtain ⟨P, hP⟩ := h
  exact ⟨kerEquiv hP⟩

end MatrixSimilarityInvariantsOQ01OQ01OQ02
