/-
  DESIGN DRAFT — NOT YET BUILD-VERIFIED. Lives outside the `proofs/Proofs/` glob on
  purpose: Docker build + Aristotle were both unavailable the session this was written,
  so it must not enter gallery CI until it compiles. Promote to `proofs/Proofs/` only
  after a clean `./proofs/scripts/docker-build.sh`.

  Generic / regular realization of Sₙ and Aₙ as Galois groups
  (abel-ruffini-galois-extensions-oq-10, the Sₙ/Aₙ case of RIGP)

  Idea: the symmetric group Sₙ = Equiv.Perm (Fin n) acts faithfully on the rational
  function field F = ℚ(x₁,…,xₙ) by permuting the variables. Artin's fixed-field theorem
  (Mathlib `FixedPoints.toAlgAutMulEquiv`) then hands us

      Sₙ  ≃*  Gal(F / F^{Sₙ}),        F^{Sₙ} = ℚ(e₁,…,eₙ)  (symmetric functions),

  and likewise for the alternating subgroup Aₙ ≤ Sₙ. Both fixed fields are purely
  transcendental over ℚ, so ℚ is algebraically closed in them and the extensions are
  *regular* — i.e. these are RIGP realizations, not merely IGP.

  The whole abstract engine is already in Mathlib; the ONLY thing to build is the
  concrete permutation action on the fraction field (Mathlib ships symmetric polynomials
  as `∀ e, rename e p = p`, not as fixed points of a `MulSemiringAction`).
-/
import Mathlib

open scoped Classical
open MvPolynomial Equiv

noncomputable section

variable (n : ℕ)

/-- The polynomial ring ℚ[x₁,…,xₙ]. -/
abbrev P : Type := MvPolynomial (Fin n) ℚ

/-- The rational function field ℚ(x₁,…,xₙ). -/
abbrev F : Type := FractionRing (MvPolynomial (Fin n) ℚ)

/-! ### Step 1 — the permutation action on the fraction field

`renameEquiv ℚ e` permutes the variables of `P`; `IsFractionRing.ringEquivOfRingEquiv`
lifts it to `F`. Package the lift as a monoid hom `Perm (Fin n) →* RingAut F`, then turn
that into a `MulSemiringAction` with `MulSemiringAction.compHom`. -/

/-- The ring automorphism of `F` induced by permuting variables by `e`. -/
def permAutF (e : Equiv.Perm (Fin n)) : RingAut (F n) :=
  IsFractionRing.ringEquivOfRingEquiv (K := F n) (L := F n)
    (MvPolynomial.renameEquiv ℚ e).toRingEquiv

/-- `Perm (Fin n) →* RingAut F`. `map_one'`/`map_mul'` follow from `renameEquiv_refl`
    and `renameEquiv_trans` plus functoriality of `ringEquivOfRingEquiv`
    (`IsFractionRing.ringEquivOfRingEquiv_eq`/uniqueness of the fraction-field lift). -/
def permToAutF : Equiv.Perm (Fin n) →* RingAut (F n) where
  toFun := permAutF n
  map_one' := by
    -- renameEquiv ℚ (1 : Perm) = AlgEquiv.refl  (renameEquiv_refl), lift of refl is refl
    sorry
  map_mul' e f := by
    -- renameEquiv ℚ (e * f) = (renameEquiv ℚ e).trans/comp (renameEquiv ℚ f)  (direction
    -- via Equiv.Perm.mul_def + renameEquiv_trans); ringEquivOfRingEquiv is functorial
    -- because the fraction-field extension of a ring hom is unique.
    sorry

/-- The permutation action of `Sₙ` on `F = ℚ(x₁,…,xₙ)`. -/
instance permAction : MulSemiringAction (Equiv.Perm (Fin n)) (F n) :=
  MulSemiringAction.compHom _ (permToAutF n)

/-! ### Step 2 — faithfulness

Distinct permutations act differently already on `P` (`rename e (X i) = X (e i)`), and `P`
embeds in `F` via `algebraMap`, so the action on `F` is faithful. -/

instance permFaithful : FaithfulSMul (Equiv.Perm (Fin n)) (F n) := by
  -- e • algebraMap (X i) = algebraMap (X (e i)); if the action is trivial then X (e i)=X i
  -- for all i, hence e i = i (X injective on Fin n), hence e = 1.
  sorry

/-! ### Step 3 — Artin ⟹ Sₙ is a Galois group

Everything below is a direct application of `Mathlib/FieldTheory/Fixed.lean`. -/

/-- **Sₙ realized.** `Equiv.Perm (Fin n) ≅ Gal(F / F^{Sₙ})`. -/
def realizeSn :
    Equiv.Perm (Fin n) ≃*
      (F n ≃ₐ[FixedPoints.subfield (Equiv.Perm (Fin n)) (F n)] F n) :=
  FixedPoints.toAlgAutMulEquiv _ _

/-- `F / F^{Sₙ}` is Galois (from Mathlib's `Normal` + `IsSeparable` + `FiniteDimensional`
    instances on `FixedPoints.subfield`). -/
example : IsGalois (FixedPoints.subfield (Equiv.Perm (Fin n)) (F n)) (F n) := inferInstance

/-- The degree of the generic Sₙ extension is `n!`. -/
theorem finrank_Sn :
    Module.finrank (FixedPoints.subfield (Equiv.Perm (Fin n)) (F n)) (F n)
      = Nat.factorial n := by
  rw [FixedPoints.finrank_eq_card]
  simp [Fintype.card_perm, Fintype.card_fin]

/-! ### Step 4 — Aₙ realized (same machinery, restricted action)

`alternatingGroup (Fin n) ≤ Perm (Fin n)` inherits the action by
`MulSemiringAction.compHom _ ((permToAutF n).comp (alternatingGroup (Fin n)).subtype)`,
and is faithful as a subgroup of a faithful action. -/

instance altAction : MulSemiringAction (alternatingGroup (Fin n)) (F n) :=
  MulSemiringAction.compHom _
    ((permToAutF n).comp (alternatingGroup (Fin n)).subtype)

instance altFaithful : FaithfulSMul (alternatingGroup (Fin n)) (F n) := by
  sorry

/-- **Aₙ realized.** `alternatingGroup (Fin n) ≅ Gal(F / F^{Aₙ})`.
    `F^{Aₙ} = ℚ(e₁,…,eₙ)(√disc)`. -/
def realizeAn :
    alternatingGroup (Fin n) ≃*
      (F n ≃ₐ[FixedPoints.subfield (alternatingGroup (Fin n)) (F n)] F n) :=
  FixedPoints.toAlgAutMulEquiv _ _

/-- Degree of the generic Aₙ extension is `n!/2` (for `n ≥ 2`). -/
theorem finrank_An :
    Module.finrank (FixedPoints.subfield (alternatingGroup (Fin n)) (F n)) (F n)
      = Fintype.card (alternatingGroup (Fin n)) := by
  rw [FixedPoints.finrank_eq_card]

end
