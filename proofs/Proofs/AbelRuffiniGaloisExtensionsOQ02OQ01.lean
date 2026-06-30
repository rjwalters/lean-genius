/-
  The normal refinement of the Galois correspondence, completed
  (Open Question OQ-02-OQ-01 of abel-ruffini-galois-extensions, a follow-up to
   OQ-02 "Prove the Galois Correspondence Theorem (Subfields ↔ Subgroups)").

  ## What this file establishes (0 sorry, 0 axiom)

  `AbelRuffiniGaloisExtensionsOQ02` packaged the Fundamental Theorem of Galois Theory and,
  in its Part VI, *one half* of the normal refinement: a **normal** subgroup `H` corresponds
  to a **Galois** subextension `fixedField H`, with `Gal(fixedField H / F) ≃* Gal(E/F) ⧸ H`.

  This file completes that refinement into the full **second part of the FTGT**: the Galois
  correspondence restricts to a bijection between the *normal* subgroups of `Gal(E/F)` and the
  intermediate fields that are themselves *Galois* (equivalently *normal*) over the base.

  Mathlib supplies the two implications as type-class instances
  (`IsGalois.fixingSubgroup_normal_of_isGalois`: a Galois subextension has a normal fixing
  subgroup, and `IsGalois.of_fixedField_normal_subgroup`: a normal subgroup has a Galois fixed
  field), but it does **not** state the biconditional, nor the restricted bijection. Assembling
  them is the new content here:

    * `isGalois_iff_fixingSubgroup_normal` — the **biconditional**: an intermediate field `K` is
      Galois over `F` **iff** its fixing subgroup `K.fixingSubgroup` is normal in `Gal(E/F)`.
      The `←` direction is not a Mathlib instance; it goes through the round trip
      `fixedField K.fixingSubgroup = K`.
    * `normal_iff_fixingSubgroup_normal` — the same statement phrased with `Normal F K`
      (separability of `K/F` is automatic, since `E/F` is separable).
    * `normalCorrespondence` — the **restricted bijection**
      `{K // IsGalois F K} ≃ {H : Subgroup (E ≃ₐ[F] E) // H.Normal}`, i.e. the Galois
      correspondence carries Galois subextensions exactly onto normal subgroups. This is FTGT
      part (ii) as a single equivalence, which is not a Mathlib declaration.
    * `card_isGalois_intermediateField_eq_card_normal_subgroup` — the counting corollary: a
      finite Galois extension has exactly as many Galois subextensions as its Galois group has
      normal subgroups.

  ## Concrete instantiation (links to OQ-01 / OQ-02)

  Applied to the Abel–Ruffini witness `q = X⁵ − 4X + 2` (OQ-01), whose splitting field is a
  finite Galois extension of `ℚ` with Galois group `S₅`: the Galois subextensions of the
  splitting field are in bijection with the normal subgroups of `S₅`
  (`quintic_card_isGalois_intermediateField_eq_card_normal_subgroup`).

  ## Provenance

  The two implications are Mathlib's `Mathlib/FieldTheory/Galois/Basic.lean`
  (`IsGalois.fixingSubgroup_normal_of_isGalois`, `IsGalois.of_fixedField_normal_subgroup`). The
  biconditional, the `Normal F K` rephrasing, the restricted bijection, the counting corollary,
  and the quintic instantiation are new.

  ## References
  - Mathlib, `Mathlib/FieldTheory/Galois/Basic.lean`.
  - Stacks project, tag 09DW (Fundamental theorem of Galois theory), part (2).
-/

import Mathlib.FieldTheory.Galois.Basic
import Proofs.AbelRuffiniGaloisExtensionsOQ02

namespace AbelRuffiniGaloisExtensionsOQ02OQ01

open IntermediateField AbelRuffiniGaloisExtensionsOQ02

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-! ## Part I — the biconditional (FTGT part (ii)) -/

/-- **The second part of the Fundamental Theorem of Galois Theory.** An intermediate field `K`
of a finite Galois extension `E / F` is itself Galois over `F` **iff** its fixing subgroup is a
normal subgroup of `Gal(E/F)`. The `→` direction is Mathlib's instance
`IsGalois.fixingSubgroup_normal_of_isGalois`; the `←` direction uses the round trip
`fixedField K.fixingSubgroup = K` to turn the Galois fixed field of a normal subgroup back into
a statement about `K`. -/
theorem isGalois_iff_fixingSubgroup_normal (K : IntermediateField F E) :
    IsGalois F K ↔ K.fixingSubgroup.Normal := by
  constructor
  · intro h
    haveI := h
    infer_instance
  · intro h
    haveI := h
    have hg : IsGalois F (fixedField K.fixingSubgroup) := inferInstance
    rwa [IsGalois.fixedField_fixingSubgroup] at hg

/-- The biconditional phrased with `Normal F K`: an intermediate field is **normal** over the
base iff its fixing subgroup is normal in the Galois group. Separability of `K / F` is
automatic, so `Normal F K` and `IsGalois F K` coincide here. -/
theorem normal_iff_fixingSubgroup_normal (K : IntermediateField F E) :
    Normal F K ↔ K.fixingSubgroup.Normal := by
  haveI : Algebra.IsSeparable F K :=
    Algebra.isSeparable_tower_bot_of_isSeparable F K E
  rw [← isGalois_iff_fixingSubgroup_normal]
  exact ⟨fun h => { to_isSeparable := inferInstance, to_normal := h }, fun h => h.to_normal⟩

/-! ## Part II — the restricted bijection -/

/-- **The normal refinement of the Galois correspondence.** The bijection of OQ-02 restricts to
a bijection between the intermediate fields that are Galois over `F` and the normal subgroups of
`Gal(E/F)`. Concretely, `K ↦ K.fixingSubgroup` is a bijection
`{K // IsGalois F K} ≃ {H // H.Normal}`, by `intermediateFieldEquivSubgroup'` together with the
biconditional `isGalois_iff_fixingSubgroup_normal`. -/
noncomputable def normalCorrespondence :
    {K : IntermediateField F E // IsGalois F K} ≃
      {H : Subgroup (E ≃ₐ[F] E) // H.Normal} :=
  Equiv.subtypeEquiv intermediateFieldEquivSubgroup'
    (fun K => isGalois_iff_fixingSubgroup_normal K)

/-- Counting corollary: a finite Galois extension has exactly as many Galois subextensions as its
Galois group has normal subgroups. -/
theorem card_isGalois_intermediateField_eq_card_normal_subgroup :
    Nat.card {K : IntermediateField F E // IsGalois F K}
      = Nat.card {H : Subgroup (E ≃ₐ[F] E) // H.Normal} :=
  Nat.card_congr normalCorrespondence

/-! ## Part III — concrete instantiation: the Abel–Ruffini quintic `X⁵ − 4X + 2` -/

section Quintic

open AbelRuffiniGaloisExtensionsOQ01

/-- **The normal Galois correspondence for the Abel–Ruffini witness.** The Galois subextensions
of the splitting field of `X⁵ − 4X + 2` are in bijection with the normal subgroups of its Galois
group — which is `S₅` by `AbelRuffiniGaloisExtensionsOQ01.galEquivS5`. -/
theorem quintic_card_isGalois_intermediateField_eq_card_normal_subgroup :
    Nat.card {K : IntermediateField ℚ q.SplittingField // IsGalois ℚ K}
      = Nat.card {H : Subgroup (q.SplittingField ≃ₐ[ℚ] q.SplittingField) // H.Normal} :=
  card_isGalois_intermediateField_eq_card_normal_subgroup

end Quintic

end AbelRuffiniGaloisExtensionsOQ02OQ01
